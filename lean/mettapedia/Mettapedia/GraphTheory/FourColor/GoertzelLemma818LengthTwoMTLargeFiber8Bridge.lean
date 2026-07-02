import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for `mirror,normal` size-64 fiber 8

This module proves direct connectedness for one generated size-64 fiber from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMTBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorTauCertificate
open GoertzelLemma818MirrorTauReverseAudit

def mtFiber8StateAt (i : Nat) : List TauState :=
  directStates (mtFiber8RowAt i).sourceLeft (mtFiber8RowAt i).sourceRight

def mtFiber8DirectStates : List (List TauState) :=
  [mtFiber8StateAt 0, mtFiber8StateAt 1, mtFiber8StateAt 2, mtFiber8StateAt 3, mtFiber8StateAt 4, mtFiber8StateAt 5, mtFiber8StateAt 6, mtFiber8StateAt 7, mtFiber8StateAt 8, mtFiber8StateAt 9, mtFiber8StateAt 10, mtFiber8StateAt 11, mtFiber8StateAt 12, mtFiber8StateAt 13, mtFiber8StateAt 14, mtFiber8StateAt 15, mtFiber8StateAt 16, mtFiber8StateAt 17, mtFiber8StateAt 18, mtFiber8StateAt 19, mtFiber8StateAt 20, mtFiber8StateAt 21, mtFiber8StateAt 22, mtFiber8StateAt 23, mtFiber8StateAt 24, mtFiber8StateAt 25, mtFiber8StateAt 26, mtFiber8StateAt 27, mtFiber8StateAt 28, mtFiber8StateAt 29, mtFiber8StateAt 30, mtFiber8StateAt 31, mtFiber8StateAt 32, mtFiber8StateAt 33, mtFiber8StateAt 34, mtFiber8StateAt 35, mtFiber8StateAt 36, mtFiber8StateAt 37, mtFiber8StateAt 38, mtFiber8StateAt 39, mtFiber8StateAt 40, mtFiber8StateAt 41, mtFiber8StateAt 42, mtFiber8StateAt 43, mtFiber8StateAt 44, mtFiber8StateAt 45, mtFiber8StateAt 46, mtFiber8StateAt 47, mtFiber8StateAt 48, mtFiber8StateAt 49, mtFiber8StateAt 50, mtFiber8StateAt 51, mtFiber8StateAt 52, mtFiber8StateAt 53, mtFiber8StateAt 54, mtFiber8StateAt 55, mtFiber8StateAt 56, mtFiber8StateAt 57, mtFiber8StateAt 58, mtFiber8StateAt 59, mtFiber8StateAt 60, mtFiber8StateAt 61, mtFiber8StateAt 62, mtFiber8StateAt 63]

theorem mtFiber8ReverseRow_1_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk0_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 0) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 0) (mtFiber8StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 0) (mtFiber8StateAt 1)
    (mtFiber8RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 1) (by decide) mtFiber8ReverseRow_1_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_2_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk1_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 2) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber8ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 1) (mtFiber8StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 1) (mtFiber8StateAt 2)
    (mtFiber8RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 2) (by decide) mtFiber8ReverseRow_2_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_3_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk1_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 2) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 0) (mtFiber8StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 0) (mtFiber8StateAt 3)
    (mtFiber8RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 3) (by decide) mtFiber8ReverseRow_3_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_4_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk2_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 4) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber8ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 0) (mtFiber8StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 0) (mtFiber8StateAt 4)
    (mtFiber8RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 4) (by decide) mtFiber8ReverseRow_4_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_5_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk2_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 4) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 1) (mtFiber8StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 1) (mtFiber8StateAt 5)
    (mtFiber8RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 5) (by decide) mtFiber8ReverseRow_5_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_6_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk3_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 6) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber8ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 4) (mtFiber8StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 4) (mtFiber8StateAt 6)
    (mtFiber8RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 6) (by decide) mtFiber8ReverseRow_6_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_7_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk3_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 6) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 3) (mtFiber8StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 3) (mtFiber8StateAt 7)
    (mtFiber8RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 7) (by decide) mtFiber8ReverseRow_7_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_8_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk4_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 8) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber8ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 0) (mtFiber8StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 0) (mtFiber8StateAt 8)
    (mtFiber8RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 8) (by decide) mtFiber8ReverseRow_8_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_9_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk4_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 8) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 1) (mtFiber8StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 1) (mtFiber8StateAt 9)
    (mtFiber8RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 9) (by decide) mtFiber8ReverseRow_9_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_10_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk5_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 10) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber8ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 2) (mtFiber8StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 2) (mtFiber8StateAt 10)
    (mtFiber8RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 10) (by decide) mtFiber8ReverseRow_10_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_11_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk5_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 10) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 3) (mtFiber8StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 3) (mtFiber8StateAt 11)
    (mtFiber8RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 11) (by decide) mtFiber8ReverseRow_11_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_12_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk6_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 12) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber8ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 4) (mtFiber8StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 4) (mtFiber8StateAt 12)
    (mtFiber8RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 12) (by decide) mtFiber8ReverseRow_12_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_13_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk6_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 12) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 5) (mtFiber8StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 5) (mtFiber8StateAt 13)
    (mtFiber8RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 13) (by decide) mtFiber8ReverseRow_13_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_14_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk7_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 14) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber8ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 6) (mtFiber8StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 6) (mtFiber8StateAt 14)
    (mtFiber8RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 14) (by decide) mtFiber8ReverseRow_14_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_15_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk7_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 14) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 7) (mtFiber8StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 7) (mtFiber8StateAt 15)
    (mtFiber8RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 15) (by decide) mtFiber8ReverseRow_15_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_16_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 16) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk8_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 16) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber8ReverseSingleStep16 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 0) (mtFiber8StateAt 16) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 0) (mtFiber8StateAt 16)
    (mtFiber8RowAt 16).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 16) (by decide) mtFiber8ReverseRow_16_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_17_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 17) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk8_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 16) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep17 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 1) (mtFiber8StateAt 17) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 1) (mtFiber8StateAt 17)
    (mtFiber8RowAt 17).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 17) (by decide) mtFiber8ReverseRow_17_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_18_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 18) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk9_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 18) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber8ReverseSingleStep18 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 2) (mtFiber8StateAt 18) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 2) (mtFiber8StateAt 18)
    (mtFiber8RowAt 18).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 18) (by decide) mtFiber8ReverseRow_18_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_19_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 19) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk9_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 18) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep19 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 3) (mtFiber8StateAt 19) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 3) (mtFiber8StateAt 19)
    (mtFiber8RowAt 19).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 19) (by decide) mtFiber8ReverseRow_19_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_20_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 20) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk10_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 20) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber8ReverseSingleStep20 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 4) (mtFiber8StateAt 20) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 4) (mtFiber8StateAt 20)
    (mtFiber8RowAt 20).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 20) (by decide) mtFiber8ReverseRow_20_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_21_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 21) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk10_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 20) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep21 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 5) (mtFiber8StateAt 21) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 5) (mtFiber8StateAt 21)
    (mtFiber8RowAt 21).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 21) (by decide) mtFiber8ReverseRow_21_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_22_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 22) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk11_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 22) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber8ReverseSingleStep22 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 6) (mtFiber8StateAt 22) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 6) (mtFiber8StateAt 22)
    (mtFiber8RowAt 22).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 22) (by decide) mtFiber8ReverseRow_22_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_23_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 23) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk11_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 22) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep23 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 7) (mtFiber8StateAt 23) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 7) (mtFiber8StateAt 23)
    (mtFiber8RowAt 23).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 23) (by decide) mtFiber8ReverseRow_23_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_24_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 24) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk12_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 24) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber8ReverseSingleStep24 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 8) (mtFiber8StateAt 24) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 8) (mtFiber8StateAt 24)
    (mtFiber8RowAt 24).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 24) (by decide) mtFiber8ReverseRow_24_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_25_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 25) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk12_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 24) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep25 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 9) (mtFiber8StateAt 25) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 9) (mtFiber8StateAt 25)
    (mtFiber8RowAt 25).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 25) (by decide) mtFiber8ReverseRow_25_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_26_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 26) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk13_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 26) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber8ReverseSingleStep26 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 10) (mtFiber8StateAt 26) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 10) (mtFiber8StateAt 26)
    (mtFiber8RowAt 26).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 26) (by decide) mtFiber8ReverseRow_26_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_27_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 27) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk13_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 26) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep27 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 11) (mtFiber8StateAt 27) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 11) (mtFiber8StateAt 27)
    (mtFiber8RowAt 27).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 27) (by decide) mtFiber8ReverseRow_27_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_28_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 28) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk14_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 28) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber8ReverseSingleStep28 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 12) (mtFiber8StateAt 28) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 12) (mtFiber8StateAt 28)
    (mtFiber8RowAt 28).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 28) (by decide) mtFiber8ReverseRow_28_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_29_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 29) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk14_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 28) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep29 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 13) (mtFiber8StateAt 29) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 13) (mtFiber8StateAt 29)
    (mtFiber8RowAt 29).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 29) (by decide) mtFiber8ReverseRow_29_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_30_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 30) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk15_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 30) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber8ReverseSingleStep30 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 14) (mtFiber8StateAt 30) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 14) (mtFiber8StateAt 30)
    (mtFiber8RowAt 30).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 30) (by decide) mtFiber8ReverseRow_30_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_31_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 31) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk15_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 30) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep31 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 15) (mtFiber8StateAt 31) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 15) (mtFiber8StateAt 31)
    (mtFiber8RowAt 31).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 31) (by decide) mtFiber8ReverseRow_31_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_32_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 32) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk16_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 32) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber8ReverseSingleStep32 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 0) (mtFiber8StateAt 32) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 0) (mtFiber8StateAt 32)
    (mtFiber8RowAt 32).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 32) (by decide) mtFiber8ReverseRow_32_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_33_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 33) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk16_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 32) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep33 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 1) (mtFiber8StateAt 33) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 1) (mtFiber8StateAt 33)
    (mtFiber8RowAt 33).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 33) (by decide) mtFiber8ReverseRow_33_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_34_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 34) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk17_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 34) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber8ReverseSingleStep34 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 32) (mtFiber8StateAt 34) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 32) (mtFiber8StateAt 34)
    (mtFiber8RowAt 34).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 34) (by decide) mtFiber8ReverseRow_34_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_35_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 35) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk17_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 34) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep35 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 3) (mtFiber8StateAt 35) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 3) (mtFiber8StateAt 35)
    (mtFiber8RowAt 35).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 35) (by decide) mtFiber8ReverseRow_35_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_36_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 36) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk18_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 36) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber8ReverseSingleStep36 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 4) (mtFiber8StateAt 36) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 4) (mtFiber8StateAt 36)
    (mtFiber8RowAt 36).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 36) (by decide) mtFiber8ReverseRow_36_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_37_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 37) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk18_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 36) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep37 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 5) (mtFiber8StateAt 37) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 5) (mtFiber8StateAt 37)
    (mtFiber8RowAt 37).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 37) (by decide) mtFiber8ReverseRow_37_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_38_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 38) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk19_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 38) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber8ReverseSingleStep38 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 33) (mtFiber8StateAt 38) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 33) (mtFiber8StateAt 38)
    (mtFiber8RowAt 38).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 38) (by decide) mtFiber8ReverseRow_38_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_39_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 39) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk19_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 38) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep39 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 32) (mtFiber8StateAt 39) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 32) (mtFiber8StateAt 39)
    (mtFiber8RowAt 39).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 39) (by decide) mtFiber8ReverseRow_39_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_40_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 40) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk20_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 40) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber8ReverseSingleStep40 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 8) (mtFiber8StateAt 40) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 8) (mtFiber8StateAt 40)
    (mtFiber8RowAt 40).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 40) (by decide) mtFiber8ReverseRow_40_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_41_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 41) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk20_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 40) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep41 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 9) (mtFiber8StateAt 41) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 9) (mtFiber8StateAt 41)
    (mtFiber8RowAt 41).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 41) (by decide) mtFiber8ReverseRow_41_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_42_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 42) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk21_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 42) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber8ReverseSingleStep42 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 40) (mtFiber8StateAt 42) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 40) (mtFiber8StateAt 42)
    (mtFiber8RowAt 42).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 42) (by decide) mtFiber8ReverseRow_42_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_43_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 43) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk21_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 42) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep43 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 11) (mtFiber8StateAt 43) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 11) (mtFiber8StateAt 43)
    (mtFiber8RowAt 43).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 43) (by decide) mtFiber8ReverseRow_43_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_44_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 44) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk22_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 44) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber8ReverseSingleStep44 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 12) (mtFiber8StateAt 44) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 12) (mtFiber8StateAt 44)
    (mtFiber8RowAt 44).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 44) (by decide) mtFiber8ReverseRow_44_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_45_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 45) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk22_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 44) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep45 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 13) (mtFiber8StateAt 45) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 13) (mtFiber8StateAt 45)
    (mtFiber8RowAt 45).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 45) (by decide) mtFiber8ReverseRow_45_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_46_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 46) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk23_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 46) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber8ReverseSingleStep46 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 41) (mtFiber8StateAt 46) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 41) (mtFiber8StateAt 46)
    (mtFiber8RowAt 46).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 46) (by decide) mtFiber8ReverseRow_46_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_47_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 47) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk23_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 46) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep47 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 40) (mtFiber8StateAt 47) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 40) (mtFiber8StateAt 47)
    (mtFiber8RowAt 47).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 47) (by decide) mtFiber8ReverseRow_47_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_48_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 48) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk24_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 48) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber8ReverseSingleStep48 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 16) (mtFiber8StateAt 48) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 16) (mtFiber8StateAt 48)
    (mtFiber8RowAt 48).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 48) (by decide) mtFiber8ReverseRow_48_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_49_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 49) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk24_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 48) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep49 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 17) (mtFiber8StateAt 49) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 17) (mtFiber8StateAt 49)
    (mtFiber8RowAt 49).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 49) (by decide) mtFiber8ReverseRow_49_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_50_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 50) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk25_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 50) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber8ReverseSingleStep50 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 48) (mtFiber8StateAt 50) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 48) (mtFiber8StateAt 50)
    (mtFiber8RowAt 50).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 50) (by decide) mtFiber8ReverseRow_50_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_51_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 51) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk25_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 50) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep51 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 19) (mtFiber8StateAt 51) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 19) (mtFiber8StateAt 51)
    (mtFiber8RowAt 51).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 51) (by decide) mtFiber8ReverseRow_51_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_52_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 52) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk26_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 52) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber8ReverseSingleStep52 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 20) (mtFiber8StateAt 52) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 20) (mtFiber8StateAt 52)
    (mtFiber8RowAt 52).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 52) (by decide) mtFiber8ReverseRow_52_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_53_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 53) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk26_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 52) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep53 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 21) (mtFiber8StateAt 53) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 21) (mtFiber8StateAt 53)
    (mtFiber8RowAt 53).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 53) (by decide) mtFiber8ReverseRow_53_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_54_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 54) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk27_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 54) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber8ReverseSingleStep54 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 49) (mtFiber8StateAt 54) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 49) (mtFiber8StateAt 54)
    (mtFiber8RowAt 54).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 54) (by decide) mtFiber8ReverseRow_54_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_55_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 55) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk27_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 54) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep55 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 48) (mtFiber8StateAt 55) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 48) (mtFiber8StateAt 55)
    (mtFiber8RowAt 55).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 55) (by decide) mtFiber8ReverseRow_55_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_56_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 56) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk28_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 56) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber8ReverseSingleStep56 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 32) (mtFiber8StateAt 56) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 32) (mtFiber8StateAt 56)
    (mtFiber8RowAt 56).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 56) (by decide) mtFiber8ReverseRow_56_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_57_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 57) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk28_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 56) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep57 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 33) (mtFiber8StateAt 57) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 33) (mtFiber8StateAt 57)
    (mtFiber8RowAt 57).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 57) (by decide) mtFiber8ReverseRow_57_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_58_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 58) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk29_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 58) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber8ReverseSingleStep58 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 34) (mtFiber8StateAt 58) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 34) (mtFiber8StateAt 58)
    (mtFiber8RowAt 58).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 58) (by decide) mtFiber8ReverseRow_58_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_59_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 59) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk29_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 58) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep59 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 35) (mtFiber8StateAt 59) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 35) (mtFiber8StateAt 59)
    (mtFiber8RowAt 59).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 59) (by decide) mtFiber8ReverseRow_59_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_60_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 60) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk30_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 60) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber8ReverseSingleStep60 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 36) (mtFiber8StateAt 60) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 36) (mtFiber8StateAt 60)
    (mtFiber8RowAt 60).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 60) (by decide) mtFiber8ReverseRow_60_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_61_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 61) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk30_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 60) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep61 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 37) (mtFiber8StateAt 61) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 37) (mtFiber8StateAt 61)
    (mtFiber8RowAt 61).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 61) (by decide) mtFiber8ReverseRow_61_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_62_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 62) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk31_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 62) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber8ReverseSingleStep62 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 38) (mtFiber8StateAt 62) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 38) (mtFiber8StateAt 62)
    (mtFiber8RowAt 62).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 62) (by decide) mtFiber8ReverseRow_62_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8ReverseRow_63_ok :
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 63) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber8Chunk31_ok
  change (mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 62) &&
    mtRowReverseValid mtFiber8Key mtFiber8Expected (mtFiber8RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber8ReverseSingleStep63 :
    chainSingleKempeStep mtWord (mtFiber8StateAt 39) (mtFiber8StateAt 63) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber8StateAt 39) (mtFiber8StateAt 63)
    (mtFiber8RowAt 63).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber8Key mtFiber8Expected
        (mtFiber8RowAt 63) (by decide) mtFiber8ReverseRow_63_ok
      simpa [mtFiber8StateAt, mtFiber8RowAt, mtFiber8Rows, listGetD, directRow] using h)

theorem mtFiber8State0_in_close :
    mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  change mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 64 [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 0 64 [mtFiber8StateAt 0] (mtFiber8StateAt 0) (by simp [closeChainFiber])

theorem mtFiber8State1_in_close :
    mtFiber8StateAt 1 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 1 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 1) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep1
  change mtFiber8StateAt 1 ∈ closeChainFiber mtWord mtFiber8DirectStates (1 + 63) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 1 63 [mtFiber8StateAt 0] (mtFiber8StateAt 1) h1

theorem mtFiber8State2_in_close :
    mtFiber8StateAt 2 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 1 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 1) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep1
  have h2 : mtFiber8StateAt 2 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 1) (mtFiber8StateAt 2) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep2
  change mtFiber8StateAt 2 ∈ closeChainFiber mtWord mtFiber8DirectStates (2 + 62) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 2 62 [mtFiber8StateAt 0] (mtFiber8StateAt 2) h2

theorem mtFiber8State3_in_close :
    mtFiber8StateAt 3 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 3 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 3) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep3
  change mtFiber8StateAt 3 ∈ closeChainFiber mtWord mtFiber8DirectStates (1 + 63) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 1 63 [mtFiber8StateAt 0] (mtFiber8StateAt 3) h1

theorem mtFiber8State4_in_close :
    mtFiber8StateAt 4 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 4 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 4) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep4
  change mtFiber8StateAt 4 ∈ closeChainFiber mtWord mtFiber8DirectStates (1 + 63) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 1 63 [mtFiber8StateAt 0] (mtFiber8StateAt 4) h1

theorem mtFiber8State5_in_close :
    mtFiber8StateAt 5 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 1 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 1) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep1
  have h2 : mtFiber8StateAt 5 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 1) (mtFiber8StateAt 5) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep5
  change mtFiber8StateAt 5 ∈ closeChainFiber mtWord mtFiber8DirectStates (2 + 62) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 2 62 [mtFiber8StateAt 0] (mtFiber8StateAt 5) h2

theorem mtFiber8State6_in_close :
    mtFiber8StateAt 6 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 4 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 4) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep4
  have h2 : mtFiber8StateAt 6 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 4) (mtFiber8StateAt 6) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep6
  change mtFiber8StateAt 6 ∈ closeChainFiber mtWord mtFiber8DirectStates (2 + 62) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 2 62 [mtFiber8StateAt 0] (mtFiber8StateAt 6) h2

theorem mtFiber8State7_in_close :
    mtFiber8StateAt 7 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 3 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 3) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep3
  have h2 : mtFiber8StateAt 7 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 3) (mtFiber8StateAt 7) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep7
  change mtFiber8StateAt 7 ∈ closeChainFiber mtWord mtFiber8DirectStates (2 + 62) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 2 62 [mtFiber8StateAt 0] (mtFiber8StateAt 7) h2

theorem mtFiber8State8_in_close :
    mtFiber8StateAt 8 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 8 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 8) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep8
  change mtFiber8StateAt 8 ∈ closeChainFiber mtWord mtFiber8DirectStates (1 + 63) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 1 63 [mtFiber8StateAt 0] (mtFiber8StateAt 8) h1

theorem mtFiber8State9_in_close :
    mtFiber8StateAt 9 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 1 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 1) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep1
  have h2 : mtFiber8StateAt 9 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 1) (mtFiber8StateAt 9) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep9
  change mtFiber8StateAt 9 ∈ closeChainFiber mtWord mtFiber8DirectStates (2 + 62) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 2 62 [mtFiber8StateAt 0] (mtFiber8StateAt 9) h2

theorem mtFiber8State10_in_close :
    mtFiber8StateAt 10 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 1 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 1) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep1
  have h2 : mtFiber8StateAt 2 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 1) (mtFiber8StateAt 2) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep2
  have h3 : mtFiber8StateAt 10 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 2) (mtFiber8StateAt 10) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep10
  change mtFiber8StateAt 10 ∈ closeChainFiber mtWord mtFiber8DirectStates (3 + 61) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 3 61 [mtFiber8StateAt 0] (mtFiber8StateAt 10) h3

theorem mtFiber8State11_in_close :
    mtFiber8StateAt 11 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 3 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 3) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep3
  have h2 : mtFiber8StateAt 11 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 3) (mtFiber8StateAt 11) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep11
  change mtFiber8StateAt 11 ∈ closeChainFiber mtWord mtFiber8DirectStates (2 + 62) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 2 62 [mtFiber8StateAt 0] (mtFiber8StateAt 11) h2

theorem mtFiber8State12_in_close :
    mtFiber8StateAt 12 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 4 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 4) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep4
  have h2 : mtFiber8StateAt 12 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 4) (mtFiber8StateAt 12) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep12
  change mtFiber8StateAt 12 ∈ closeChainFiber mtWord mtFiber8DirectStates (2 + 62) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 2 62 [mtFiber8StateAt 0] (mtFiber8StateAt 12) h2

theorem mtFiber8State13_in_close :
    mtFiber8StateAt 13 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 1 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 1) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep1
  have h2 : mtFiber8StateAt 5 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 1) (mtFiber8StateAt 5) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep5
  have h3 : mtFiber8StateAt 13 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 5) (mtFiber8StateAt 13) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep13
  change mtFiber8StateAt 13 ∈ closeChainFiber mtWord mtFiber8DirectStates (3 + 61) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 3 61 [mtFiber8StateAt 0] (mtFiber8StateAt 13) h3

theorem mtFiber8State14_in_close :
    mtFiber8StateAt 14 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 4 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 4) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep4
  have h2 : mtFiber8StateAt 6 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 4) (mtFiber8StateAt 6) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep6
  have h3 : mtFiber8StateAt 14 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 6) (mtFiber8StateAt 14) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep14
  change mtFiber8StateAt 14 ∈ closeChainFiber mtWord mtFiber8DirectStates (3 + 61) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 3 61 [mtFiber8StateAt 0] (mtFiber8StateAt 14) h3

theorem mtFiber8State15_in_close :
    mtFiber8StateAt 15 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 3 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 3) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep3
  have h2 : mtFiber8StateAt 7 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 3) (mtFiber8StateAt 7) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep7
  have h3 : mtFiber8StateAt 15 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 7) (mtFiber8StateAt 15) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep15
  change mtFiber8StateAt 15 ∈ closeChainFiber mtWord mtFiber8DirectStates (3 + 61) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 3 61 [mtFiber8StateAt 0] (mtFiber8StateAt 15) h3

theorem mtFiber8State16_in_close :
    mtFiber8StateAt 16 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 16 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 16) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep16
  change mtFiber8StateAt 16 ∈ closeChainFiber mtWord mtFiber8DirectStates (1 + 63) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 1 63 [mtFiber8StateAt 0] (mtFiber8StateAt 16) h1

theorem mtFiber8State17_in_close :
    mtFiber8StateAt 17 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 1 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 1) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep1
  have h2 : mtFiber8StateAt 17 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 1) (mtFiber8StateAt 17) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep17
  change mtFiber8StateAt 17 ∈ closeChainFiber mtWord mtFiber8DirectStates (2 + 62) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 2 62 [mtFiber8StateAt 0] (mtFiber8StateAt 17) h2

theorem mtFiber8State18_in_close :
    mtFiber8StateAt 18 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 1 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 1) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep1
  have h2 : mtFiber8StateAt 2 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 1) (mtFiber8StateAt 2) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep2
  have h3 : mtFiber8StateAt 18 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 2) (mtFiber8StateAt 18) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep18
  change mtFiber8StateAt 18 ∈ closeChainFiber mtWord mtFiber8DirectStates (3 + 61) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 3 61 [mtFiber8StateAt 0] (mtFiber8StateAt 18) h3

theorem mtFiber8State19_in_close :
    mtFiber8StateAt 19 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 3 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 3) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep3
  have h2 : mtFiber8StateAt 19 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 3) (mtFiber8StateAt 19) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep19
  change mtFiber8StateAt 19 ∈ closeChainFiber mtWord mtFiber8DirectStates (2 + 62) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 2 62 [mtFiber8StateAt 0] (mtFiber8StateAt 19) h2

theorem mtFiber8State20_in_close :
    mtFiber8StateAt 20 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 4 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 4) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep4
  have h2 : mtFiber8StateAt 20 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 4) (mtFiber8StateAt 20) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep20
  change mtFiber8StateAt 20 ∈ closeChainFiber mtWord mtFiber8DirectStates (2 + 62) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 2 62 [mtFiber8StateAt 0] (mtFiber8StateAt 20) h2

theorem mtFiber8State21_in_close :
    mtFiber8StateAt 21 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 1 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 1) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep1
  have h2 : mtFiber8StateAt 5 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 1) (mtFiber8StateAt 5) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep5
  have h3 : mtFiber8StateAt 21 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 5) (mtFiber8StateAt 21) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep21
  change mtFiber8StateAt 21 ∈ closeChainFiber mtWord mtFiber8DirectStates (3 + 61) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 3 61 [mtFiber8StateAt 0] (mtFiber8StateAt 21) h3

theorem mtFiber8State22_in_close :
    mtFiber8StateAt 22 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 4 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 4) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep4
  have h2 : mtFiber8StateAt 6 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 4) (mtFiber8StateAt 6) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep6
  have h3 : mtFiber8StateAt 22 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 6) (mtFiber8StateAt 22) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep22
  change mtFiber8StateAt 22 ∈ closeChainFiber mtWord mtFiber8DirectStates (3 + 61) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 3 61 [mtFiber8StateAt 0] (mtFiber8StateAt 22) h3

theorem mtFiber8State23_in_close :
    mtFiber8StateAt 23 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 3 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 3) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep3
  have h2 : mtFiber8StateAt 7 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 3) (mtFiber8StateAt 7) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep7
  have h3 : mtFiber8StateAt 23 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 7) (mtFiber8StateAt 23) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep23
  change mtFiber8StateAt 23 ∈ closeChainFiber mtWord mtFiber8DirectStates (3 + 61) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 3 61 [mtFiber8StateAt 0] (mtFiber8StateAt 23) h3

theorem mtFiber8State24_in_close :
    mtFiber8StateAt 24 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 8 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 8) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep8
  have h2 : mtFiber8StateAt 24 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 8) (mtFiber8StateAt 24) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep24
  change mtFiber8StateAt 24 ∈ closeChainFiber mtWord mtFiber8DirectStates (2 + 62) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 2 62 [mtFiber8StateAt 0] (mtFiber8StateAt 24) h2

theorem mtFiber8State25_in_close :
    mtFiber8StateAt 25 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 1 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 1) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep1
  have h2 : mtFiber8StateAt 9 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 1) (mtFiber8StateAt 9) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep9
  have h3 : mtFiber8StateAt 25 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 9) (mtFiber8StateAt 25) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep25
  change mtFiber8StateAt 25 ∈ closeChainFiber mtWord mtFiber8DirectStates (3 + 61) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 3 61 [mtFiber8StateAt 0] (mtFiber8StateAt 25) h3

theorem mtFiber8State26_in_close :
    mtFiber8StateAt 26 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 1 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 1) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep1
  have h2 : mtFiber8StateAt 2 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 1) (mtFiber8StateAt 2) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep2
  have h3 : mtFiber8StateAt 10 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 2) (mtFiber8StateAt 10) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep10
  have h4 : mtFiber8StateAt 26 ∈ closeChainFiber mtWord mtFiber8DirectStates 4 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0]
      (mtFiber8StateAt 10) (mtFiber8StateAt 26) (by decide) h3 (by decide)
      mtFiber8ReverseSingleStep26
  change mtFiber8StateAt 26 ∈ closeChainFiber mtWord mtFiber8DirectStates (4 + 60) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 4 60 [mtFiber8StateAt 0] (mtFiber8StateAt 26) h4

theorem mtFiber8State27_in_close :
    mtFiber8StateAt 27 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 3 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 3) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep3
  have h2 : mtFiber8StateAt 11 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 3) (mtFiber8StateAt 11) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep11
  have h3 : mtFiber8StateAt 27 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 11) (mtFiber8StateAt 27) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep27
  change mtFiber8StateAt 27 ∈ closeChainFiber mtWord mtFiber8DirectStates (3 + 61) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 3 61 [mtFiber8StateAt 0] (mtFiber8StateAt 27) h3

theorem mtFiber8State28_in_close :
    mtFiber8StateAt 28 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 4 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 4) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep4
  have h2 : mtFiber8StateAt 12 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 4) (mtFiber8StateAt 12) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep12
  have h3 : mtFiber8StateAt 28 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 12) (mtFiber8StateAt 28) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep28
  change mtFiber8StateAt 28 ∈ closeChainFiber mtWord mtFiber8DirectStates (3 + 61) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 3 61 [mtFiber8StateAt 0] (mtFiber8StateAt 28) h3

theorem mtFiber8State29_in_close :
    mtFiber8StateAt 29 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 1 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 1) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep1
  have h2 : mtFiber8StateAt 5 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 1) (mtFiber8StateAt 5) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep5
  have h3 : mtFiber8StateAt 13 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 5) (mtFiber8StateAt 13) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep13
  have h4 : mtFiber8StateAt 29 ∈ closeChainFiber mtWord mtFiber8DirectStates 4 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0]
      (mtFiber8StateAt 13) (mtFiber8StateAt 29) (by decide) h3 (by decide)
      mtFiber8ReverseSingleStep29
  change mtFiber8StateAt 29 ∈ closeChainFiber mtWord mtFiber8DirectStates (4 + 60) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 4 60 [mtFiber8StateAt 0] (mtFiber8StateAt 29) h4

theorem mtFiber8State30_in_close :
    mtFiber8StateAt 30 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 4 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 4) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep4
  have h2 : mtFiber8StateAt 6 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 4) (mtFiber8StateAt 6) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep6
  have h3 : mtFiber8StateAt 14 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 6) (mtFiber8StateAt 14) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep14
  have h4 : mtFiber8StateAt 30 ∈ closeChainFiber mtWord mtFiber8DirectStates 4 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0]
      (mtFiber8StateAt 14) (mtFiber8StateAt 30) (by decide) h3 (by decide)
      mtFiber8ReverseSingleStep30
  change mtFiber8StateAt 30 ∈ closeChainFiber mtWord mtFiber8DirectStates (4 + 60) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 4 60 [mtFiber8StateAt 0] (mtFiber8StateAt 30) h4

theorem mtFiber8State31_in_close :
    mtFiber8StateAt 31 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 3 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 3) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep3
  have h2 : mtFiber8StateAt 7 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 3) (mtFiber8StateAt 7) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep7
  have h3 : mtFiber8StateAt 15 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 7) (mtFiber8StateAt 15) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep15
  have h4 : mtFiber8StateAt 31 ∈ closeChainFiber mtWord mtFiber8DirectStates 4 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0]
      (mtFiber8StateAt 15) (mtFiber8StateAt 31) (by decide) h3 (by decide)
      mtFiber8ReverseSingleStep31
  change mtFiber8StateAt 31 ∈ closeChainFiber mtWord mtFiber8DirectStates (4 + 60) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 4 60 [mtFiber8StateAt 0] (mtFiber8StateAt 31) h4

theorem mtFiber8State32_in_close :
    mtFiber8StateAt 32 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 32 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 32) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep32
  change mtFiber8StateAt 32 ∈ closeChainFiber mtWord mtFiber8DirectStates (1 + 63) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 1 63 [mtFiber8StateAt 0] (mtFiber8StateAt 32) h1

theorem mtFiber8State33_in_close :
    mtFiber8StateAt 33 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 1 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 1) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep1
  have h2 : mtFiber8StateAt 33 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 1) (mtFiber8StateAt 33) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep33
  change mtFiber8StateAt 33 ∈ closeChainFiber mtWord mtFiber8DirectStates (2 + 62) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 2 62 [mtFiber8StateAt 0] (mtFiber8StateAt 33) h2

theorem mtFiber8State34_in_close :
    mtFiber8StateAt 34 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 32 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 32) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep32
  have h2 : mtFiber8StateAt 34 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 32) (mtFiber8StateAt 34) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep34
  change mtFiber8StateAt 34 ∈ closeChainFiber mtWord mtFiber8DirectStates (2 + 62) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 2 62 [mtFiber8StateAt 0] (mtFiber8StateAt 34) h2

theorem mtFiber8State35_in_close :
    mtFiber8StateAt 35 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 3 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 3) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep3
  have h2 : mtFiber8StateAt 35 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 3) (mtFiber8StateAt 35) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep35
  change mtFiber8StateAt 35 ∈ closeChainFiber mtWord mtFiber8DirectStates (2 + 62) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 2 62 [mtFiber8StateAt 0] (mtFiber8StateAt 35) h2

theorem mtFiber8State36_in_close :
    mtFiber8StateAt 36 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 4 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 4) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep4
  have h2 : mtFiber8StateAt 36 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 4) (mtFiber8StateAt 36) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep36
  change mtFiber8StateAt 36 ∈ closeChainFiber mtWord mtFiber8DirectStates (2 + 62) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 2 62 [mtFiber8StateAt 0] (mtFiber8StateAt 36) h2

theorem mtFiber8State37_in_close :
    mtFiber8StateAt 37 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 1 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 1) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep1
  have h2 : mtFiber8StateAt 5 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 1) (mtFiber8StateAt 5) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep5
  have h3 : mtFiber8StateAt 37 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 5) (mtFiber8StateAt 37) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep37
  change mtFiber8StateAt 37 ∈ closeChainFiber mtWord mtFiber8DirectStates (3 + 61) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 3 61 [mtFiber8StateAt 0] (mtFiber8StateAt 37) h3

theorem mtFiber8State38_in_close :
    mtFiber8StateAt 38 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 1 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 1) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep1
  have h2 : mtFiber8StateAt 33 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 1) (mtFiber8StateAt 33) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep33
  have h3 : mtFiber8StateAt 38 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 33) (mtFiber8StateAt 38) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep38
  change mtFiber8StateAt 38 ∈ closeChainFiber mtWord mtFiber8DirectStates (3 + 61) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 3 61 [mtFiber8StateAt 0] (mtFiber8StateAt 38) h3

theorem mtFiber8State39_in_close :
    mtFiber8StateAt 39 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 32 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 32) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep32
  have h2 : mtFiber8StateAt 39 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 32) (mtFiber8StateAt 39) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep39
  change mtFiber8StateAt 39 ∈ closeChainFiber mtWord mtFiber8DirectStates (2 + 62) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 2 62 [mtFiber8StateAt 0] (mtFiber8StateAt 39) h2

theorem mtFiber8State40_in_close :
    mtFiber8StateAt 40 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 8 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 8) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep8
  have h2 : mtFiber8StateAt 40 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 8) (mtFiber8StateAt 40) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep40
  change mtFiber8StateAt 40 ∈ closeChainFiber mtWord mtFiber8DirectStates (2 + 62) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 2 62 [mtFiber8StateAt 0] (mtFiber8StateAt 40) h2

theorem mtFiber8State41_in_close :
    mtFiber8StateAt 41 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 1 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 1) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep1
  have h2 : mtFiber8StateAt 9 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 1) (mtFiber8StateAt 9) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep9
  have h3 : mtFiber8StateAt 41 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 9) (mtFiber8StateAt 41) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep41
  change mtFiber8StateAt 41 ∈ closeChainFiber mtWord mtFiber8DirectStates (3 + 61) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 3 61 [mtFiber8StateAt 0] (mtFiber8StateAt 41) h3

theorem mtFiber8State42_in_close :
    mtFiber8StateAt 42 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 8 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 8) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep8
  have h2 : mtFiber8StateAt 40 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 8) (mtFiber8StateAt 40) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep40
  have h3 : mtFiber8StateAt 42 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 40) (mtFiber8StateAt 42) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep42
  change mtFiber8StateAt 42 ∈ closeChainFiber mtWord mtFiber8DirectStates (3 + 61) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 3 61 [mtFiber8StateAt 0] (mtFiber8StateAt 42) h3

theorem mtFiber8State43_in_close :
    mtFiber8StateAt 43 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 3 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 3) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep3
  have h2 : mtFiber8StateAt 11 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 3) (mtFiber8StateAt 11) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep11
  have h3 : mtFiber8StateAt 43 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 11) (mtFiber8StateAt 43) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep43
  change mtFiber8StateAt 43 ∈ closeChainFiber mtWord mtFiber8DirectStates (3 + 61) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 3 61 [mtFiber8StateAt 0] (mtFiber8StateAt 43) h3

theorem mtFiber8State44_in_close :
    mtFiber8StateAt 44 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 4 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 4) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep4
  have h2 : mtFiber8StateAt 12 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 4) (mtFiber8StateAt 12) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep12
  have h3 : mtFiber8StateAt 44 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 12) (mtFiber8StateAt 44) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep44
  change mtFiber8StateAt 44 ∈ closeChainFiber mtWord mtFiber8DirectStates (3 + 61) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 3 61 [mtFiber8StateAt 0] (mtFiber8StateAt 44) h3

theorem mtFiber8State45_in_close :
    mtFiber8StateAt 45 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 1 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 1) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep1
  have h2 : mtFiber8StateAt 5 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 1) (mtFiber8StateAt 5) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep5
  have h3 : mtFiber8StateAt 13 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 5) (mtFiber8StateAt 13) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep13
  have h4 : mtFiber8StateAt 45 ∈ closeChainFiber mtWord mtFiber8DirectStates 4 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0]
      (mtFiber8StateAt 13) (mtFiber8StateAt 45) (by decide) h3 (by decide)
      mtFiber8ReverseSingleStep45
  change mtFiber8StateAt 45 ∈ closeChainFiber mtWord mtFiber8DirectStates (4 + 60) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 4 60 [mtFiber8StateAt 0] (mtFiber8StateAt 45) h4

theorem mtFiber8State46_in_close :
    mtFiber8StateAt 46 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 1 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 1) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep1
  have h2 : mtFiber8StateAt 9 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 1) (mtFiber8StateAt 9) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep9
  have h3 : mtFiber8StateAt 41 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 9) (mtFiber8StateAt 41) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep41
  have h4 : mtFiber8StateAt 46 ∈ closeChainFiber mtWord mtFiber8DirectStates 4 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0]
      (mtFiber8StateAt 41) (mtFiber8StateAt 46) (by decide) h3 (by decide)
      mtFiber8ReverseSingleStep46
  change mtFiber8StateAt 46 ∈ closeChainFiber mtWord mtFiber8DirectStates (4 + 60) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 4 60 [mtFiber8StateAt 0] (mtFiber8StateAt 46) h4

theorem mtFiber8State47_in_close :
    mtFiber8StateAt 47 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 8 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 8) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep8
  have h2 : mtFiber8StateAt 40 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 8) (mtFiber8StateAt 40) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep40
  have h3 : mtFiber8StateAt 47 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 40) (mtFiber8StateAt 47) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep47
  change mtFiber8StateAt 47 ∈ closeChainFiber mtWord mtFiber8DirectStates (3 + 61) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 3 61 [mtFiber8StateAt 0] (mtFiber8StateAt 47) h3

theorem mtFiber8State48_in_close :
    mtFiber8StateAt 48 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 16 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 16) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep16
  have h2 : mtFiber8StateAt 48 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 16) (mtFiber8StateAt 48) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep48
  change mtFiber8StateAt 48 ∈ closeChainFiber mtWord mtFiber8DirectStates (2 + 62) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 2 62 [mtFiber8StateAt 0] (mtFiber8StateAt 48) h2

theorem mtFiber8State49_in_close :
    mtFiber8StateAt 49 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 1 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 1) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep1
  have h2 : mtFiber8StateAt 17 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 1) (mtFiber8StateAt 17) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep17
  have h3 : mtFiber8StateAt 49 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 17) (mtFiber8StateAt 49) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep49
  change mtFiber8StateAt 49 ∈ closeChainFiber mtWord mtFiber8DirectStates (3 + 61) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 3 61 [mtFiber8StateAt 0] (mtFiber8StateAt 49) h3

theorem mtFiber8State50_in_close :
    mtFiber8StateAt 50 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 16 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 16) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep16
  have h2 : mtFiber8StateAt 48 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 16) (mtFiber8StateAt 48) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep48
  have h3 : mtFiber8StateAt 50 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 48) (mtFiber8StateAt 50) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep50
  change mtFiber8StateAt 50 ∈ closeChainFiber mtWord mtFiber8DirectStates (3 + 61) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 3 61 [mtFiber8StateAt 0] (mtFiber8StateAt 50) h3

theorem mtFiber8State51_in_close :
    mtFiber8StateAt 51 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 3 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 3) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep3
  have h2 : mtFiber8StateAt 19 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 3) (mtFiber8StateAt 19) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep19
  have h3 : mtFiber8StateAt 51 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 19) (mtFiber8StateAt 51) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep51
  change mtFiber8StateAt 51 ∈ closeChainFiber mtWord mtFiber8DirectStates (3 + 61) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 3 61 [mtFiber8StateAt 0] (mtFiber8StateAt 51) h3

theorem mtFiber8State52_in_close :
    mtFiber8StateAt 52 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 4 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 4) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep4
  have h2 : mtFiber8StateAt 20 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 4) (mtFiber8StateAt 20) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep20
  have h3 : mtFiber8StateAt 52 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 20) (mtFiber8StateAt 52) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep52
  change mtFiber8StateAt 52 ∈ closeChainFiber mtWord mtFiber8DirectStates (3 + 61) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 3 61 [mtFiber8StateAt 0] (mtFiber8StateAt 52) h3

theorem mtFiber8State53_in_close :
    mtFiber8StateAt 53 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 1 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 1) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep1
  have h2 : mtFiber8StateAt 5 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 1) (mtFiber8StateAt 5) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep5
  have h3 : mtFiber8StateAt 21 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 5) (mtFiber8StateAt 21) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep21
  have h4 : mtFiber8StateAt 53 ∈ closeChainFiber mtWord mtFiber8DirectStates 4 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0]
      (mtFiber8StateAt 21) (mtFiber8StateAt 53) (by decide) h3 (by decide)
      mtFiber8ReverseSingleStep53
  change mtFiber8StateAt 53 ∈ closeChainFiber mtWord mtFiber8DirectStates (4 + 60) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 4 60 [mtFiber8StateAt 0] (mtFiber8StateAt 53) h4

theorem mtFiber8State54_in_close :
    mtFiber8StateAt 54 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 1 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 1) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep1
  have h2 : mtFiber8StateAt 17 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 1) (mtFiber8StateAt 17) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep17
  have h3 : mtFiber8StateAt 49 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 17) (mtFiber8StateAt 49) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep49
  have h4 : mtFiber8StateAt 54 ∈ closeChainFiber mtWord mtFiber8DirectStates 4 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0]
      (mtFiber8StateAt 49) (mtFiber8StateAt 54) (by decide) h3 (by decide)
      mtFiber8ReverseSingleStep54
  change mtFiber8StateAt 54 ∈ closeChainFiber mtWord mtFiber8DirectStates (4 + 60) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 4 60 [mtFiber8StateAt 0] (mtFiber8StateAt 54) h4

theorem mtFiber8State55_in_close :
    mtFiber8StateAt 55 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 16 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 16) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep16
  have h2 : mtFiber8StateAt 48 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 16) (mtFiber8StateAt 48) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep48
  have h3 : mtFiber8StateAt 55 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 48) (mtFiber8StateAt 55) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep55
  change mtFiber8StateAt 55 ∈ closeChainFiber mtWord mtFiber8DirectStates (3 + 61) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 3 61 [mtFiber8StateAt 0] (mtFiber8StateAt 55) h3

theorem mtFiber8State56_in_close :
    mtFiber8StateAt 56 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 32 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 32) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep32
  have h2 : mtFiber8StateAt 56 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 32) (mtFiber8StateAt 56) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep56
  change mtFiber8StateAt 56 ∈ closeChainFiber mtWord mtFiber8DirectStates (2 + 62) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 2 62 [mtFiber8StateAt 0] (mtFiber8StateAt 56) h2

theorem mtFiber8State57_in_close :
    mtFiber8StateAt 57 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 1 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 1) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep1
  have h2 : mtFiber8StateAt 33 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 1) (mtFiber8StateAt 33) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep33
  have h3 : mtFiber8StateAt 57 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 33) (mtFiber8StateAt 57) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep57
  change mtFiber8StateAt 57 ∈ closeChainFiber mtWord mtFiber8DirectStates (3 + 61) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 3 61 [mtFiber8StateAt 0] (mtFiber8StateAt 57) h3

theorem mtFiber8State58_in_close :
    mtFiber8StateAt 58 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 32 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 32) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep32
  have h2 : mtFiber8StateAt 34 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 32) (mtFiber8StateAt 34) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep34
  have h3 : mtFiber8StateAt 58 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 34) (mtFiber8StateAt 58) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep58
  change mtFiber8StateAt 58 ∈ closeChainFiber mtWord mtFiber8DirectStates (3 + 61) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 3 61 [mtFiber8StateAt 0] (mtFiber8StateAt 58) h3

theorem mtFiber8State59_in_close :
    mtFiber8StateAt 59 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 3 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 3) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep3
  have h2 : mtFiber8StateAt 35 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 3) (mtFiber8StateAt 35) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep35
  have h3 : mtFiber8StateAt 59 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 35) (mtFiber8StateAt 59) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep59
  change mtFiber8StateAt 59 ∈ closeChainFiber mtWord mtFiber8DirectStates (3 + 61) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 3 61 [mtFiber8StateAt 0] (mtFiber8StateAt 59) h3

theorem mtFiber8State60_in_close :
    mtFiber8StateAt 60 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 4 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 4) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep4
  have h2 : mtFiber8StateAt 36 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 4) (mtFiber8StateAt 36) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep36
  have h3 : mtFiber8StateAt 60 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 36) (mtFiber8StateAt 60) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep60
  change mtFiber8StateAt 60 ∈ closeChainFiber mtWord mtFiber8DirectStates (3 + 61) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 3 61 [mtFiber8StateAt 0] (mtFiber8StateAt 60) h3

theorem mtFiber8State61_in_close :
    mtFiber8StateAt 61 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 1 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 1) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep1
  have h2 : mtFiber8StateAt 5 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 1) (mtFiber8StateAt 5) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep5
  have h3 : mtFiber8StateAt 37 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 5) (mtFiber8StateAt 37) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep37
  have h4 : mtFiber8StateAt 61 ∈ closeChainFiber mtWord mtFiber8DirectStates 4 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0]
      (mtFiber8StateAt 37) (mtFiber8StateAt 61) (by decide) h3 (by decide)
      mtFiber8ReverseSingleStep61
  change mtFiber8StateAt 61 ∈ closeChainFiber mtWord mtFiber8DirectStates (4 + 60) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 4 60 [mtFiber8StateAt 0] (mtFiber8StateAt 61) h4

theorem mtFiber8State62_in_close :
    mtFiber8StateAt 62 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 1 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 1) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep1
  have h2 : mtFiber8StateAt 33 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 1) (mtFiber8StateAt 33) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep33
  have h3 : mtFiber8StateAt 38 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 33) (mtFiber8StateAt 38) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep38
  have h4 : mtFiber8StateAt 62 ∈ closeChainFiber mtWord mtFiber8DirectStates 4 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0]
      (mtFiber8StateAt 38) (mtFiber8StateAt 62) (by decide) h3 (by decide)
      mtFiber8ReverseSingleStep62
  change mtFiber8StateAt 62 ∈ closeChainFiber mtWord mtFiber8DirectStates (4 + 60) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 4 60 [mtFiber8StateAt 0] (mtFiber8StateAt 62) h4

theorem mtFiber8State63_in_close :
    mtFiber8StateAt 63 ∈ closeChainFiber mtWord mtFiber8DirectStates mtFiber8DirectStates.length [mtFiber8StateAt 0] := by
  have h0 : mtFiber8StateAt 0 ∈ closeChainFiber mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber8StateAt 32 ∈ closeChainFiber mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 0 [mtFiber8StateAt 0]
      (mtFiber8StateAt 0) (mtFiber8StateAt 32) (by decide) h0 (by decide)
      mtFiber8ReverseSingleStep32
  have h2 : mtFiber8StateAt 39 ∈ closeChainFiber mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 1 [mtFiber8StateAt 0]
      (mtFiber8StateAt 32) (mtFiber8StateAt 39) (by decide) h1 (by decide)
      mtFiber8ReverseSingleStep39
  have h3 : mtFiber8StateAt 63 ∈ closeChainFiber mtWord mtFiber8DirectStates 3 [mtFiber8StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber8DirectStates 2 [mtFiber8StateAt 0]
      (mtFiber8StateAt 39) (mtFiber8StateAt 63) (by decide) h2 (by decide)
      mtFiber8ReverseSingleStep63
  change mtFiber8StateAt 63 ∈ closeChainFiber mtWord mtFiber8DirectStates (3 + 61) [mtFiber8StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber8DirectStates 3 61 [mtFiber8StateAt 0] (mtFiber8StateAt 63) h3

theorem mtFiber8DirectConnected :
    chainFiberConnected mtWord mtFiber8DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber8DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber8State0_in_close
  · subst state
    exact mtFiber8State1_in_close
  · subst state
    exact mtFiber8State2_in_close
  · subst state
    exact mtFiber8State3_in_close
  · subst state
    exact mtFiber8State4_in_close
  · subst state
    exact mtFiber8State5_in_close
  · subst state
    exact mtFiber8State6_in_close
  · subst state
    exact mtFiber8State7_in_close
  · subst state
    exact mtFiber8State8_in_close
  · subst state
    exact mtFiber8State9_in_close
  · subst state
    exact mtFiber8State10_in_close
  · subst state
    exact mtFiber8State11_in_close
  · subst state
    exact mtFiber8State12_in_close
  · subst state
    exact mtFiber8State13_in_close
  · subst state
    exact mtFiber8State14_in_close
  · subst state
    exact mtFiber8State15_in_close
  · subst state
    exact mtFiber8State16_in_close
  · subst state
    exact mtFiber8State17_in_close
  · subst state
    exact mtFiber8State18_in_close
  · subst state
    exact mtFiber8State19_in_close
  · subst state
    exact mtFiber8State20_in_close
  · subst state
    exact mtFiber8State21_in_close
  · subst state
    exact mtFiber8State22_in_close
  · subst state
    exact mtFiber8State23_in_close
  · subst state
    exact mtFiber8State24_in_close
  · subst state
    exact mtFiber8State25_in_close
  · subst state
    exact mtFiber8State26_in_close
  · subst state
    exact mtFiber8State27_in_close
  · subst state
    exact mtFiber8State28_in_close
  · subst state
    exact mtFiber8State29_in_close
  · subst state
    exact mtFiber8State30_in_close
  · subst state
    exact mtFiber8State31_in_close
  · subst state
    exact mtFiber8State32_in_close
  · subst state
    exact mtFiber8State33_in_close
  · subst state
    exact mtFiber8State34_in_close
  · subst state
    exact mtFiber8State35_in_close
  · subst state
    exact mtFiber8State36_in_close
  · subst state
    exact mtFiber8State37_in_close
  · subst state
    exact mtFiber8State38_in_close
  · subst state
    exact mtFiber8State39_in_close
  · subst state
    exact mtFiber8State40_in_close
  · subst state
    exact mtFiber8State41_in_close
  · subst state
    exact mtFiber8State42_in_close
  · subst state
    exact mtFiber8State43_in_close
  · subst state
    exact mtFiber8State44_in_close
  · subst state
    exact mtFiber8State45_in_close
  · subst state
    exact mtFiber8State46_in_close
  · subst state
    exact mtFiber8State47_in_close
  · subst state
    exact mtFiber8State48_in_close
  · subst state
    exact mtFiber8State49_in_close
  · subst state
    exact mtFiber8State50_in_close
  · subst state
    exact mtFiber8State51_in_close
  · subst state
    exact mtFiber8State52_in_close
  · subst state
    exact mtFiber8State53_in_close
  · subst state
    exact mtFiber8State54_in_close
  · subst state
    exact mtFiber8State55_in_close
  · subst state
    exact mtFiber8State56_in_close
  · subst state
    exact mtFiber8State57_in_close
  · subst state
    exact mtFiber8State58_in_close
  · subst state
    exact mtFiber8State59_in_close
  · subst state
    exact mtFiber8State60_in_close
  · subst state
    exact mtFiber8State61_in_close
  · subst state
    exact mtFiber8State62_in_close
  · subst state
    exact mtFiber8State63_in_close
  · cases h
end GoertzelLemma818LengthTwoMTBridge

end Mettapedia.GraphTheory.FourColor
