import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for `mirror,normal` size-64 fiber 76

This module proves direct connectedness for one generated size-64 fiber from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMTBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorTauCertificate
open GoertzelLemma818MirrorTauReverseAudit

def mtFiber76StateAt (i : Nat) : List TauState :=
  directStates (mtFiber76RowAt i).sourceLeft (mtFiber76RowAt i).sourceRight

def mtFiber76DirectStates : List (List TauState) :=
  [mtFiber76StateAt 0, mtFiber76StateAt 1, mtFiber76StateAt 2, mtFiber76StateAt 3, mtFiber76StateAt 4, mtFiber76StateAt 5, mtFiber76StateAt 6, mtFiber76StateAt 7, mtFiber76StateAt 8, mtFiber76StateAt 9, mtFiber76StateAt 10, mtFiber76StateAt 11, mtFiber76StateAt 12, mtFiber76StateAt 13, mtFiber76StateAt 14, mtFiber76StateAt 15, mtFiber76StateAt 16, mtFiber76StateAt 17, mtFiber76StateAt 18, mtFiber76StateAt 19, mtFiber76StateAt 20, mtFiber76StateAt 21, mtFiber76StateAt 22, mtFiber76StateAt 23, mtFiber76StateAt 24, mtFiber76StateAt 25, mtFiber76StateAt 26, mtFiber76StateAt 27, mtFiber76StateAt 28, mtFiber76StateAt 29, mtFiber76StateAt 30, mtFiber76StateAt 31, mtFiber76StateAt 32, mtFiber76StateAt 33, mtFiber76StateAt 34, mtFiber76StateAt 35, mtFiber76StateAt 36, mtFiber76StateAt 37, mtFiber76StateAt 38, mtFiber76StateAt 39, mtFiber76StateAt 40, mtFiber76StateAt 41, mtFiber76StateAt 42, mtFiber76StateAt 43, mtFiber76StateAt 44, mtFiber76StateAt 45, mtFiber76StateAt 46, mtFiber76StateAt 47, mtFiber76StateAt 48, mtFiber76StateAt 49, mtFiber76StateAt 50, mtFiber76StateAt 51, mtFiber76StateAt 52, mtFiber76StateAt 53, mtFiber76StateAt 54, mtFiber76StateAt 55, mtFiber76StateAt 56, mtFiber76StateAt 57, mtFiber76StateAt 58, mtFiber76StateAt 59, mtFiber76StateAt 60, mtFiber76StateAt 61, mtFiber76StateAt 62, mtFiber76StateAt 63]

theorem mtFiber76ReverseRow_1_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk0_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 0) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 0) (mtFiber76StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 0) (mtFiber76StateAt 1)
    (mtFiber76RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 1) (by decide) mtFiber76ReverseRow_1_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_2_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk1_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 2) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber76ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 0) (mtFiber76StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 0) (mtFiber76StateAt 2)
    (mtFiber76RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 2) (by decide) mtFiber76ReverseRow_2_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_3_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk1_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 2) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 1) (mtFiber76StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 1) (mtFiber76StateAt 3)
    (mtFiber76RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 3) (by decide) mtFiber76ReverseRow_3_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_4_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk2_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 4) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber76ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 2) (mtFiber76StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 2) (mtFiber76StateAt 4)
    (mtFiber76RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 4) (by decide) mtFiber76ReverseRow_4_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_5_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk2_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 4) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 7) (mtFiber76StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 7) (mtFiber76StateAt 5)
    (mtFiber76RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 5) (by decide) mtFiber76ReverseRow_5_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_6_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk3_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 6) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber76ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 1) (mtFiber76StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 1) (mtFiber76StateAt 6)
    (mtFiber76RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 6) (by decide) mtFiber76ReverseRow_6_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_7_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk3_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 6) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 0) (mtFiber76StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 0) (mtFiber76StateAt 7)
    (mtFiber76RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 7) (by decide) mtFiber76ReverseRow_7_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_8_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk4_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 8) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber76ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 0) (mtFiber76StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 0) (mtFiber76StateAt 8)
    (mtFiber76RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 8) (by decide) mtFiber76ReverseRow_8_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_9_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk4_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 8) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 1) (mtFiber76StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 1) (mtFiber76StateAt 9)
    (mtFiber76RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 9) (by decide) mtFiber76ReverseRow_9_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_10_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk5_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 10) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber76ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 2) (mtFiber76StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 2) (mtFiber76StateAt 10)
    (mtFiber76RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 10) (by decide) mtFiber76ReverseRow_10_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_11_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk5_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 10) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 3) (mtFiber76StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 3) (mtFiber76StateAt 11)
    (mtFiber76RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 11) (by decide) mtFiber76ReverseRow_11_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_12_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk6_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 12) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber76ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 4) (mtFiber76StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 4) (mtFiber76StateAt 12)
    (mtFiber76RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 12) (by decide) mtFiber76ReverseRow_12_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_13_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk6_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 12) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 5) (mtFiber76StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 5) (mtFiber76StateAt 13)
    (mtFiber76RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 13) (by decide) mtFiber76ReverseRow_13_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_14_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk7_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 14) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber76ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 6) (mtFiber76StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 6) (mtFiber76StateAt 14)
    (mtFiber76RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 14) (by decide) mtFiber76ReverseRow_14_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_15_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk7_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 14) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 7) (mtFiber76StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 7) (mtFiber76StateAt 15)
    (mtFiber76RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 15) (by decide) mtFiber76ReverseRow_15_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_16_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 16) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk8_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 16) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber76ReverseSingleStep16 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 8) (mtFiber76StateAt 16) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 8) (mtFiber76StateAt 16)
    (mtFiber76RowAt 16).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 16) (by decide) mtFiber76ReverseRow_16_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_17_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 17) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk8_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 16) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep17 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 9) (mtFiber76StateAt 17) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 9) (mtFiber76StateAt 17)
    (mtFiber76RowAt 17).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 17) (by decide) mtFiber76ReverseRow_17_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_18_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 18) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk9_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 18) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber76ReverseSingleStep18 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 10) (mtFiber76StateAt 18) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 10) (mtFiber76StateAt 18)
    (mtFiber76RowAt 18).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 18) (by decide) mtFiber76ReverseRow_18_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_19_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 19) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk9_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 18) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep19 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 11) (mtFiber76StateAt 19) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 11) (mtFiber76StateAt 19)
    (mtFiber76RowAt 19).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 19) (by decide) mtFiber76ReverseRow_19_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_20_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 20) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk10_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 20) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber76ReverseSingleStep20 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 12) (mtFiber76StateAt 20) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 12) (mtFiber76StateAt 20)
    (mtFiber76RowAt 20).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 20) (by decide) mtFiber76ReverseRow_20_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_21_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 21) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk10_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 20) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep21 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 13) (mtFiber76StateAt 21) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 13) (mtFiber76StateAt 21)
    (mtFiber76RowAt 21).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 21) (by decide) mtFiber76ReverseRow_21_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_22_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 22) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk11_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 22) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber76ReverseSingleStep22 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 14) (mtFiber76StateAt 22) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 14) (mtFiber76StateAt 22)
    (mtFiber76RowAt 22).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 22) (by decide) mtFiber76ReverseRow_22_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_23_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 23) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk11_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 22) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep23 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 15) (mtFiber76StateAt 23) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 15) (mtFiber76StateAt 23)
    (mtFiber76RowAt 23).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 23) (by decide) mtFiber76ReverseRow_23_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_24_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 24) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk12_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 24) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber76ReverseSingleStep24 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 0) (mtFiber76StateAt 24) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 0) (mtFiber76StateAt 24)
    (mtFiber76RowAt 24).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 24) (by decide) mtFiber76ReverseRow_24_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_25_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 25) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk12_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 24) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep25 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 1) (mtFiber76StateAt 25) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 1) (mtFiber76StateAt 25)
    (mtFiber76RowAt 25).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 25) (by decide) mtFiber76ReverseRow_25_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_26_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 26) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk13_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 26) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber76ReverseSingleStep26 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 2) (mtFiber76StateAt 26) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 2) (mtFiber76StateAt 26)
    (mtFiber76RowAt 26).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 26) (by decide) mtFiber76ReverseRow_26_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_27_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 27) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk13_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 26) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep27 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 3) (mtFiber76StateAt 27) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 3) (mtFiber76StateAt 27)
    (mtFiber76RowAt 27).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 27) (by decide) mtFiber76ReverseRow_27_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_28_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 28) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk14_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 28) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber76ReverseSingleStep28 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 4) (mtFiber76StateAt 28) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 4) (mtFiber76StateAt 28)
    (mtFiber76RowAt 28).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 28) (by decide) mtFiber76ReverseRow_28_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_29_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 29) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk14_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 28) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep29 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 5) (mtFiber76StateAt 29) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 5) (mtFiber76StateAt 29)
    (mtFiber76RowAt 29).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 29) (by decide) mtFiber76ReverseRow_29_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_30_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 30) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk15_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 30) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber76ReverseSingleStep30 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 6) (mtFiber76StateAt 30) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 6) (mtFiber76StateAt 30)
    (mtFiber76RowAt 30).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 30) (by decide) mtFiber76ReverseRow_30_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_31_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 31) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk15_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 30) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep31 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 7) (mtFiber76StateAt 31) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 7) (mtFiber76StateAt 31)
    (mtFiber76RowAt 31).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 31) (by decide) mtFiber76ReverseRow_31_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_32_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 32) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk16_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 32) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber76ReverseSingleStep32 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 0) (mtFiber76StateAt 32) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 0) (mtFiber76StateAt 32)
    (mtFiber76RowAt 32).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 32) (by decide) mtFiber76ReverseRow_32_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_33_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 33) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk16_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 32) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep33 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 1) (mtFiber76StateAt 33) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 1) (mtFiber76StateAt 33)
    (mtFiber76RowAt 33).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 33) (by decide) mtFiber76ReverseRow_33_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_34_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 34) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk17_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 34) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber76ReverseSingleStep34 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 2) (mtFiber76StateAt 34) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 2) (mtFiber76StateAt 34)
    (mtFiber76RowAt 34).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 34) (by decide) mtFiber76ReverseRow_34_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_35_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 35) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk17_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 34) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep35 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 3) (mtFiber76StateAt 35) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 3) (mtFiber76StateAt 35)
    (mtFiber76RowAt 35).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 35) (by decide) mtFiber76ReverseRow_35_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_36_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 36) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk18_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 36) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber76ReverseSingleStep36 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 32) (mtFiber76StateAt 36) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 32) (mtFiber76StateAt 36)
    (mtFiber76RowAt 36).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 36) (by decide) mtFiber76ReverseRow_36_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_37_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 37) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk18_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 36) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep37 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 33) (mtFiber76StateAt 37) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 33) (mtFiber76StateAt 37)
    (mtFiber76RowAt 37).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 37) (by decide) mtFiber76ReverseRow_37_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_38_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 38) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk19_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 38) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber76ReverseSingleStep38 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 6) (mtFiber76StateAt 38) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 6) (mtFiber76StateAt 38)
    (mtFiber76RowAt 38).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 38) (by decide) mtFiber76ReverseRow_38_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_39_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 39) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk19_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 38) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep39 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 7) (mtFiber76StateAt 39) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 7) (mtFiber76StateAt 39)
    (mtFiber76RowAt 39).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 39) (by decide) mtFiber76ReverseRow_39_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_40_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 40) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk20_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 40) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber76ReverseSingleStep40 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 8) (mtFiber76StateAt 40) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 8) (mtFiber76StateAt 40)
    (mtFiber76RowAt 40).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 40) (by decide) mtFiber76ReverseRow_40_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_41_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 41) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk20_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 40) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep41 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 9) (mtFiber76StateAt 41) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 9) (mtFiber76StateAt 41)
    (mtFiber76RowAt 41).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 41) (by decide) mtFiber76ReverseRow_41_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_42_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 42) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk21_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 42) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber76ReverseSingleStep42 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 10) (mtFiber76StateAt 42) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 10) (mtFiber76StateAt 42)
    (mtFiber76RowAt 42).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 42) (by decide) mtFiber76ReverseRow_42_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_43_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 43) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk21_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 42) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep43 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 11) (mtFiber76StateAt 43) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 11) (mtFiber76StateAt 43)
    (mtFiber76RowAt 43).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 43) (by decide) mtFiber76ReverseRow_43_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_44_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 44) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk22_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 44) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber76ReverseSingleStep44 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 40) (mtFiber76StateAt 44) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 40) (mtFiber76StateAt 44)
    (mtFiber76RowAt 44).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 44) (by decide) mtFiber76ReverseRow_44_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_45_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 45) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk22_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 44) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep45 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 41) (mtFiber76StateAt 45) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 41) (mtFiber76StateAt 45)
    (mtFiber76RowAt 45).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 45) (by decide) mtFiber76ReverseRow_45_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_46_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 46) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk23_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 46) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber76ReverseSingleStep46 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 14) (mtFiber76StateAt 46) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 14) (mtFiber76StateAt 46)
    (mtFiber76RowAt 46).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 46) (by decide) mtFiber76ReverseRow_46_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_47_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 47) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk23_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 46) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep47 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 15) (mtFiber76StateAt 47) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 15) (mtFiber76StateAt 47)
    (mtFiber76RowAt 47).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 47) (by decide) mtFiber76ReverseRow_47_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_48_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 48) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk24_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 48) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber76ReverseSingleStep48 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 32) (mtFiber76StateAt 48) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 32) (mtFiber76StateAt 48)
    (mtFiber76RowAt 48).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 48) (by decide) mtFiber76ReverseRow_48_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_49_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 49) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk24_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 48) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep49 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 33) (mtFiber76StateAt 49) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 33) (mtFiber76StateAt 49)
    (mtFiber76RowAt 49).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 49) (by decide) mtFiber76ReverseRow_49_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_50_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 50) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk25_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 50) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber76ReverseSingleStep50 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 34) (mtFiber76StateAt 50) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 34) (mtFiber76StateAt 50)
    (mtFiber76RowAt 50).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 50) (by decide) mtFiber76ReverseRow_50_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_51_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 51) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk25_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 50) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep51 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 35) (mtFiber76StateAt 51) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 35) (mtFiber76StateAt 51)
    (mtFiber76RowAt 51).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 51) (by decide) mtFiber76ReverseRow_51_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_52_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 52) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk26_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 52) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber76ReverseSingleStep52 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 36) (mtFiber76StateAt 52) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 36) (mtFiber76StateAt 52)
    (mtFiber76RowAt 52).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 52) (by decide) mtFiber76ReverseRow_52_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_53_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 53) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk26_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 52) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep53 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 37) (mtFiber76StateAt 53) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 37) (mtFiber76StateAt 53)
    (mtFiber76RowAt 53).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 53) (by decide) mtFiber76ReverseRow_53_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_54_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 54) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk27_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 54) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber76ReverseSingleStep54 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 38) (mtFiber76StateAt 54) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 38) (mtFiber76StateAt 54)
    (mtFiber76RowAt 54).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 54) (by decide) mtFiber76ReverseRow_54_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_55_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 55) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk27_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 54) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep55 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 39) (mtFiber76StateAt 55) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 39) (mtFiber76StateAt 55)
    (mtFiber76RowAt 55).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 55) (by decide) mtFiber76ReverseRow_55_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_56_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 56) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk28_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 56) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber76ReverseSingleStep56 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 24) (mtFiber76StateAt 56) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 24) (mtFiber76StateAt 56)
    (mtFiber76RowAt 56).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 56) (by decide) mtFiber76ReverseRow_56_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_57_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 57) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk28_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 56) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep57 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 25) (mtFiber76StateAt 57) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 25) (mtFiber76StateAt 57)
    (mtFiber76RowAt 57).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 57) (by decide) mtFiber76ReverseRow_57_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_58_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 58) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk29_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 58) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber76ReverseSingleStep58 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 26) (mtFiber76StateAt 58) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 26) (mtFiber76StateAt 58)
    (mtFiber76RowAt 58).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 58) (by decide) mtFiber76ReverseRow_58_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_59_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 59) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk29_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 58) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep59 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 27) (mtFiber76StateAt 59) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 27) (mtFiber76StateAt 59)
    (mtFiber76RowAt 59).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 59) (by decide) mtFiber76ReverseRow_59_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_60_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 60) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk30_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 60) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber76ReverseSingleStep60 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 56) (mtFiber76StateAt 60) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 56) (mtFiber76StateAt 60)
    (mtFiber76RowAt 60).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 60) (by decide) mtFiber76ReverseRow_60_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_61_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 61) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk30_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 60) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep61 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 57) (mtFiber76StateAt 61) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 57) (mtFiber76StateAt 61)
    (mtFiber76RowAt 61).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 61) (by decide) mtFiber76ReverseRow_61_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_62_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 62) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk31_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 62) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber76ReverseSingleStep62 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 30) (mtFiber76StateAt 62) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 30) (mtFiber76StateAt 62)
    (mtFiber76RowAt 62).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 62) (by decide) mtFiber76ReverseRow_62_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76ReverseRow_63_ok :
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 63) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber76Chunk31_ok
  change (mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 62) &&
    mtRowReverseValid mtFiber76Key mtFiber76Expected (mtFiber76RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber76ReverseSingleStep63 :
    chainSingleKempeStep mtWord (mtFiber76StateAt 31) (mtFiber76StateAt 63) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber76StateAt 31) (mtFiber76StateAt 63)
    (mtFiber76RowAt 63).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber76Key mtFiber76Expected
        (mtFiber76RowAt 63) (by decide) mtFiber76ReverseRow_63_ok
      simpa [mtFiber76StateAt, mtFiber76RowAt, mtFiber76Rows, listGetD, directRow] using h)

theorem mtFiber76State0_in_close :
    mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  change mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 64 [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 0 64 [mtFiber76StateAt 0] (mtFiber76StateAt 0) (by simp [closeChainFiber])

theorem mtFiber76State1_in_close :
    mtFiber76StateAt 1 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 1 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 1) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep1
  change mtFiber76StateAt 1 ∈ closeChainFiber mtWord mtFiber76DirectStates (1 + 63) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 1 63 [mtFiber76StateAt 0] (mtFiber76StateAt 1) h1

theorem mtFiber76State2_in_close :
    mtFiber76StateAt 2 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 2 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 2) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep2
  change mtFiber76StateAt 2 ∈ closeChainFiber mtWord mtFiber76DirectStates (1 + 63) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 1 63 [mtFiber76StateAt 0] (mtFiber76StateAt 2) h1

theorem mtFiber76State3_in_close :
    mtFiber76StateAt 3 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 1 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 1) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep1
  have h2 : mtFiber76StateAt 3 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 1) (mtFiber76StateAt 3) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep3
  change mtFiber76StateAt 3 ∈ closeChainFiber mtWord mtFiber76DirectStates (2 + 62) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 2 62 [mtFiber76StateAt 0] (mtFiber76StateAt 3) h2

theorem mtFiber76State4_in_close :
    mtFiber76StateAt 4 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 2 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 2) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep2
  have h2 : mtFiber76StateAt 4 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 2) (mtFiber76StateAt 4) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep4
  change mtFiber76StateAt 4 ∈ closeChainFiber mtWord mtFiber76DirectStates (2 + 62) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 2 62 [mtFiber76StateAt 0] (mtFiber76StateAt 4) h2

theorem mtFiber76State5_in_close :
    mtFiber76StateAt 5 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 7 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 7) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep7
  have h2 : mtFiber76StateAt 5 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 7) (mtFiber76StateAt 5) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep5
  change mtFiber76StateAt 5 ∈ closeChainFiber mtWord mtFiber76DirectStates (2 + 62) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 2 62 [mtFiber76StateAt 0] (mtFiber76StateAt 5) h2

theorem mtFiber76State6_in_close :
    mtFiber76StateAt 6 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 1 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 1) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep1
  have h2 : mtFiber76StateAt 6 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 1) (mtFiber76StateAt 6) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep6
  change mtFiber76StateAt 6 ∈ closeChainFiber mtWord mtFiber76DirectStates (2 + 62) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 2 62 [mtFiber76StateAt 0] (mtFiber76StateAt 6) h2

theorem mtFiber76State7_in_close :
    mtFiber76StateAt 7 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 7 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 7) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep7
  change mtFiber76StateAt 7 ∈ closeChainFiber mtWord mtFiber76DirectStates (1 + 63) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 1 63 [mtFiber76StateAt 0] (mtFiber76StateAt 7) h1

theorem mtFiber76State8_in_close :
    mtFiber76StateAt 8 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 8 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 8) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep8
  change mtFiber76StateAt 8 ∈ closeChainFiber mtWord mtFiber76DirectStates (1 + 63) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 1 63 [mtFiber76StateAt 0] (mtFiber76StateAt 8) h1

theorem mtFiber76State9_in_close :
    mtFiber76StateAt 9 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 1 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 1) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep1
  have h2 : mtFiber76StateAt 9 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 1) (mtFiber76StateAt 9) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep9
  change mtFiber76StateAt 9 ∈ closeChainFiber mtWord mtFiber76DirectStates (2 + 62) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 2 62 [mtFiber76StateAt 0] (mtFiber76StateAt 9) h2

theorem mtFiber76State10_in_close :
    mtFiber76StateAt 10 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 2 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 2) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep2
  have h2 : mtFiber76StateAt 10 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 2) (mtFiber76StateAt 10) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep10
  change mtFiber76StateAt 10 ∈ closeChainFiber mtWord mtFiber76DirectStates (2 + 62) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 2 62 [mtFiber76StateAt 0] (mtFiber76StateAt 10) h2

theorem mtFiber76State11_in_close :
    mtFiber76StateAt 11 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 1 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 1) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep1
  have h2 : mtFiber76StateAt 3 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 1) (mtFiber76StateAt 3) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep3
  have h3 : mtFiber76StateAt 11 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 3) (mtFiber76StateAt 11) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep11
  change mtFiber76StateAt 11 ∈ closeChainFiber mtWord mtFiber76DirectStates (3 + 61) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 3 61 [mtFiber76StateAt 0] (mtFiber76StateAt 11) h3

theorem mtFiber76State12_in_close :
    mtFiber76StateAt 12 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 2 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 2) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep2
  have h2 : mtFiber76StateAt 4 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 2) (mtFiber76StateAt 4) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep4
  have h3 : mtFiber76StateAt 12 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 4) (mtFiber76StateAt 12) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep12
  change mtFiber76StateAt 12 ∈ closeChainFiber mtWord mtFiber76DirectStates (3 + 61) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 3 61 [mtFiber76StateAt 0] (mtFiber76StateAt 12) h3

theorem mtFiber76State13_in_close :
    mtFiber76StateAt 13 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 7 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 7) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep7
  have h2 : mtFiber76StateAt 5 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 7) (mtFiber76StateAt 5) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep5
  have h3 : mtFiber76StateAt 13 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 5) (mtFiber76StateAt 13) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep13
  change mtFiber76StateAt 13 ∈ closeChainFiber mtWord mtFiber76DirectStates (3 + 61) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 3 61 [mtFiber76StateAt 0] (mtFiber76StateAt 13) h3

theorem mtFiber76State14_in_close :
    mtFiber76StateAt 14 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 1 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 1) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep1
  have h2 : mtFiber76StateAt 6 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 1) (mtFiber76StateAt 6) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep6
  have h3 : mtFiber76StateAt 14 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 6) (mtFiber76StateAt 14) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep14
  change mtFiber76StateAt 14 ∈ closeChainFiber mtWord mtFiber76DirectStates (3 + 61) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 3 61 [mtFiber76StateAt 0] (mtFiber76StateAt 14) h3

theorem mtFiber76State15_in_close :
    mtFiber76StateAt 15 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 7 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 7) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep7
  have h2 : mtFiber76StateAt 15 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 7) (mtFiber76StateAt 15) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep15
  change mtFiber76StateAt 15 ∈ closeChainFiber mtWord mtFiber76DirectStates (2 + 62) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 2 62 [mtFiber76StateAt 0] (mtFiber76StateAt 15) h2

theorem mtFiber76State16_in_close :
    mtFiber76StateAt 16 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 8 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 8) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep8
  have h2 : mtFiber76StateAt 16 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 8) (mtFiber76StateAt 16) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep16
  change mtFiber76StateAt 16 ∈ closeChainFiber mtWord mtFiber76DirectStates (2 + 62) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 2 62 [mtFiber76StateAt 0] (mtFiber76StateAt 16) h2

theorem mtFiber76State17_in_close :
    mtFiber76StateAt 17 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 1 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 1) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep1
  have h2 : mtFiber76StateAt 9 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 1) (mtFiber76StateAt 9) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep9
  have h3 : mtFiber76StateAt 17 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 9) (mtFiber76StateAt 17) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep17
  change mtFiber76StateAt 17 ∈ closeChainFiber mtWord mtFiber76DirectStates (3 + 61) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 3 61 [mtFiber76StateAt 0] (mtFiber76StateAt 17) h3

theorem mtFiber76State18_in_close :
    mtFiber76StateAt 18 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 2 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 2) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep2
  have h2 : mtFiber76StateAt 10 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 2) (mtFiber76StateAt 10) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep10
  have h3 : mtFiber76StateAt 18 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 10) (mtFiber76StateAt 18) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep18
  change mtFiber76StateAt 18 ∈ closeChainFiber mtWord mtFiber76DirectStates (3 + 61) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 3 61 [mtFiber76StateAt 0] (mtFiber76StateAt 18) h3

theorem mtFiber76State19_in_close :
    mtFiber76StateAt 19 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 1 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 1) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep1
  have h2 : mtFiber76StateAt 3 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 1) (mtFiber76StateAt 3) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep3
  have h3 : mtFiber76StateAt 11 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 3) (mtFiber76StateAt 11) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep11
  have h4 : mtFiber76StateAt 19 ∈ closeChainFiber mtWord mtFiber76DirectStates 4 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0]
      (mtFiber76StateAt 11) (mtFiber76StateAt 19) (by decide) h3 (by decide)
      mtFiber76ReverseSingleStep19
  change mtFiber76StateAt 19 ∈ closeChainFiber mtWord mtFiber76DirectStates (4 + 60) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 4 60 [mtFiber76StateAt 0] (mtFiber76StateAt 19) h4

theorem mtFiber76State20_in_close :
    mtFiber76StateAt 20 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 2 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 2) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep2
  have h2 : mtFiber76StateAt 4 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 2) (mtFiber76StateAt 4) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep4
  have h3 : mtFiber76StateAt 12 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 4) (mtFiber76StateAt 12) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep12
  have h4 : mtFiber76StateAt 20 ∈ closeChainFiber mtWord mtFiber76DirectStates 4 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0]
      (mtFiber76StateAt 12) (mtFiber76StateAt 20) (by decide) h3 (by decide)
      mtFiber76ReverseSingleStep20
  change mtFiber76StateAt 20 ∈ closeChainFiber mtWord mtFiber76DirectStates (4 + 60) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 4 60 [mtFiber76StateAt 0] (mtFiber76StateAt 20) h4

theorem mtFiber76State21_in_close :
    mtFiber76StateAt 21 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 7 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 7) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep7
  have h2 : mtFiber76StateAt 5 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 7) (mtFiber76StateAt 5) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep5
  have h3 : mtFiber76StateAt 13 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 5) (mtFiber76StateAt 13) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep13
  have h4 : mtFiber76StateAt 21 ∈ closeChainFiber mtWord mtFiber76DirectStates 4 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0]
      (mtFiber76StateAt 13) (mtFiber76StateAt 21) (by decide) h3 (by decide)
      mtFiber76ReverseSingleStep21
  change mtFiber76StateAt 21 ∈ closeChainFiber mtWord mtFiber76DirectStates (4 + 60) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 4 60 [mtFiber76StateAt 0] (mtFiber76StateAt 21) h4

theorem mtFiber76State22_in_close :
    mtFiber76StateAt 22 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 1 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 1) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep1
  have h2 : mtFiber76StateAt 6 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 1) (mtFiber76StateAt 6) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep6
  have h3 : mtFiber76StateAt 14 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 6) (mtFiber76StateAt 14) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep14
  have h4 : mtFiber76StateAt 22 ∈ closeChainFiber mtWord mtFiber76DirectStates 4 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0]
      (mtFiber76StateAt 14) (mtFiber76StateAt 22) (by decide) h3 (by decide)
      mtFiber76ReverseSingleStep22
  change mtFiber76StateAt 22 ∈ closeChainFiber mtWord mtFiber76DirectStates (4 + 60) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 4 60 [mtFiber76StateAt 0] (mtFiber76StateAt 22) h4

theorem mtFiber76State23_in_close :
    mtFiber76StateAt 23 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 7 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 7) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep7
  have h2 : mtFiber76StateAt 15 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 7) (mtFiber76StateAt 15) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep15
  have h3 : mtFiber76StateAt 23 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 15) (mtFiber76StateAt 23) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep23
  change mtFiber76StateAt 23 ∈ closeChainFiber mtWord mtFiber76DirectStates (3 + 61) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 3 61 [mtFiber76StateAt 0] (mtFiber76StateAt 23) h3

theorem mtFiber76State24_in_close :
    mtFiber76StateAt 24 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 24 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 24) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep24
  change mtFiber76StateAt 24 ∈ closeChainFiber mtWord mtFiber76DirectStates (1 + 63) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 1 63 [mtFiber76StateAt 0] (mtFiber76StateAt 24) h1

theorem mtFiber76State25_in_close :
    mtFiber76StateAt 25 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 1 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 1) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep1
  have h2 : mtFiber76StateAt 25 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 1) (mtFiber76StateAt 25) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep25
  change mtFiber76StateAt 25 ∈ closeChainFiber mtWord mtFiber76DirectStates (2 + 62) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 2 62 [mtFiber76StateAt 0] (mtFiber76StateAt 25) h2

theorem mtFiber76State26_in_close :
    mtFiber76StateAt 26 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 2 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 2) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep2
  have h2 : mtFiber76StateAt 26 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 2) (mtFiber76StateAt 26) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep26
  change mtFiber76StateAt 26 ∈ closeChainFiber mtWord mtFiber76DirectStates (2 + 62) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 2 62 [mtFiber76StateAt 0] (mtFiber76StateAt 26) h2

theorem mtFiber76State27_in_close :
    mtFiber76StateAt 27 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 1 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 1) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep1
  have h2 : mtFiber76StateAt 3 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 1) (mtFiber76StateAt 3) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep3
  have h3 : mtFiber76StateAt 27 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 3) (mtFiber76StateAt 27) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep27
  change mtFiber76StateAt 27 ∈ closeChainFiber mtWord mtFiber76DirectStates (3 + 61) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 3 61 [mtFiber76StateAt 0] (mtFiber76StateAt 27) h3

theorem mtFiber76State28_in_close :
    mtFiber76StateAt 28 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 2 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 2) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep2
  have h2 : mtFiber76StateAt 4 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 2) (mtFiber76StateAt 4) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep4
  have h3 : mtFiber76StateAt 28 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 4) (mtFiber76StateAt 28) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep28
  change mtFiber76StateAt 28 ∈ closeChainFiber mtWord mtFiber76DirectStates (3 + 61) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 3 61 [mtFiber76StateAt 0] (mtFiber76StateAt 28) h3

theorem mtFiber76State29_in_close :
    mtFiber76StateAt 29 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 7 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 7) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep7
  have h2 : mtFiber76StateAt 5 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 7) (mtFiber76StateAt 5) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep5
  have h3 : mtFiber76StateAt 29 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 5) (mtFiber76StateAt 29) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep29
  change mtFiber76StateAt 29 ∈ closeChainFiber mtWord mtFiber76DirectStates (3 + 61) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 3 61 [mtFiber76StateAt 0] (mtFiber76StateAt 29) h3

theorem mtFiber76State30_in_close :
    mtFiber76StateAt 30 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 1 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 1) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep1
  have h2 : mtFiber76StateAt 6 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 1) (mtFiber76StateAt 6) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep6
  have h3 : mtFiber76StateAt 30 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 6) (mtFiber76StateAt 30) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep30
  change mtFiber76StateAt 30 ∈ closeChainFiber mtWord mtFiber76DirectStates (3 + 61) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 3 61 [mtFiber76StateAt 0] (mtFiber76StateAt 30) h3

theorem mtFiber76State31_in_close :
    mtFiber76StateAt 31 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 7 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 7) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep7
  have h2 : mtFiber76StateAt 31 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 7) (mtFiber76StateAt 31) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep31
  change mtFiber76StateAt 31 ∈ closeChainFiber mtWord mtFiber76DirectStates (2 + 62) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 2 62 [mtFiber76StateAt 0] (mtFiber76StateAt 31) h2

theorem mtFiber76State32_in_close :
    mtFiber76StateAt 32 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 32 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 32) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep32
  change mtFiber76StateAt 32 ∈ closeChainFiber mtWord mtFiber76DirectStates (1 + 63) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 1 63 [mtFiber76StateAt 0] (mtFiber76StateAt 32) h1

theorem mtFiber76State33_in_close :
    mtFiber76StateAt 33 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 1 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 1) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep1
  have h2 : mtFiber76StateAt 33 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 1) (mtFiber76StateAt 33) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep33
  change mtFiber76StateAt 33 ∈ closeChainFiber mtWord mtFiber76DirectStates (2 + 62) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 2 62 [mtFiber76StateAt 0] (mtFiber76StateAt 33) h2

theorem mtFiber76State34_in_close :
    mtFiber76StateAt 34 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 2 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 2) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep2
  have h2 : mtFiber76StateAt 34 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 2) (mtFiber76StateAt 34) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep34
  change mtFiber76StateAt 34 ∈ closeChainFiber mtWord mtFiber76DirectStates (2 + 62) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 2 62 [mtFiber76StateAt 0] (mtFiber76StateAt 34) h2

theorem mtFiber76State35_in_close :
    mtFiber76StateAt 35 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 1 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 1) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep1
  have h2 : mtFiber76StateAt 3 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 1) (mtFiber76StateAt 3) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep3
  have h3 : mtFiber76StateAt 35 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 3) (mtFiber76StateAt 35) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep35
  change mtFiber76StateAt 35 ∈ closeChainFiber mtWord mtFiber76DirectStates (3 + 61) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 3 61 [mtFiber76StateAt 0] (mtFiber76StateAt 35) h3

theorem mtFiber76State36_in_close :
    mtFiber76StateAt 36 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 32 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 32) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep32
  have h2 : mtFiber76StateAt 36 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 32) (mtFiber76StateAt 36) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep36
  change mtFiber76StateAt 36 ∈ closeChainFiber mtWord mtFiber76DirectStates (2 + 62) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 2 62 [mtFiber76StateAt 0] (mtFiber76StateAt 36) h2

theorem mtFiber76State37_in_close :
    mtFiber76StateAt 37 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 1 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 1) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep1
  have h2 : mtFiber76StateAt 33 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 1) (mtFiber76StateAt 33) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep33
  have h3 : mtFiber76StateAt 37 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 33) (mtFiber76StateAt 37) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep37
  change mtFiber76StateAt 37 ∈ closeChainFiber mtWord mtFiber76DirectStates (3 + 61) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 3 61 [mtFiber76StateAt 0] (mtFiber76StateAt 37) h3

theorem mtFiber76State38_in_close :
    mtFiber76StateAt 38 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 1 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 1) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep1
  have h2 : mtFiber76StateAt 6 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 1) (mtFiber76StateAt 6) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep6
  have h3 : mtFiber76StateAt 38 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 6) (mtFiber76StateAt 38) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep38
  change mtFiber76StateAt 38 ∈ closeChainFiber mtWord mtFiber76DirectStates (3 + 61) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 3 61 [mtFiber76StateAt 0] (mtFiber76StateAt 38) h3

theorem mtFiber76State39_in_close :
    mtFiber76StateAt 39 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 7 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 7) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep7
  have h2 : mtFiber76StateAt 39 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 7) (mtFiber76StateAt 39) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep39
  change mtFiber76StateAt 39 ∈ closeChainFiber mtWord mtFiber76DirectStates (2 + 62) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 2 62 [mtFiber76StateAt 0] (mtFiber76StateAt 39) h2

theorem mtFiber76State40_in_close :
    mtFiber76StateAt 40 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 8 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 8) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep8
  have h2 : mtFiber76StateAt 40 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 8) (mtFiber76StateAt 40) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep40
  change mtFiber76StateAt 40 ∈ closeChainFiber mtWord mtFiber76DirectStates (2 + 62) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 2 62 [mtFiber76StateAt 0] (mtFiber76StateAt 40) h2

theorem mtFiber76State41_in_close :
    mtFiber76StateAt 41 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 1 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 1) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep1
  have h2 : mtFiber76StateAt 9 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 1) (mtFiber76StateAt 9) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep9
  have h3 : mtFiber76StateAt 41 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 9) (mtFiber76StateAt 41) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep41
  change mtFiber76StateAt 41 ∈ closeChainFiber mtWord mtFiber76DirectStates (3 + 61) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 3 61 [mtFiber76StateAt 0] (mtFiber76StateAt 41) h3

theorem mtFiber76State42_in_close :
    mtFiber76StateAt 42 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 2 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 2) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep2
  have h2 : mtFiber76StateAt 10 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 2) (mtFiber76StateAt 10) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep10
  have h3 : mtFiber76StateAt 42 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 10) (mtFiber76StateAt 42) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep42
  change mtFiber76StateAt 42 ∈ closeChainFiber mtWord mtFiber76DirectStates (3 + 61) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 3 61 [mtFiber76StateAt 0] (mtFiber76StateAt 42) h3

theorem mtFiber76State43_in_close :
    mtFiber76StateAt 43 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 1 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 1) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep1
  have h2 : mtFiber76StateAt 3 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 1) (mtFiber76StateAt 3) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep3
  have h3 : mtFiber76StateAt 11 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 3) (mtFiber76StateAt 11) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep11
  have h4 : mtFiber76StateAt 43 ∈ closeChainFiber mtWord mtFiber76DirectStates 4 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0]
      (mtFiber76StateAt 11) (mtFiber76StateAt 43) (by decide) h3 (by decide)
      mtFiber76ReverseSingleStep43
  change mtFiber76StateAt 43 ∈ closeChainFiber mtWord mtFiber76DirectStates (4 + 60) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 4 60 [mtFiber76StateAt 0] (mtFiber76StateAt 43) h4

theorem mtFiber76State44_in_close :
    mtFiber76StateAt 44 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 8 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 8) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep8
  have h2 : mtFiber76StateAt 40 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 8) (mtFiber76StateAt 40) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep40
  have h3 : mtFiber76StateAt 44 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 40) (mtFiber76StateAt 44) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep44
  change mtFiber76StateAt 44 ∈ closeChainFiber mtWord mtFiber76DirectStates (3 + 61) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 3 61 [mtFiber76StateAt 0] (mtFiber76StateAt 44) h3

theorem mtFiber76State45_in_close :
    mtFiber76StateAt 45 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 1 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 1) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep1
  have h2 : mtFiber76StateAt 9 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 1) (mtFiber76StateAt 9) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep9
  have h3 : mtFiber76StateAt 41 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 9) (mtFiber76StateAt 41) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep41
  have h4 : mtFiber76StateAt 45 ∈ closeChainFiber mtWord mtFiber76DirectStates 4 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0]
      (mtFiber76StateAt 41) (mtFiber76StateAt 45) (by decide) h3 (by decide)
      mtFiber76ReverseSingleStep45
  change mtFiber76StateAt 45 ∈ closeChainFiber mtWord mtFiber76DirectStates (4 + 60) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 4 60 [mtFiber76StateAt 0] (mtFiber76StateAt 45) h4

theorem mtFiber76State46_in_close :
    mtFiber76StateAt 46 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 1 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 1) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep1
  have h2 : mtFiber76StateAt 6 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 1) (mtFiber76StateAt 6) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep6
  have h3 : mtFiber76StateAt 14 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 6) (mtFiber76StateAt 14) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep14
  have h4 : mtFiber76StateAt 46 ∈ closeChainFiber mtWord mtFiber76DirectStates 4 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0]
      (mtFiber76StateAt 14) (mtFiber76StateAt 46) (by decide) h3 (by decide)
      mtFiber76ReverseSingleStep46
  change mtFiber76StateAt 46 ∈ closeChainFiber mtWord mtFiber76DirectStates (4 + 60) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 4 60 [mtFiber76StateAt 0] (mtFiber76StateAt 46) h4

theorem mtFiber76State47_in_close :
    mtFiber76StateAt 47 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 7 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 7) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep7
  have h2 : mtFiber76StateAt 15 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 7) (mtFiber76StateAt 15) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep15
  have h3 : mtFiber76StateAt 47 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 15) (mtFiber76StateAt 47) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep47
  change mtFiber76StateAt 47 ∈ closeChainFiber mtWord mtFiber76DirectStates (3 + 61) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 3 61 [mtFiber76StateAt 0] (mtFiber76StateAt 47) h3

theorem mtFiber76State48_in_close :
    mtFiber76StateAt 48 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 32 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 32) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep32
  have h2 : mtFiber76StateAt 48 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 32) (mtFiber76StateAt 48) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep48
  change mtFiber76StateAt 48 ∈ closeChainFiber mtWord mtFiber76DirectStates (2 + 62) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 2 62 [mtFiber76StateAt 0] (mtFiber76StateAt 48) h2

theorem mtFiber76State49_in_close :
    mtFiber76StateAt 49 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 1 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 1) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep1
  have h2 : mtFiber76StateAt 33 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 1) (mtFiber76StateAt 33) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep33
  have h3 : mtFiber76StateAt 49 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 33) (mtFiber76StateAt 49) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep49
  change mtFiber76StateAt 49 ∈ closeChainFiber mtWord mtFiber76DirectStates (3 + 61) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 3 61 [mtFiber76StateAt 0] (mtFiber76StateAt 49) h3

theorem mtFiber76State50_in_close :
    mtFiber76StateAt 50 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 2 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 2) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep2
  have h2 : mtFiber76StateAt 34 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 2) (mtFiber76StateAt 34) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep34
  have h3 : mtFiber76StateAt 50 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 34) (mtFiber76StateAt 50) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep50
  change mtFiber76StateAt 50 ∈ closeChainFiber mtWord mtFiber76DirectStates (3 + 61) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 3 61 [mtFiber76StateAt 0] (mtFiber76StateAt 50) h3

theorem mtFiber76State51_in_close :
    mtFiber76StateAt 51 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 1 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 1) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep1
  have h2 : mtFiber76StateAt 3 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 1) (mtFiber76StateAt 3) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep3
  have h3 : mtFiber76StateAt 35 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 3) (mtFiber76StateAt 35) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep35
  have h4 : mtFiber76StateAt 51 ∈ closeChainFiber mtWord mtFiber76DirectStates 4 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0]
      (mtFiber76StateAt 35) (mtFiber76StateAt 51) (by decide) h3 (by decide)
      mtFiber76ReverseSingleStep51
  change mtFiber76StateAt 51 ∈ closeChainFiber mtWord mtFiber76DirectStates (4 + 60) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 4 60 [mtFiber76StateAt 0] (mtFiber76StateAt 51) h4

theorem mtFiber76State52_in_close :
    mtFiber76StateAt 52 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 32 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 32) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep32
  have h2 : mtFiber76StateAt 36 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 32) (mtFiber76StateAt 36) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep36
  have h3 : mtFiber76StateAt 52 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 36) (mtFiber76StateAt 52) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep52
  change mtFiber76StateAt 52 ∈ closeChainFiber mtWord mtFiber76DirectStates (3 + 61) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 3 61 [mtFiber76StateAt 0] (mtFiber76StateAt 52) h3

theorem mtFiber76State53_in_close :
    mtFiber76StateAt 53 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 1 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 1) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep1
  have h2 : mtFiber76StateAt 33 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 1) (mtFiber76StateAt 33) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep33
  have h3 : mtFiber76StateAt 37 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 33) (mtFiber76StateAt 37) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep37
  have h4 : mtFiber76StateAt 53 ∈ closeChainFiber mtWord mtFiber76DirectStates 4 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0]
      (mtFiber76StateAt 37) (mtFiber76StateAt 53) (by decide) h3 (by decide)
      mtFiber76ReverseSingleStep53
  change mtFiber76StateAt 53 ∈ closeChainFiber mtWord mtFiber76DirectStates (4 + 60) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 4 60 [mtFiber76StateAt 0] (mtFiber76StateAt 53) h4

theorem mtFiber76State54_in_close :
    mtFiber76StateAt 54 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 1 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 1) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep1
  have h2 : mtFiber76StateAt 6 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 1) (mtFiber76StateAt 6) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep6
  have h3 : mtFiber76StateAt 38 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 6) (mtFiber76StateAt 38) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep38
  have h4 : mtFiber76StateAt 54 ∈ closeChainFiber mtWord mtFiber76DirectStates 4 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0]
      (mtFiber76StateAt 38) (mtFiber76StateAt 54) (by decide) h3 (by decide)
      mtFiber76ReverseSingleStep54
  change mtFiber76StateAt 54 ∈ closeChainFiber mtWord mtFiber76DirectStates (4 + 60) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 4 60 [mtFiber76StateAt 0] (mtFiber76StateAt 54) h4

theorem mtFiber76State55_in_close :
    mtFiber76StateAt 55 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 7 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 7) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep7
  have h2 : mtFiber76StateAt 39 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 7) (mtFiber76StateAt 39) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep39
  have h3 : mtFiber76StateAt 55 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 39) (mtFiber76StateAt 55) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep55
  change mtFiber76StateAt 55 ∈ closeChainFiber mtWord mtFiber76DirectStates (3 + 61) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 3 61 [mtFiber76StateAt 0] (mtFiber76StateAt 55) h3

theorem mtFiber76State56_in_close :
    mtFiber76StateAt 56 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 24 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 24) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep24
  have h2 : mtFiber76StateAt 56 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 24) (mtFiber76StateAt 56) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep56
  change mtFiber76StateAt 56 ∈ closeChainFiber mtWord mtFiber76DirectStates (2 + 62) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 2 62 [mtFiber76StateAt 0] (mtFiber76StateAt 56) h2

theorem mtFiber76State57_in_close :
    mtFiber76StateAt 57 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 1 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 1) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep1
  have h2 : mtFiber76StateAt 25 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 1) (mtFiber76StateAt 25) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep25
  have h3 : mtFiber76StateAt 57 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 25) (mtFiber76StateAt 57) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep57
  change mtFiber76StateAt 57 ∈ closeChainFiber mtWord mtFiber76DirectStates (3 + 61) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 3 61 [mtFiber76StateAt 0] (mtFiber76StateAt 57) h3

theorem mtFiber76State58_in_close :
    mtFiber76StateAt 58 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 2 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 2) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep2
  have h2 : mtFiber76StateAt 26 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 2) (mtFiber76StateAt 26) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep26
  have h3 : mtFiber76StateAt 58 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 26) (mtFiber76StateAt 58) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep58
  change mtFiber76StateAt 58 ∈ closeChainFiber mtWord mtFiber76DirectStates (3 + 61) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 3 61 [mtFiber76StateAt 0] (mtFiber76StateAt 58) h3

theorem mtFiber76State59_in_close :
    mtFiber76StateAt 59 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 1 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 1) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep1
  have h2 : mtFiber76StateAt 3 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 1) (mtFiber76StateAt 3) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep3
  have h3 : mtFiber76StateAt 27 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 3) (mtFiber76StateAt 27) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep27
  have h4 : mtFiber76StateAt 59 ∈ closeChainFiber mtWord mtFiber76DirectStates 4 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0]
      (mtFiber76StateAt 27) (mtFiber76StateAt 59) (by decide) h3 (by decide)
      mtFiber76ReverseSingleStep59
  change mtFiber76StateAt 59 ∈ closeChainFiber mtWord mtFiber76DirectStates (4 + 60) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 4 60 [mtFiber76StateAt 0] (mtFiber76StateAt 59) h4

theorem mtFiber76State60_in_close :
    mtFiber76StateAt 60 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 24 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 24) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep24
  have h2 : mtFiber76StateAt 56 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 24) (mtFiber76StateAt 56) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep56
  have h3 : mtFiber76StateAt 60 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 56) (mtFiber76StateAt 60) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep60
  change mtFiber76StateAt 60 ∈ closeChainFiber mtWord mtFiber76DirectStates (3 + 61) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 3 61 [mtFiber76StateAt 0] (mtFiber76StateAt 60) h3

theorem mtFiber76State61_in_close :
    mtFiber76StateAt 61 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 1 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 1) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep1
  have h2 : mtFiber76StateAt 25 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 1) (mtFiber76StateAt 25) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep25
  have h3 : mtFiber76StateAt 57 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 25) (mtFiber76StateAt 57) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep57
  have h4 : mtFiber76StateAt 61 ∈ closeChainFiber mtWord mtFiber76DirectStates 4 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0]
      (mtFiber76StateAt 57) (mtFiber76StateAt 61) (by decide) h3 (by decide)
      mtFiber76ReverseSingleStep61
  change mtFiber76StateAt 61 ∈ closeChainFiber mtWord mtFiber76DirectStates (4 + 60) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 4 60 [mtFiber76StateAt 0] (mtFiber76StateAt 61) h4

theorem mtFiber76State62_in_close :
    mtFiber76StateAt 62 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 1 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 1) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep1
  have h2 : mtFiber76StateAt 6 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 1) (mtFiber76StateAt 6) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep6
  have h3 : mtFiber76StateAt 30 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 6) (mtFiber76StateAt 30) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep30
  have h4 : mtFiber76StateAt 62 ∈ closeChainFiber mtWord mtFiber76DirectStates 4 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0]
      (mtFiber76StateAt 30) (mtFiber76StateAt 62) (by decide) h3 (by decide)
      mtFiber76ReverseSingleStep62
  change mtFiber76StateAt 62 ∈ closeChainFiber mtWord mtFiber76DirectStates (4 + 60) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 4 60 [mtFiber76StateAt 0] (mtFiber76StateAt 62) h4

theorem mtFiber76State63_in_close :
    mtFiber76StateAt 63 ∈ closeChainFiber mtWord mtFiber76DirectStates mtFiber76DirectStates.length [mtFiber76StateAt 0] := by
  have h0 : mtFiber76StateAt 0 ∈ closeChainFiber mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber76StateAt 7 ∈ closeChainFiber mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 0 [mtFiber76StateAt 0]
      (mtFiber76StateAt 0) (mtFiber76StateAt 7) (by decide) h0 (by decide)
      mtFiber76ReverseSingleStep7
  have h2 : mtFiber76StateAt 31 ∈ closeChainFiber mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 1 [mtFiber76StateAt 0]
      (mtFiber76StateAt 7) (mtFiber76StateAt 31) (by decide) h1 (by decide)
      mtFiber76ReverseSingleStep31
  have h3 : mtFiber76StateAt 63 ∈ closeChainFiber mtWord mtFiber76DirectStates 3 [mtFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber76DirectStates 2 [mtFiber76StateAt 0]
      (mtFiber76StateAt 31) (mtFiber76StateAt 63) (by decide) h2 (by decide)
      mtFiber76ReverseSingleStep63
  change mtFiber76StateAt 63 ∈ closeChainFiber mtWord mtFiber76DirectStates (3 + 61) [mtFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber76DirectStates 3 61 [mtFiber76StateAt 0] (mtFiber76StateAt 63) h3

theorem mtFiber76DirectConnected :
    chainFiberConnected mtWord mtFiber76DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber76DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber76State0_in_close
  · subst state
    exact mtFiber76State1_in_close
  · subst state
    exact mtFiber76State2_in_close
  · subst state
    exact mtFiber76State3_in_close
  · subst state
    exact mtFiber76State4_in_close
  · subst state
    exact mtFiber76State5_in_close
  · subst state
    exact mtFiber76State6_in_close
  · subst state
    exact mtFiber76State7_in_close
  · subst state
    exact mtFiber76State8_in_close
  · subst state
    exact mtFiber76State9_in_close
  · subst state
    exact mtFiber76State10_in_close
  · subst state
    exact mtFiber76State11_in_close
  · subst state
    exact mtFiber76State12_in_close
  · subst state
    exact mtFiber76State13_in_close
  · subst state
    exact mtFiber76State14_in_close
  · subst state
    exact mtFiber76State15_in_close
  · subst state
    exact mtFiber76State16_in_close
  · subst state
    exact mtFiber76State17_in_close
  · subst state
    exact mtFiber76State18_in_close
  · subst state
    exact mtFiber76State19_in_close
  · subst state
    exact mtFiber76State20_in_close
  · subst state
    exact mtFiber76State21_in_close
  · subst state
    exact mtFiber76State22_in_close
  · subst state
    exact mtFiber76State23_in_close
  · subst state
    exact mtFiber76State24_in_close
  · subst state
    exact mtFiber76State25_in_close
  · subst state
    exact mtFiber76State26_in_close
  · subst state
    exact mtFiber76State27_in_close
  · subst state
    exact mtFiber76State28_in_close
  · subst state
    exact mtFiber76State29_in_close
  · subst state
    exact mtFiber76State30_in_close
  · subst state
    exact mtFiber76State31_in_close
  · subst state
    exact mtFiber76State32_in_close
  · subst state
    exact mtFiber76State33_in_close
  · subst state
    exact mtFiber76State34_in_close
  · subst state
    exact mtFiber76State35_in_close
  · subst state
    exact mtFiber76State36_in_close
  · subst state
    exact mtFiber76State37_in_close
  · subst state
    exact mtFiber76State38_in_close
  · subst state
    exact mtFiber76State39_in_close
  · subst state
    exact mtFiber76State40_in_close
  · subst state
    exact mtFiber76State41_in_close
  · subst state
    exact mtFiber76State42_in_close
  · subst state
    exact mtFiber76State43_in_close
  · subst state
    exact mtFiber76State44_in_close
  · subst state
    exact mtFiber76State45_in_close
  · subst state
    exact mtFiber76State46_in_close
  · subst state
    exact mtFiber76State47_in_close
  · subst state
    exact mtFiber76State48_in_close
  · subst state
    exact mtFiber76State49_in_close
  · subst state
    exact mtFiber76State50_in_close
  · subst state
    exact mtFiber76State51_in_close
  · subst state
    exact mtFiber76State52_in_close
  · subst state
    exact mtFiber76State53_in_close
  · subst state
    exact mtFiber76State54_in_close
  · subst state
    exact mtFiber76State55_in_close
  · subst state
    exact mtFiber76State56_in_close
  · subst state
    exact mtFiber76State57_in_close
  · subst state
    exact mtFiber76State58_in_close
  · subst state
    exact mtFiber76State59_in_close
  · subst state
    exact mtFiber76State60_in_close
  · subst state
    exact mtFiber76State61_in_close
  · subst state
    exact mtFiber76State62_in_close
  · subst state
    exact mtFiber76State63_in_close
  · cases h
end GoertzelLemma818LengthTwoMTBridge

end Mettapedia.GraphTheory.FourColor
