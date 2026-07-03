import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for `mirror,normal` size-64 fiber 70

This module proves direct connectedness for one generated size-64 fiber from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMTBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorTauCertificate
open GoertzelLemma818MirrorTauReverseAudit

def mtFiber70StateAt (i : Nat) : List TauState :=
  directStates (mtFiber70RowAt i).sourceLeft (mtFiber70RowAt i).sourceRight

def mtFiber70DirectStates : List (List TauState) :=
  [mtFiber70StateAt 0, mtFiber70StateAt 1, mtFiber70StateAt 2, mtFiber70StateAt 3, mtFiber70StateAt 4, mtFiber70StateAt 5, mtFiber70StateAt 6, mtFiber70StateAt 7, mtFiber70StateAt 8, mtFiber70StateAt 9, mtFiber70StateAt 10, mtFiber70StateAt 11, mtFiber70StateAt 12, mtFiber70StateAt 13, mtFiber70StateAt 14, mtFiber70StateAt 15, mtFiber70StateAt 16, mtFiber70StateAt 17, mtFiber70StateAt 18, mtFiber70StateAt 19, mtFiber70StateAt 20, mtFiber70StateAt 21, mtFiber70StateAt 22, mtFiber70StateAt 23, mtFiber70StateAt 24, mtFiber70StateAt 25, mtFiber70StateAt 26, mtFiber70StateAt 27, mtFiber70StateAt 28, mtFiber70StateAt 29, mtFiber70StateAt 30, mtFiber70StateAt 31, mtFiber70StateAt 32, mtFiber70StateAt 33, mtFiber70StateAt 34, mtFiber70StateAt 35, mtFiber70StateAt 36, mtFiber70StateAt 37, mtFiber70StateAt 38, mtFiber70StateAt 39, mtFiber70StateAt 40, mtFiber70StateAt 41, mtFiber70StateAt 42, mtFiber70StateAt 43, mtFiber70StateAt 44, mtFiber70StateAt 45, mtFiber70StateAt 46, mtFiber70StateAt 47, mtFiber70StateAt 48, mtFiber70StateAt 49, mtFiber70StateAt 50, mtFiber70StateAt 51, mtFiber70StateAt 52, mtFiber70StateAt 53, mtFiber70StateAt 54, mtFiber70StateAt 55, mtFiber70StateAt 56, mtFiber70StateAt 57, mtFiber70StateAt 58, mtFiber70StateAt 59, mtFiber70StateAt 60, mtFiber70StateAt 61, mtFiber70StateAt 62, mtFiber70StateAt 63]

theorem mtFiber70ReverseRow_1_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk0_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 0) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 0) (mtFiber70StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 0) (mtFiber70StateAt 1)
    (mtFiber70RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 1) (by decide) mtFiber70ReverseRow_1_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_2_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk1_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 2) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber70ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 0) (mtFiber70StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 0) (mtFiber70StateAt 2)
    (mtFiber70RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 2) (by decide) mtFiber70ReverseRow_2_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_3_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk1_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 2) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 1) (mtFiber70StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 1) (mtFiber70StateAt 3)
    (mtFiber70RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 3) (by decide) mtFiber70ReverseRow_3_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_4_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk2_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 4) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber70ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 2) (mtFiber70StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 2) (mtFiber70StateAt 4)
    (mtFiber70RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 4) (by decide) mtFiber70ReverseRow_4_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_5_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk2_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 4) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 7) (mtFiber70StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 7) (mtFiber70StateAt 5)
    (mtFiber70RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 5) (by decide) mtFiber70ReverseRow_5_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_6_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk3_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 6) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber70ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 1) (mtFiber70StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 1) (mtFiber70StateAt 6)
    (mtFiber70RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 6) (by decide) mtFiber70ReverseRow_6_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_7_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk3_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 6) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 0) (mtFiber70StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 0) (mtFiber70StateAt 7)
    (mtFiber70RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 7) (by decide) mtFiber70ReverseRow_7_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_8_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk4_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 8) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber70ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 0) (mtFiber70StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 0) (mtFiber70StateAt 8)
    (mtFiber70RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 8) (by decide) mtFiber70ReverseRow_8_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_9_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk4_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 8) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 1) (mtFiber70StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 1) (mtFiber70StateAt 9)
    (mtFiber70RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 9) (by decide) mtFiber70ReverseRow_9_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_10_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk5_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 10) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber70ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 2) (mtFiber70StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 2) (mtFiber70StateAt 10)
    (mtFiber70RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 10) (by decide) mtFiber70ReverseRow_10_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_11_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk5_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 10) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 3) (mtFiber70StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 3) (mtFiber70StateAt 11)
    (mtFiber70RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 11) (by decide) mtFiber70ReverseRow_11_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_12_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk6_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 12) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber70ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 4) (mtFiber70StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 4) (mtFiber70StateAt 12)
    (mtFiber70RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 12) (by decide) mtFiber70ReverseRow_12_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_13_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk6_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 12) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 5) (mtFiber70StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 5) (mtFiber70StateAt 13)
    (mtFiber70RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 13) (by decide) mtFiber70ReverseRow_13_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_14_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk7_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 14) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber70ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 6) (mtFiber70StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 6) (mtFiber70StateAt 14)
    (mtFiber70RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 14) (by decide) mtFiber70ReverseRow_14_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_15_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk7_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 14) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 7) (mtFiber70StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 7) (mtFiber70StateAt 15)
    (mtFiber70RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 15) (by decide) mtFiber70ReverseRow_15_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_16_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 16) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk8_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 16) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber70ReverseSingleStep16 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 8) (mtFiber70StateAt 16) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 8) (mtFiber70StateAt 16)
    (mtFiber70RowAt 16).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 16) (by decide) mtFiber70ReverseRow_16_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_17_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 17) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk8_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 16) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep17 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 9) (mtFiber70StateAt 17) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 9) (mtFiber70StateAt 17)
    (mtFiber70RowAt 17).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 17) (by decide) mtFiber70ReverseRow_17_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_18_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 18) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk9_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 18) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber70ReverseSingleStep18 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 10) (mtFiber70StateAt 18) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 10) (mtFiber70StateAt 18)
    (mtFiber70RowAt 18).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 18) (by decide) mtFiber70ReverseRow_18_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_19_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 19) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk9_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 18) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep19 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 11) (mtFiber70StateAt 19) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 11) (mtFiber70StateAt 19)
    (mtFiber70RowAt 19).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 19) (by decide) mtFiber70ReverseRow_19_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_20_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 20) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk10_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 20) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber70ReverseSingleStep20 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 12) (mtFiber70StateAt 20) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 12) (mtFiber70StateAt 20)
    (mtFiber70RowAt 20).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 20) (by decide) mtFiber70ReverseRow_20_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_21_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 21) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk10_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 20) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep21 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 13) (mtFiber70StateAt 21) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 13) (mtFiber70StateAt 21)
    (mtFiber70RowAt 21).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 21) (by decide) mtFiber70ReverseRow_21_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_22_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 22) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk11_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 22) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber70ReverseSingleStep22 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 14) (mtFiber70StateAt 22) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 14) (mtFiber70StateAt 22)
    (mtFiber70RowAt 22).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 22) (by decide) mtFiber70ReverseRow_22_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_23_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 23) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk11_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 22) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep23 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 15) (mtFiber70StateAt 23) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 15) (mtFiber70StateAt 23)
    (mtFiber70RowAt 23).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 23) (by decide) mtFiber70ReverseRow_23_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_24_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 24) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk12_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 24) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber70ReverseSingleStep24 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 0) (mtFiber70StateAt 24) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 0) (mtFiber70StateAt 24)
    (mtFiber70RowAt 24).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 24) (by decide) mtFiber70ReverseRow_24_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_25_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 25) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk12_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 24) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep25 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 1) (mtFiber70StateAt 25) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 1) (mtFiber70StateAt 25)
    (mtFiber70RowAt 25).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 25) (by decide) mtFiber70ReverseRow_25_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_26_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 26) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk13_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 26) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber70ReverseSingleStep26 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 2) (mtFiber70StateAt 26) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 2) (mtFiber70StateAt 26)
    (mtFiber70RowAt 26).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 26) (by decide) mtFiber70ReverseRow_26_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_27_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 27) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk13_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 26) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep27 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 3) (mtFiber70StateAt 27) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 3) (mtFiber70StateAt 27)
    (mtFiber70RowAt 27).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 27) (by decide) mtFiber70ReverseRow_27_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_28_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 28) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk14_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 28) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber70ReverseSingleStep28 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 4) (mtFiber70StateAt 28) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 4) (mtFiber70StateAt 28)
    (mtFiber70RowAt 28).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 28) (by decide) mtFiber70ReverseRow_28_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_29_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 29) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk14_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 28) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep29 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 5) (mtFiber70StateAt 29) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 5) (mtFiber70StateAt 29)
    (mtFiber70RowAt 29).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 29) (by decide) mtFiber70ReverseRow_29_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_30_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 30) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk15_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 30) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber70ReverseSingleStep30 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 6) (mtFiber70StateAt 30) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 6) (mtFiber70StateAt 30)
    (mtFiber70RowAt 30).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 30) (by decide) mtFiber70ReverseRow_30_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_31_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 31) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk15_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 30) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep31 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 7) (mtFiber70StateAt 31) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 7) (mtFiber70StateAt 31)
    (mtFiber70RowAt 31).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 31) (by decide) mtFiber70ReverseRow_31_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_32_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 32) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk16_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 32) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber70ReverseSingleStep32 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 0) (mtFiber70StateAt 32) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 0) (mtFiber70StateAt 32)
    (mtFiber70RowAt 32).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 32) (by decide) mtFiber70ReverseRow_32_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_33_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 33) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk16_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 32) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep33 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 1) (mtFiber70StateAt 33) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 1) (mtFiber70StateAt 33)
    (mtFiber70RowAt 33).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 33) (by decide) mtFiber70ReverseRow_33_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_34_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 34) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk17_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 34) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber70ReverseSingleStep34 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 2) (mtFiber70StateAt 34) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 2) (mtFiber70StateAt 34)
    (mtFiber70RowAt 34).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 34) (by decide) mtFiber70ReverseRow_34_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_35_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 35) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk17_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 34) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep35 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 3) (mtFiber70StateAt 35) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 3) (mtFiber70StateAt 35)
    (mtFiber70RowAt 35).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 35) (by decide) mtFiber70ReverseRow_35_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_36_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 36) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk18_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 36) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber70ReverseSingleStep36 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 32) (mtFiber70StateAt 36) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 32) (mtFiber70StateAt 36)
    (mtFiber70RowAt 36).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 36) (by decide) mtFiber70ReverseRow_36_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_37_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 37) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk18_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 36) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep37 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 33) (mtFiber70StateAt 37) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 33) (mtFiber70StateAt 37)
    (mtFiber70RowAt 37).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 37) (by decide) mtFiber70ReverseRow_37_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_38_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 38) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk19_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 38) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber70ReverseSingleStep38 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 6) (mtFiber70StateAt 38) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 6) (mtFiber70StateAt 38)
    (mtFiber70RowAt 38).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 38) (by decide) mtFiber70ReverseRow_38_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_39_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 39) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk19_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 38) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep39 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 7) (mtFiber70StateAt 39) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 7) (mtFiber70StateAt 39)
    (mtFiber70RowAt 39).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 39) (by decide) mtFiber70ReverseRow_39_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_40_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 40) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk20_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 40) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber70ReverseSingleStep40 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 8) (mtFiber70StateAt 40) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 8) (mtFiber70StateAt 40)
    (mtFiber70RowAt 40).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 40) (by decide) mtFiber70ReverseRow_40_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_41_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 41) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk20_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 40) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep41 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 9) (mtFiber70StateAt 41) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 9) (mtFiber70StateAt 41)
    (mtFiber70RowAt 41).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 41) (by decide) mtFiber70ReverseRow_41_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_42_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 42) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk21_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 42) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber70ReverseSingleStep42 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 10) (mtFiber70StateAt 42) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 10) (mtFiber70StateAt 42)
    (mtFiber70RowAt 42).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 42) (by decide) mtFiber70ReverseRow_42_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_43_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 43) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk21_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 42) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep43 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 11) (mtFiber70StateAt 43) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 11) (mtFiber70StateAt 43)
    (mtFiber70RowAt 43).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 43) (by decide) mtFiber70ReverseRow_43_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_44_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 44) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk22_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 44) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber70ReverseSingleStep44 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 40) (mtFiber70StateAt 44) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 40) (mtFiber70StateAt 44)
    (mtFiber70RowAt 44).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 44) (by decide) mtFiber70ReverseRow_44_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_45_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 45) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk22_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 44) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep45 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 41) (mtFiber70StateAt 45) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 41) (mtFiber70StateAt 45)
    (mtFiber70RowAt 45).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 45) (by decide) mtFiber70ReverseRow_45_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_46_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 46) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk23_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 46) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber70ReverseSingleStep46 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 14) (mtFiber70StateAt 46) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 14) (mtFiber70StateAt 46)
    (mtFiber70RowAt 46).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 46) (by decide) mtFiber70ReverseRow_46_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_47_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 47) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk23_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 46) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep47 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 15) (mtFiber70StateAt 47) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 15) (mtFiber70StateAt 47)
    (mtFiber70RowAt 47).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 47) (by decide) mtFiber70ReverseRow_47_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_48_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 48) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk24_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 48) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber70ReverseSingleStep48 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 32) (mtFiber70StateAt 48) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 32) (mtFiber70StateAt 48)
    (mtFiber70RowAt 48).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 48) (by decide) mtFiber70ReverseRow_48_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_49_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 49) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk24_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 48) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep49 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 33) (mtFiber70StateAt 49) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 33) (mtFiber70StateAt 49)
    (mtFiber70RowAt 49).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 49) (by decide) mtFiber70ReverseRow_49_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_50_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 50) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk25_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 50) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber70ReverseSingleStep50 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 34) (mtFiber70StateAt 50) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 34) (mtFiber70StateAt 50)
    (mtFiber70RowAt 50).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 50) (by decide) mtFiber70ReverseRow_50_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_51_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 51) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk25_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 50) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep51 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 35) (mtFiber70StateAt 51) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 35) (mtFiber70StateAt 51)
    (mtFiber70RowAt 51).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 51) (by decide) mtFiber70ReverseRow_51_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_52_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 52) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk26_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 52) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber70ReverseSingleStep52 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 36) (mtFiber70StateAt 52) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 36) (mtFiber70StateAt 52)
    (mtFiber70RowAt 52).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 52) (by decide) mtFiber70ReverseRow_52_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_53_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 53) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk26_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 52) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep53 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 37) (mtFiber70StateAt 53) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 37) (mtFiber70StateAt 53)
    (mtFiber70RowAt 53).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 53) (by decide) mtFiber70ReverseRow_53_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_54_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 54) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk27_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 54) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber70ReverseSingleStep54 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 38) (mtFiber70StateAt 54) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 38) (mtFiber70StateAt 54)
    (mtFiber70RowAt 54).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 54) (by decide) mtFiber70ReverseRow_54_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_55_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 55) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk27_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 54) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep55 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 39) (mtFiber70StateAt 55) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 39) (mtFiber70StateAt 55)
    (mtFiber70RowAt 55).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 55) (by decide) mtFiber70ReverseRow_55_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_56_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 56) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk28_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 56) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber70ReverseSingleStep56 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 24) (mtFiber70StateAt 56) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 24) (mtFiber70StateAt 56)
    (mtFiber70RowAt 56).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 56) (by decide) mtFiber70ReverseRow_56_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_57_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 57) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk28_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 56) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep57 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 25) (mtFiber70StateAt 57) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 25) (mtFiber70StateAt 57)
    (mtFiber70RowAt 57).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 57) (by decide) mtFiber70ReverseRow_57_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_58_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 58) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk29_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 58) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber70ReverseSingleStep58 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 26) (mtFiber70StateAt 58) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 26) (mtFiber70StateAt 58)
    (mtFiber70RowAt 58).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 58) (by decide) mtFiber70ReverseRow_58_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_59_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 59) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk29_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 58) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep59 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 27) (mtFiber70StateAt 59) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 27) (mtFiber70StateAt 59)
    (mtFiber70RowAt 59).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 59) (by decide) mtFiber70ReverseRow_59_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_60_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 60) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk30_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 60) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber70ReverseSingleStep60 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 56) (mtFiber70StateAt 60) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 56) (mtFiber70StateAt 60)
    (mtFiber70RowAt 60).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 60) (by decide) mtFiber70ReverseRow_60_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_61_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 61) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk30_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 60) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep61 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 57) (mtFiber70StateAt 61) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 57) (mtFiber70StateAt 61)
    (mtFiber70RowAt 61).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 61) (by decide) mtFiber70ReverseRow_61_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_62_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 62) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk31_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 62) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber70ReverseSingleStep62 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 30) (mtFiber70StateAt 62) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 30) (mtFiber70StateAt 62)
    (mtFiber70RowAt 62).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 62) (by decide) mtFiber70ReverseRow_62_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70ReverseRow_63_ok :
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 63) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber70Chunk31_ok
  change (mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 62) &&
    mtRowReverseValid mtFiber70Key mtFiber70Expected (mtFiber70RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber70ReverseSingleStep63 :
    chainSingleKempeStep mtWord (mtFiber70StateAt 31) (mtFiber70StateAt 63) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber70StateAt 31) (mtFiber70StateAt 63)
    (mtFiber70RowAt 63).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber70Key mtFiber70Expected
        (mtFiber70RowAt 63) (by decide) mtFiber70ReverseRow_63_ok
      simpa [mtFiber70StateAt, mtFiber70RowAt, mtFiber70Rows, listGetD, directRow] using h)

theorem mtFiber70State0_in_close :
    mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  change mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 64 [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 0 64 [mtFiber70StateAt 0] (mtFiber70StateAt 0) (by simp [closeChainFiber])

theorem mtFiber70State1_in_close :
    mtFiber70StateAt 1 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 1 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 1) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep1
  change mtFiber70StateAt 1 ∈ closeChainFiber mtWord mtFiber70DirectStates (1 + 63) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 1 63 [mtFiber70StateAt 0] (mtFiber70StateAt 1) h1

theorem mtFiber70State2_in_close :
    mtFiber70StateAt 2 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 2 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 2) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep2
  change mtFiber70StateAt 2 ∈ closeChainFiber mtWord mtFiber70DirectStates (1 + 63) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 1 63 [mtFiber70StateAt 0] (mtFiber70StateAt 2) h1

theorem mtFiber70State3_in_close :
    mtFiber70StateAt 3 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 1 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 1) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep1
  have h2 : mtFiber70StateAt 3 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 1) (mtFiber70StateAt 3) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep3
  change mtFiber70StateAt 3 ∈ closeChainFiber mtWord mtFiber70DirectStates (2 + 62) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 2 62 [mtFiber70StateAt 0] (mtFiber70StateAt 3) h2

theorem mtFiber70State4_in_close :
    mtFiber70StateAt 4 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 2 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 2) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep2
  have h2 : mtFiber70StateAt 4 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 2) (mtFiber70StateAt 4) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep4
  change mtFiber70StateAt 4 ∈ closeChainFiber mtWord mtFiber70DirectStates (2 + 62) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 2 62 [mtFiber70StateAt 0] (mtFiber70StateAt 4) h2

theorem mtFiber70State5_in_close :
    mtFiber70StateAt 5 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 7 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 7) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep7
  have h2 : mtFiber70StateAt 5 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 7) (mtFiber70StateAt 5) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep5
  change mtFiber70StateAt 5 ∈ closeChainFiber mtWord mtFiber70DirectStates (2 + 62) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 2 62 [mtFiber70StateAt 0] (mtFiber70StateAt 5) h2

theorem mtFiber70State6_in_close :
    mtFiber70StateAt 6 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 1 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 1) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep1
  have h2 : mtFiber70StateAt 6 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 1) (mtFiber70StateAt 6) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep6
  change mtFiber70StateAt 6 ∈ closeChainFiber mtWord mtFiber70DirectStates (2 + 62) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 2 62 [mtFiber70StateAt 0] (mtFiber70StateAt 6) h2

theorem mtFiber70State7_in_close :
    mtFiber70StateAt 7 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 7 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 7) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep7
  change mtFiber70StateAt 7 ∈ closeChainFiber mtWord mtFiber70DirectStates (1 + 63) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 1 63 [mtFiber70StateAt 0] (mtFiber70StateAt 7) h1

theorem mtFiber70State8_in_close :
    mtFiber70StateAt 8 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 8 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 8) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep8
  change mtFiber70StateAt 8 ∈ closeChainFiber mtWord mtFiber70DirectStates (1 + 63) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 1 63 [mtFiber70StateAt 0] (mtFiber70StateAt 8) h1

theorem mtFiber70State9_in_close :
    mtFiber70StateAt 9 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 1 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 1) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep1
  have h2 : mtFiber70StateAt 9 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 1) (mtFiber70StateAt 9) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep9
  change mtFiber70StateAt 9 ∈ closeChainFiber mtWord mtFiber70DirectStates (2 + 62) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 2 62 [mtFiber70StateAt 0] (mtFiber70StateAt 9) h2

theorem mtFiber70State10_in_close :
    mtFiber70StateAt 10 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 2 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 2) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep2
  have h2 : mtFiber70StateAt 10 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 2) (mtFiber70StateAt 10) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep10
  change mtFiber70StateAt 10 ∈ closeChainFiber mtWord mtFiber70DirectStates (2 + 62) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 2 62 [mtFiber70StateAt 0] (mtFiber70StateAt 10) h2

theorem mtFiber70State11_in_close :
    mtFiber70StateAt 11 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 1 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 1) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep1
  have h2 : mtFiber70StateAt 3 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 1) (mtFiber70StateAt 3) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep3
  have h3 : mtFiber70StateAt 11 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 3) (mtFiber70StateAt 11) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep11
  change mtFiber70StateAt 11 ∈ closeChainFiber mtWord mtFiber70DirectStates (3 + 61) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 3 61 [mtFiber70StateAt 0] (mtFiber70StateAt 11) h3

theorem mtFiber70State12_in_close :
    mtFiber70StateAt 12 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 2 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 2) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep2
  have h2 : mtFiber70StateAt 4 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 2) (mtFiber70StateAt 4) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep4
  have h3 : mtFiber70StateAt 12 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 4) (mtFiber70StateAt 12) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep12
  change mtFiber70StateAt 12 ∈ closeChainFiber mtWord mtFiber70DirectStates (3 + 61) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 3 61 [mtFiber70StateAt 0] (mtFiber70StateAt 12) h3

theorem mtFiber70State13_in_close :
    mtFiber70StateAt 13 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 7 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 7) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep7
  have h2 : mtFiber70StateAt 5 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 7) (mtFiber70StateAt 5) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep5
  have h3 : mtFiber70StateAt 13 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 5) (mtFiber70StateAt 13) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep13
  change mtFiber70StateAt 13 ∈ closeChainFiber mtWord mtFiber70DirectStates (3 + 61) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 3 61 [mtFiber70StateAt 0] (mtFiber70StateAt 13) h3

theorem mtFiber70State14_in_close :
    mtFiber70StateAt 14 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 1 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 1) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep1
  have h2 : mtFiber70StateAt 6 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 1) (mtFiber70StateAt 6) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep6
  have h3 : mtFiber70StateAt 14 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 6) (mtFiber70StateAt 14) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep14
  change mtFiber70StateAt 14 ∈ closeChainFiber mtWord mtFiber70DirectStates (3 + 61) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 3 61 [mtFiber70StateAt 0] (mtFiber70StateAt 14) h3

theorem mtFiber70State15_in_close :
    mtFiber70StateAt 15 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 7 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 7) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep7
  have h2 : mtFiber70StateAt 15 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 7) (mtFiber70StateAt 15) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep15
  change mtFiber70StateAt 15 ∈ closeChainFiber mtWord mtFiber70DirectStates (2 + 62) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 2 62 [mtFiber70StateAt 0] (mtFiber70StateAt 15) h2

theorem mtFiber70State16_in_close :
    mtFiber70StateAt 16 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 8 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 8) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep8
  have h2 : mtFiber70StateAt 16 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 8) (mtFiber70StateAt 16) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep16
  change mtFiber70StateAt 16 ∈ closeChainFiber mtWord mtFiber70DirectStates (2 + 62) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 2 62 [mtFiber70StateAt 0] (mtFiber70StateAt 16) h2

theorem mtFiber70State17_in_close :
    mtFiber70StateAt 17 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 1 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 1) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep1
  have h2 : mtFiber70StateAt 9 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 1) (mtFiber70StateAt 9) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep9
  have h3 : mtFiber70StateAt 17 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 9) (mtFiber70StateAt 17) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep17
  change mtFiber70StateAt 17 ∈ closeChainFiber mtWord mtFiber70DirectStates (3 + 61) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 3 61 [mtFiber70StateAt 0] (mtFiber70StateAt 17) h3

theorem mtFiber70State18_in_close :
    mtFiber70StateAt 18 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 2 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 2) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep2
  have h2 : mtFiber70StateAt 10 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 2) (mtFiber70StateAt 10) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep10
  have h3 : mtFiber70StateAt 18 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 10) (mtFiber70StateAt 18) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep18
  change mtFiber70StateAt 18 ∈ closeChainFiber mtWord mtFiber70DirectStates (3 + 61) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 3 61 [mtFiber70StateAt 0] (mtFiber70StateAt 18) h3

theorem mtFiber70State19_in_close :
    mtFiber70StateAt 19 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 1 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 1) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep1
  have h2 : mtFiber70StateAt 3 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 1) (mtFiber70StateAt 3) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep3
  have h3 : mtFiber70StateAt 11 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 3) (mtFiber70StateAt 11) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep11
  have h4 : mtFiber70StateAt 19 ∈ closeChainFiber mtWord mtFiber70DirectStates 4 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0]
      (mtFiber70StateAt 11) (mtFiber70StateAt 19) (by decide) h3 (by decide)
      mtFiber70ReverseSingleStep19
  change mtFiber70StateAt 19 ∈ closeChainFiber mtWord mtFiber70DirectStates (4 + 60) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 4 60 [mtFiber70StateAt 0] (mtFiber70StateAt 19) h4

theorem mtFiber70State20_in_close :
    mtFiber70StateAt 20 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 2 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 2) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep2
  have h2 : mtFiber70StateAt 4 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 2) (mtFiber70StateAt 4) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep4
  have h3 : mtFiber70StateAt 12 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 4) (mtFiber70StateAt 12) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep12
  have h4 : mtFiber70StateAt 20 ∈ closeChainFiber mtWord mtFiber70DirectStates 4 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0]
      (mtFiber70StateAt 12) (mtFiber70StateAt 20) (by decide) h3 (by decide)
      mtFiber70ReverseSingleStep20
  change mtFiber70StateAt 20 ∈ closeChainFiber mtWord mtFiber70DirectStates (4 + 60) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 4 60 [mtFiber70StateAt 0] (mtFiber70StateAt 20) h4

theorem mtFiber70State21_in_close :
    mtFiber70StateAt 21 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 7 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 7) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep7
  have h2 : mtFiber70StateAt 5 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 7) (mtFiber70StateAt 5) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep5
  have h3 : mtFiber70StateAt 13 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 5) (mtFiber70StateAt 13) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep13
  have h4 : mtFiber70StateAt 21 ∈ closeChainFiber mtWord mtFiber70DirectStates 4 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0]
      (mtFiber70StateAt 13) (mtFiber70StateAt 21) (by decide) h3 (by decide)
      mtFiber70ReverseSingleStep21
  change mtFiber70StateAt 21 ∈ closeChainFiber mtWord mtFiber70DirectStates (4 + 60) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 4 60 [mtFiber70StateAt 0] (mtFiber70StateAt 21) h4

theorem mtFiber70State22_in_close :
    mtFiber70StateAt 22 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 1 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 1) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep1
  have h2 : mtFiber70StateAt 6 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 1) (mtFiber70StateAt 6) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep6
  have h3 : mtFiber70StateAt 14 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 6) (mtFiber70StateAt 14) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep14
  have h4 : mtFiber70StateAt 22 ∈ closeChainFiber mtWord mtFiber70DirectStates 4 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0]
      (mtFiber70StateAt 14) (mtFiber70StateAt 22) (by decide) h3 (by decide)
      mtFiber70ReverseSingleStep22
  change mtFiber70StateAt 22 ∈ closeChainFiber mtWord mtFiber70DirectStates (4 + 60) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 4 60 [mtFiber70StateAt 0] (mtFiber70StateAt 22) h4

theorem mtFiber70State23_in_close :
    mtFiber70StateAt 23 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 7 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 7) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep7
  have h2 : mtFiber70StateAt 15 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 7) (mtFiber70StateAt 15) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep15
  have h3 : mtFiber70StateAt 23 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 15) (mtFiber70StateAt 23) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep23
  change mtFiber70StateAt 23 ∈ closeChainFiber mtWord mtFiber70DirectStates (3 + 61) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 3 61 [mtFiber70StateAt 0] (mtFiber70StateAt 23) h3

theorem mtFiber70State24_in_close :
    mtFiber70StateAt 24 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 24 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 24) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep24
  change mtFiber70StateAt 24 ∈ closeChainFiber mtWord mtFiber70DirectStates (1 + 63) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 1 63 [mtFiber70StateAt 0] (mtFiber70StateAt 24) h1

theorem mtFiber70State25_in_close :
    mtFiber70StateAt 25 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 1 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 1) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep1
  have h2 : mtFiber70StateAt 25 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 1) (mtFiber70StateAt 25) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep25
  change mtFiber70StateAt 25 ∈ closeChainFiber mtWord mtFiber70DirectStates (2 + 62) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 2 62 [mtFiber70StateAt 0] (mtFiber70StateAt 25) h2

theorem mtFiber70State26_in_close :
    mtFiber70StateAt 26 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 2 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 2) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep2
  have h2 : mtFiber70StateAt 26 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 2) (mtFiber70StateAt 26) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep26
  change mtFiber70StateAt 26 ∈ closeChainFiber mtWord mtFiber70DirectStates (2 + 62) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 2 62 [mtFiber70StateAt 0] (mtFiber70StateAt 26) h2

theorem mtFiber70State27_in_close :
    mtFiber70StateAt 27 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 1 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 1) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep1
  have h2 : mtFiber70StateAt 3 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 1) (mtFiber70StateAt 3) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep3
  have h3 : mtFiber70StateAt 27 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 3) (mtFiber70StateAt 27) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep27
  change mtFiber70StateAt 27 ∈ closeChainFiber mtWord mtFiber70DirectStates (3 + 61) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 3 61 [mtFiber70StateAt 0] (mtFiber70StateAt 27) h3

theorem mtFiber70State28_in_close :
    mtFiber70StateAt 28 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 2 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 2) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep2
  have h2 : mtFiber70StateAt 4 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 2) (mtFiber70StateAt 4) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep4
  have h3 : mtFiber70StateAt 28 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 4) (mtFiber70StateAt 28) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep28
  change mtFiber70StateAt 28 ∈ closeChainFiber mtWord mtFiber70DirectStates (3 + 61) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 3 61 [mtFiber70StateAt 0] (mtFiber70StateAt 28) h3

theorem mtFiber70State29_in_close :
    mtFiber70StateAt 29 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 7 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 7) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep7
  have h2 : mtFiber70StateAt 5 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 7) (mtFiber70StateAt 5) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep5
  have h3 : mtFiber70StateAt 29 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 5) (mtFiber70StateAt 29) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep29
  change mtFiber70StateAt 29 ∈ closeChainFiber mtWord mtFiber70DirectStates (3 + 61) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 3 61 [mtFiber70StateAt 0] (mtFiber70StateAt 29) h3

theorem mtFiber70State30_in_close :
    mtFiber70StateAt 30 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 1 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 1) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep1
  have h2 : mtFiber70StateAt 6 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 1) (mtFiber70StateAt 6) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep6
  have h3 : mtFiber70StateAt 30 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 6) (mtFiber70StateAt 30) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep30
  change mtFiber70StateAt 30 ∈ closeChainFiber mtWord mtFiber70DirectStates (3 + 61) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 3 61 [mtFiber70StateAt 0] (mtFiber70StateAt 30) h3

theorem mtFiber70State31_in_close :
    mtFiber70StateAt 31 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 7 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 7) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep7
  have h2 : mtFiber70StateAt 31 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 7) (mtFiber70StateAt 31) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep31
  change mtFiber70StateAt 31 ∈ closeChainFiber mtWord mtFiber70DirectStates (2 + 62) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 2 62 [mtFiber70StateAt 0] (mtFiber70StateAt 31) h2

theorem mtFiber70State32_in_close :
    mtFiber70StateAt 32 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 32 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 32) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep32
  change mtFiber70StateAt 32 ∈ closeChainFiber mtWord mtFiber70DirectStates (1 + 63) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 1 63 [mtFiber70StateAt 0] (mtFiber70StateAt 32) h1

theorem mtFiber70State33_in_close :
    mtFiber70StateAt 33 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 1 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 1) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep1
  have h2 : mtFiber70StateAt 33 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 1) (mtFiber70StateAt 33) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep33
  change mtFiber70StateAt 33 ∈ closeChainFiber mtWord mtFiber70DirectStates (2 + 62) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 2 62 [mtFiber70StateAt 0] (mtFiber70StateAt 33) h2

theorem mtFiber70State34_in_close :
    mtFiber70StateAt 34 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 2 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 2) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep2
  have h2 : mtFiber70StateAt 34 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 2) (mtFiber70StateAt 34) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep34
  change mtFiber70StateAt 34 ∈ closeChainFiber mtWord mtFiber70DirectStates (2 + 62) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 2 62 [mtFiber70StateAt 0] (mtFiber70StateAt 34) h2

theorem mtFiber70State35_in_close :
    mtFiber70StateAt 35 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 1 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 1) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep1
  have h2 : mtFiber70StateAt 3 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 1) (mtFiber70StateAt 3) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep3
  have h3 : mtFiber70StateAt 35 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 3) (mtFiber70StateAt 35) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep35
  change mtFiber70StateAt 35 ∈ closeChainFiber mtWord mtFiber70DirectStates (3 + 61) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 3 61 [mtFiber70StateAt 0] (mtFiber70StateAt 35) h3

theorem mtFiber70State36_in_close :
    mtFiber70StateAt 36 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 32 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 32) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep32
  have h2 : mtFiber70StateAt 36 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 32) (mtFiber70StateAt 36) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep36
  change mtFiber70StateAt 36 ∈ closeChainFiber mtWord mtFiber70DirectStates (2 + 62) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 2 62 [mtFiber70StateAt 0] (mtFiber70StateAt 36) h2

theorem mtFiber70State37_in_close :
    mtFiber70StateAt 37 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 1 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 1) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep1
  have h2 : mtFiber70StateAt 33 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 1) (mtFiber70StateAt 33) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep33
  have h3 : mtFiber70StateAt 37 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 33) (mtFiber70StateAt 37) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep37
  change mtFiber70StateAt 37 ∈ closeChainFiber mtWord mtFiber70DirectStates (3 + 61) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 3 61 [mtFiber70StateAt 0] (mtFiber70StateAt 37) h3

theorem mtFiber70State38_in_close :
    mtFiber70StateAt 38 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 1 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 1) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep1
  have h2 : mtFiber70StateAt 6 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 1) (mtFiber70StateAt 6) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep6
  have h3 : mtFiber70StateAt 38 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 6) (mtFiber70StateAt 38) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep38
  change mtFiber70StateAt 38 ∈ closeChainFiber mtWord mtFiber70DirectStates (3 + 61) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 3 61 [mtFiber70StateAt 0] (mtFiber70StateAt 38) h3

theorem mtFiber70State39_in_close :
    mtFiber70StateAt 39 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 7 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 7) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep7
  have h2 : mtFiber70StateAt 39 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 7) (mtFiber70StateAt 39) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep39
  change mtFiber70StateAt 39 ∈ closeChainFiber mtWord mtFiber70DirectStates (2 + 62) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 2 62 [mtFiber70StateAt 0] (mtFiber70StateAt 39) h2

theorem mtFiber70State40_in_close :
    mtFiber70StateAt 40 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 8 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 8) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep8
  have h2 : mtFiber70StateAt 40 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 8) (mtFiber70StateAt 40) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep40
  change mtFiber70StateAt 40 ∈ closeChainFiber mtWord mtFiber70DirectStates (2 + 62) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 2 62 [mtFiber70StateAt 0] (mtFiber70StateAt 40) h2

theorem mtFiber70State41_in_close :
    mtFiber70StateAt 41 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 1 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 1) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep1
  have h2 : mtFiber70StateAt 9 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 1) (mtFiber70StateAt 9) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep9
  have h3 : mtFiber70StateAt 41 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 9) (mtFiber70StateAt 41) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep41
  change mtFiber70StateAt 41 ∈ closeChainFiber mtWord mtFiber70DirectStates (3 + 61) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 3 61 [mtFiber70StateAt 0] (mtFiber70StateAt 41) h3

theorem mtFiber70State42_in_close :
    mtFiber70StateAt 42 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 2 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 2) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep2
  have h2 : mtFiber70StateAt 10 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 2) (mtFiber70StateAt 10) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep10
  have h3 : mtFiber70StateAt 42 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 10) (mtFiber70StateAt 42) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep42
  change mtFiber70StateAt 42 ∈ closeChainFiber mtWord mtFiber70DirectStates (3 + 61) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 3 61 [mtFiber70StateAt 0] (mtFiber70StateAt 42) h3

theorem mtFiber70State43_in_close :
    mtFiber70StateAt 43 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 1 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 1) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep1
  have h2 : mtFiber70StateAt 3 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 1) (mtFiber70StateAt 3) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep3
  have h3 : mtFiber70StateAt 11 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 3) (mtFiber70StateAt 11) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep11
  have h4 : mtFiber70StateAt 43 ∈ closeChainFiber mtWord mtFiber70DirectStates 4 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0]
      (mtFiber70StateAt 11) (mtFiber70StateAt 43) (by decide) h3 (by decide)
      mtFiber70ReverseSingleStep43
  change mtFiber70StateAt 43 ∈ closeChainFiber mtWord mtFiber70DirectStates (4 + 60) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 4 60 [mtFiber70StateAt 0] (mtFiber70StateAt 43) h4

theorem mtFiber70State44_in_close :
    mtFiber70StateAt 44 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 8 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 8) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep8
  have h2 : mtFiber70StateAt 40 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 8) (mtFiber70StateAt 40) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep40
  have h3 : mtFiber70StateAt 44 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 40) (mtFiber70StateAt 44) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep44
  change mtFiber70StateAt 44 ∈ closeChainFiber mtWord mtFiber70DirectStates (3 + 61) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 3 61 [mtFiber70StateAt 0] (mtFiber70StateAt 44) h3

theorem mtFiber70State45_in_close :
    mtFiber70StateAt 45 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 1 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 1) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep1
  have h2 : mtFiber70StateAt 9 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 1) (mtFiber70StateAt 9) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep9
  have h3 : mtFiber70StateAt 41 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 9) (mtFiber70StateAt 41) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep41
  have h4 : mtFiber70StateAt 45 ∈ closeChainFiber mtWord mtFiber70DirectStates 4 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0]
      (mtFiber70StateAt 41) (mtFiber70StateAt 45) (by decide) h3 (by decide)
      mtFiber70ReverseSingleStep45
  change mtFiber70StateAt 45 ∈ closeChainFiber mtWord mtFiber70DirectStates (4 + 60) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 4 60 [mtFiber70StateAt 0] (mtFiber70StateAt 45) h4

theorem mtFiber70State46_in_close :
    mtFiber70StateAt 46 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 1 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 1) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep1
  have h2 : mtFiber70StateAt 6 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 1) (mtFiber70StateAt 6) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep6
  have h3 : mtFiber70StateAt 14 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 6) (mtFiber70StateAt 14) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep14
  have h4 : mtFiber70StateAt 46 ∈ closeChainFiber mtWord mtFiber70DirectStates 4 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0]
      (mtFiber70StateAt 14) (mtFiber70StateAt 46) (by decide) h3 (by decide)
      mtFiber70ReverseSingleStep46
  change mtFiber70StateAt 46 ∈ closeChainFiber mtWord mtFiber70DirectStates (4 + 60) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 4 60 [mtFiber70StateAt 0] (mtFiber70StateAt 46) h4

theorem mtFiber70State47_in_close :
    mtFiber70StateAt 47 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 7 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 7) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep7
  have h2 : mtFiber70StateAt 15 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 7) (mtFiber70StateAt 15) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep15
  have h3 : mtFiber70StateAt 47 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 15) (mtFiber70StateAt 47) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep47
  change mtFiber70StateAt 47 ∈ closeChainFiber mtWord mtFiber70DirectStates (3 + 61) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 3 61 [mtFiber70StateAt 0] (mtFiber70StateAt 47) h3

theorem mtFiber70State48_in_close :
    mtFiber70StateAt 48 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 32 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 32) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep32
  have h2 : mtFiber70StateAt 48 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 32) (mtFiber70StateAt 48) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep48
  change mtFiber70StateAt 48 ∈ closeChainFiber mtWord mtFiber70DirectStates (2 + 62) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 2 62 [mtFiber70StateAt 0] (mtFiber70StateAt 48) h2

theorem mtFiber70State49_in_close :
    mtFiber70StateAt 49 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 1 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 1) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep1
  have h2 : mtFiber70StateAt 33 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 1) (mtFiber70StateAt 33) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep33
  have h3 : mtFiber70StateAt 49 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 33) (mtFiber70StateAt 49) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep49
  change mtFiber70StateAt 49 ∈ closeChainFiber mtWord mtFiber70DirectStates (3 + 61) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 3 61 [mtFiber70StateAt 0] (mtFiber70StateAt 49) h3

theorem mtFiber70State50_in_close :
    mtFiber70StateAt 50 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 2 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 2) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep2
  have h2 : mtFiber70StateAt 34 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 2) (mtFiber70StateAt 34) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep34
  have h3 : mtFiber70StateAt 50 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 34) (mtFiber70StateAt 50) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep50
  change mtFiber70StateAt 50 ∈ closeChainFiber mtWord mtFiber70DirectStates (3 + 61) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 3 61 [mtFiber70StateAt 0] (mtFiber70StateAt 50) h3

theorem mtFiber70State51_in_close :
    mtFiber70StateAt 51 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 1 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 1) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep1
  have h2 : mtFiber70StateAt 3 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 1) (mtFiber70StateAt 3) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep3
  have h3 : mtFiber70StateAt 35 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 3) (mtFiber70StateAt 35) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep35
  have h4 : mtFiber70StateAt 51 ∈ closeChainFiber mtWord mtFiber70DirectStates 4 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0]
      (mtFiber70StateAt 35) (mtFiber70StateAt 51) (by decide) h3 (by decide)
      mtFiber70ReverseSingleStep51
  change mtFiber70StateAt 51 ∈ closeChainFiber mtWord mtFiber70DirectStates (4 + 60) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 4 60 [mtFiber70StateAt 0] (mtFiber70StateAt 51) h4

theorem mtFiber70State52_in_close :
    mtFiber70StateAt 52 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 32 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 32) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep32
  have h2 : mtFiber70StateAt 36 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 32) (mtFiber70StateAt 36) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep36
  have h3 : mtFiber70StateAt 52 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 36) (mtFiber70StateAt 52) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep52
  change mtFiber70StateAt 52 ∈ closeChainFiber mtWord mtFiber70DirectStates (3 + 61) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 3 61 [mtFiber70StateAt 0] (mtFiber70StateAt 52) h3

theorem mtFiber70State53_in_close :
    mtFiber70StateAt 53 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 1 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 1) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep1
  have h2 : mtFiber70StateAt 33 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 1) (mtFiber70StateAt 33) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep33
  have h3 : mtFiber70StateAt 37 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 33) (mtFiber70StateAt 37) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep37
  have h4 : mtFiber70StateAt 53 ∈ closeChainFiber mtWord mtFiber70DirectStates 4 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0]
      (mtFiber70StateAt 37) (mtFiber70StateAt 53) (by decide) h3 (by decide)
      mtFiber70ReverseSingleStep53
  change mtFiber70StateAt 53 ∈ closeChainFiber mtWord mtFiber70DirectStates (4 + 60) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 4 60 [mtFiber70StateAt 0] (mtFiber70StateAt 53) h4

theorem mtFiber70State54_in_close :
    mtFiber70StateAt 54 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 1 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 1) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep1
  have h2 : mtFiber70StateAt 6 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 1) (mtFiber70StateAt 6) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep6
  have h3 : mtFiber70StateAt 38 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 6) (mtFiber70StateAt 38) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep38
  have h4 : mtFiber70StateAt 54 ∈ closeChainFiber mtWord mtFiber70DirectStates 4 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0]
      (mtFiber70StateAt 38) (mtFiber70StateAt 54) (by decide) h3 (by decide)
      mtFiber70ReverseSingleStep54
  change mtFiber70StateAt 54 ∈ closeChainFiber mtWord mtFiber70DirectStates (4 + 60) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 4 60 [mtFiber70StateAt 0] (mtFiber70StateAt 54) h4

theorem mtFiber70State55_in_close :
    mtFiber70StateAt 55 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 7 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 7) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep7
  have h2 : mtFiber70StateAt 39 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 7) (mtFiber70StateAt 39) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep39
  have h3 : mtFiber70StateAt 55 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 39) (mtFiber70StateAt 55) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep55
  change mtFiber70StateAt 55 ∈ closeChainFiber mtWord mtFiber70DirectStates (3 + 61) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 3 61 [mtFiber70StateAt 0] (mtFiber70StateAt 55) h3

theorem mtFiber70State56_in_close :
    mtFiber70StateAt 56 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 24 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 24) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep24
  have h2 : mtFiber70StateAt 56 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 24) (mtFiber70StateAt 56) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep56
  change mtFiber70StateAt 56 ∈ closeChainFiber mtWord mtFiber70DirectStates (2 + 62) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 2 62 [mtFiber70StateAt 0] (mtFiber70StateAt 56) h2

theorem mtFiber70State57_in_close :
    mtFiber70StateAt 57 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 1 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 1) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep1
  have h2 : mtFiber70StateAt 25 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 1) (mtFiber70StateAt 25) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep25
  have h3 : mtFiber70StateAt 57 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 25) (mtFiber70StateAt 57) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep57
  change mtFiber70StateAt 57 ∈ closeChainFiber mtWord mtFiber70DirectStates (3 + 61) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 3 61 [mtFiber70StateAt 0] (mtFiber70StateAt 57) h3

theorem mtFiber70State58_in_close :
    mtFiber70StateAt 58 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 2 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 2) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep2
  have h2 : mtFiber70StateAt 26 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 2) (mtFiber70StateAt 26) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep26
  have h3 : mtFiber70StateAt 58 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 26) (mtFiber70StateAt 58) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep58
  change mtFiber70StateAt 58 ∈ closeChainFiber mtWord mtFiber70DirectStates (3 + 61) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 3 61 [mtFiber70StateAt 0] (mtFiber70StateAt 58) h3

theorem mtFiber70State59_in_close :
    mtFiber70StateAt 59 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 1 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 1) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep1
  have h2 : mtFiber70StateAt 3 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 1) (mtFiber70StateAt 3) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep3
  have h3 : mtFiber70StateAt 27 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 3) (mtFiber70StateAt 27) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep27
  have h4 : mtFiber70StateAt 59 ∈ closeChainFiber mtWord mtFiber70DirectStates 4 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0]
      (mtFiber70StateAt 27) (mtFiber70StateAt 59) (by decide) h3 (by decide)
      mtFiber70ReverseSingleStep59
  change mtFiber70StateAt 59 ∈ closeChainFiber mtWord mtFiber70DirectStates (4 + 60) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 4 60 [mtFiber70StateAt 0] (mtFiber70StateAt 59) h4

theorem mtFiber70State60_in_close :
    mtFiber70StateAt 60 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 24 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 24) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep24
  have h2 : mtFiber70StateAt 56 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 24) (mtFiber70StateAt 56) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep56
  have h3 : mtFiber70StateAt 60 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 56) (mtFiber70StateAt 60) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep60
  change mtFiber70StateAt 60 ∈ closeChainFiber mtWord mtFiber70DirectStates (3 + 61) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 3 61 [mtFiber70StateAt 0] (mtFiber70StateAt 60) h3

theorem mtFiber70State61_in_close :
    mtFiber70StateAt 61 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 1 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 1) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep1
  have h2 : mtFiber70StateAt 25 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 1) (mtFiber70StateAt 25) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep25
  have h3 : mtFiber70StateAt 57 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 25) (mtFiber70StateAt 57) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep57
  have h4 : mtFiber70StateAt 61 ∈ closeChainFiber mtWord mtFiber70DirectStates 4 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0]
      (mtFiber70StateAt 57) (mtFiber70StateAt 61) (by decide) h3 (by decide)
      mtFiber70ReverseSingleStep61
  change mtFiber70StateAt 61 ∈ closeChainFiber mtWord mtFiber70DirectStates (4 + 60) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 4 60 [mtFiber70StateAt 0] (mtFiber70StateAt 61) h4

theorem mtFiber70State62_in_close :
    mtFiber70StateAt 62 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 1 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 1) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep1
  have h2 : mtFiber70StateAt 6 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 1) (mtFiber70StateAt 6) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep6
  have h3 : mtFiber70StateAt 30 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 6) (mtFiber70StateAt 30) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep30
  have h4 : mtFiber70StateAt 62 ∈ closeChainFiber mtWord mtFiber70DirectStates 4 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0]
      (mtFiber70StateAt 30) (mtFiber70StateAt 62) (by decide) h3 (by decide)
      mtFiber70ReverseSingleStep62
  change mtFiber70StateAt 62 ∈ closeChainFiber mtWord mtFiber70DirectStates (4 + 60) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 4 60 [mtFiber70StateAt 0] (mtFiber70StateAt 62) h4

theorem mtFiber70State63_in_close :
    mtFiber70StateAt 63 ∈ closeChainFiber mtWord mtFiber70DirectStates mtFiber70DirectStates.length [mtFiber70StateAt 0] := by
  have h0 : mtFiber70StateAt 0 ∈ closeChainFiber mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber70StateAt 7 ∈ closeChainFiber mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 0 [mtFiber70StateAt 0]
      (mtFiber70StateAt 0) (mtFiber70StateAt 7) (by decide) h0 (by decide)
      mtFiber70ReverseSingleStep7
  have h2 : mtFiber70StateAt 31 ∈ closeChainFiber mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 1 [mtFiber70StateAt 0]
      (mtFiber70StateAt 7) (mtFiber70StateAt 31) (by decide) h1 (by decide)
      mtFiber70ReverseSingleStep31
  have h3 : mtFiber70StateAt 63 ∈ closeChainFiber mtWord mtFiber70DirectStates 3 [mtFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber70DirectStates 2 [mtFiber70StateAt 0]
      (mtFiber70StateAt 31) (mtFiber70StateAt 63) (by decide) h2 (by decide)
      mtFiber70ReverseSingleStep63
  change mtFiber70StateAt 63 ∈ closeChainFiber mtWord mtFiber70DirectStates (3 + 61) [mtFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber70DirectStates 3 61 [mtFiber70StateAt 0] (mtFiber70StateAt 63) h3

theorem mtFiber70DirectConnected :
    chainFiberConnected mtWord mtFiber70DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber70DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber70State0_in_close
  · subst state
    exact mtFiber70State1_in_close
  · subst state
    exact mtFiber70State2_in_close
  · subst state
    exact mtFiber70State3_in_close
  · subst state
    exact mtFiber70State4_in_close
  · subst state
    exact mtFiber70State5_in_close
  · subst state
    exact mtFiber70State6_in_close
  · subst state
    exact mtFiber70State7_in_close
  · subst state
    exact mtFiber70State8_in_close
  · subst state
    exact mtFiber70State9_in_close
  · subst state
    exact mtFiber70State10_in_close
  · subst state
    exact mtFiber70State11_in_close
  · subst state
    exact mtFiber70State12_in_close
  · subst state
    exact mtFiber70State13_in_close
  · subst state
    exact mtFiber70State14_in_close
  · subst state
    exact mtFiber70State15_in_close
  · subst state
    exact mtFiber70State16_in_close
  · subst state
    exact mtFiber70State17_in_close
  · subst state
    exact mtFiber70State18_in_close
  · subst state
    exact mtFiber70State19_in_close
  · subst state
    exact mtFiber70State20_in_close
  · subst state
    exact mtFiber70State21_in_close
  · subst state
    exact mtFiber70State22_in_close
  · subst state
    exact mtFiber70State23_in_close
  · subst state
    exact mtFiber70State24_in_close
  · subst state
    exact mtFiber70State25_in_close
  · subst state
    exact mtFiber70State26_in_close
  · subst state
    exact mtFiber70State27_in_close
  · subst state
    exact mtFiber70State28_in_close
  · subst state
    exact mtFiber70State29_in_close
  · subst state
    exact mtFiber70State30_in_close
  · subst state
    exact mtFiber70State31_in_close
  · subst state
    exact mtFiber70State32_in_close
  · subst state
    exact mtFiber70State33_in_close
  · subst state
    exact mtFiber70State34_in_close
  · subst state
    exact mtFiber70State35_in_close
  · subst state
    exact mtFiber70State36_in_close
  · subst state
    exact mtFiber70State37_in_close
  · subst state
    exact mtFiber70State38_in_close
  · subst state
    exact mtFiber70State39_in_close
  · subst state
    exact mtFiber70State40_in_close
  · subst state
    exact mtFiber70State41_in_close
  · subst state
    exact mtFiber70State42_in_close
  · subst state
    exact mtFiber70State43_in_close
  · subst state
    exact mtFiber70State44_in_close
  · subst state
    exact mtFiber70State45_in_close
  · subst state
    exact mtFiber70State46_in_close
  · subst state
    exact mtFiber70State47_in_close
  · subst state
    exact mtFiber70State48_in_close
  · subst state
    exact mtFiber70State49_in_close
  · subst state
    exact mtFiber70State50_in_close
  · subst state
    exact mtFiber70State51_in_close
  · subst state
    exact mtFiber70State52_in_close
  · subst state
    exact mtFiber70State53_in_close
  · subst state
    exact mtFiber70State54_in_close
  · subst state
    exact mtFiber70State55_in_close
  · subst state
    exact mtFiber70State56_in_close
  · subst state
    exact mtFiber70State57_in_close
  · subst state
    exact mtFiber70State58_in_close
  · subst state
    exact mtFiber70State59_in_close
  · subst state
    exact mtFiber70State60_in_close
  · subst state
    exact mtFiber70State61_in_close
  · subst state
    exact mtFiber70State62_in_close
  · subst state
    exact mtFiber70State63_in_close
  · cases h
end GoertzelLemma818LengthTwoMTBridge

end Mettapedia.GraphTheory.FourColor
