import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for `mirror,mirror` size-64 fiber 70

This module proves direct connectedness for one generated size-64 fiber from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMMBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorMirrorCertificate
open GoertzelLemma818MirrorMirrorReverseAudit

def mmFiber70StateAt (i : Nat) : List TauState :=
  directStates (mmFiber70RowAt i).sourceLeft (mmFiber70RowAt i).sourceRight

def mmFiber70DirectStates : List (List TauState) :=
  [mmFiber70StateAt 0, mmFiber70StateAt 1, mmFiber70StateAt 2, mmFiber70StateAt 3, mmFiber70StateAt 4, mmFiber70StateAt 5, mmFiber70StateAt 6, mmFiber70StateAt 7, mmFiber70StateAt 8, mmFiber70StateAt 9, mmFiber70StateAt 10, mmFiber70StateAt 11, mmFiber70StateAt 12, mmFiber70StateAt 13, mmFiber70StateAt 14, mmFiber70StateAt 15, mmFiber70StateAt 16, mmFiber70StateAt 17, mmFiber70StateAt 18, mmFiber70StateAt 19, mmFiber70StateAt 20, mmFiber70StateAt 21, mmFiber70StateAt 22, mmFiber70StateAt 23, mmFiber70StateAt 24, mmFiber70StateAt 25, mmFiber70StateAt 26, mmFiber70StateAt 27, mmFiber70StateAt 28, mmFiber70StateAt 29, mmFiber70StateAt 30, mmFiber70StateAt 31, mmFiber70StateAt 32, mmFiber70StateAt 33, mmFiber70StateAt 34, mmFiber70StateAt 35, mmFiber70StateAt 36, mmFiber70StateAt 37, mmFiber70StateAt 38, mmFiber70StateAt 39, mmFiber70StateAt 40, mmFiber70StateAt 41, mmFiber70StateAt 42, mmFiber70StateAt 43, mmFiber70StateAt 44, mmFiber70StateAt 45, mmFiber70StateAt 46, mmFiber70StateAt 47, mmFiber70StateAt 48, mmFiber70StateAt 49, mmFiber70StateAt 50, mmFiber70StateAt 51, mmFiber70StateAt 52, mmFiber70StateAt 53, mmFiber70StateAt 54, mmFiber70StateAt 55, mmFiber70StateAt 56, mmFiber70StateAt 57, mmFiber70StateAt 58, mmFiber70StateAt 59, mmFiber70StateAt 60, mmFiber70StateAt 61, mmFiber70StateAt 62, mmFiber70StateAt 63]

theorem mmFiber70ReverseRow_1_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk0_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 0) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 0) (mmFiber70StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 0) (mmFiber70StateAt 1)
    (mmFiber70RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 1) (by decide) mmFiber70ReverseRow_1_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_2_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk1_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 2) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber70ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 1) (mmFiber70StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 1) (mmFiber70StateAt 2)
    (mmFiber70RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 2) (by decide) mmFiber70ReverseRow_2_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_3_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk1_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 2) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 0) (mmFiber70StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 0) (mmFiber70StateAt 3)
    (mmFiber70RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 3) (by decide) mmFiber70ReverseRow_3_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_4_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk2_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 4) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber70ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 0) (mmFiber70StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 0) (mmFiber70StateAt 4)
    (mmFiber70RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 4) (by decide) mmFiber70ReverseRow_4_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_5_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk2_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 4) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 1) (mmFiber70StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 1) (mmFiber70StateAt 5)
    (mmFiber70RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 5) (by decide) mmFiber70ReverseRow_5_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_6_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk3_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 6) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber70ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 4) (mmFiber70StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 4) (mmFiber70StateAt 6)
    (mmFiber70RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 6) (by decide) mmFiber70ReverseRow_6_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_7_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk3_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 6) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 3) (mmFiber70StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 3) (mmFiber70StateAt 7)
    (mmFiber70RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 7) (by decide) mmFiber70ReverseRow_7_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_8_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 8) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk4_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 8) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber70ReverseSingleStep8 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 0) (mmFiber70StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 0) (mmFiber70StateAt 8)
    (mmFiber70RowAt 8).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 8) (by decide) mmFiber70ReverseRow_8_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_9_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 9) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk4_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 8) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep9 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 1) (mmFiber70StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 1) (mmFiber70StateAt 9)
    (mmFiber70RowAt 9).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 9) (by decide) mmFiber70ReverseRow_9_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_10_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 10) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk5_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 10) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber70ReverseSingleStep10 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 2) (mmFiber70StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 2) (mmFiber70StateAt 10)
    (mmFiber70RowAt 10).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 10) (by decide) mmFiber70ReverseRow_10_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_11_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 11) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk5_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 10) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep11 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 3) (mmFiber70StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 3) (mmFiber70StateAt 11)
    (mmFiber70RowAt 11).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 11) (by decide) mmFiber70ReverseRow_11_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_12_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 12) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk6_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 12) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber70ReverseSingleStep12 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 4) (mmFiber70StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 4) (mmFiber70StateAt 12)
    (mmFiber70RowAt 12).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 12) (by decide) mmFiber70ReverseRow_12_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_13_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 13) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk6_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 12) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep13 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 5) (mmFiber70StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 5) (mmFiber70StateAt 13)
    (mmFiber70RowAt 13).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 13) (by decide) mmFiber70ReverseRow_13_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_14_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 14) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk7_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 14) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber70ReverseSingleStep14 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 6) (mmFiber70StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 6) (mmFiber70StateAt 14)
    (mmFiber70RowAt 14).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 14) (by decide) mmFiber70ReverseRow_14_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_15_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 15) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk7_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 14) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep15 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 7) (mmFiber70StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 7) (mmFiber70StateAt 15)
    (mmFiber70RowAt 15).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 15) (by decide) mmFiber70ReverseRow_15_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_16_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 16) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk8_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 16) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber70ReverseSingleStep16 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 20) (mmFiber70StateAt 16) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 20) (mmFiber70StateAt 16)
    (mmFiber70RowAt 16).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 16) (by decide) mmFiber70ReverseRow_16_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_17_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 17) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk8_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 16) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep17 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 21) (mmFiber70StateAt 17) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 21) (mmFiber70StateAt 17)
    (mmFiber70RowAt 17).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 17) (by decide) mmFiber70ReverseRow_17_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_18_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 18) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk9_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 18) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber70ReverseSingleStep18 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 12) (mmFiber70StateAt 18) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 12) (mmFiber70StateAt 18)
    (mmFiber70RowAt 18).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 18) (by decide) mmFiber70ReverseRow_18_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_19_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 19) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk9_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 18) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep19 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 13) (mmFiber70StateAt 19) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 13) (mmFiber70StateAt 19)
    (mmFiber70RowAt 19).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 19) (by decide) mmFiber70ReverseRow_19_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_20_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 20) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk10_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 20) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber70ReverseSingleStep20 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 8) (mmFiber70StateAt 20) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 8) (mmFiber70StateAt 20)
    (mmFiber70RowAt 20).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 20) (by decide) mmFiber70ReverseRow_20_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_21_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 21) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk10_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 20) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep21 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 9) (mmFiber70StateAt 21) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 9) (mmFiber70StateAt 21)
    (mmFiber70RowAt 21).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 21) (by decide) mmFiber70ReverseRow_21_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_22_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 22) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk11_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 22) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber70ReverseSingleStep22 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 10) (mmFiber70StateAt 22) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 10) (mmFiber70StateAt 22)
    (mmFiber70RowAt 22).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 22) (by decide) mmFiber70ReverseRow_22_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_23_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 23) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk11_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 22) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep23 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 11) (mmFiber70StateAt 23) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 11) (mmFiber70StateAt 23)
    (mmFiber70RowAt 23).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 23) (by decide) mmFiber70ReverseRow_23_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_24_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 24) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk12_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 24) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber70ReverseSingleStep24 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 28) (mmFiber70StateAt 24) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 28) (mmFiber70StateAt 24)
    (mmFiber70RowAt 24).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 24) (by decide) mmFiber70ReverseRow_24_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_25_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 25) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk12_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 24) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep25 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 29) (mmFiber70StateAt 25) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 29) (mmFiber70StateAt 25)
    (mmFiber70RowAt 25).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 25) (by decide) mmFiber70ReverseRow_25_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_26_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 26) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk13_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 26) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber70ReverseSingleStep26 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 4) (mmFiber70StateAt 26) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 4) (mmFiber70StateAt 26)
    (mmFiber70RowAt 26).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 26) (by decide) mmFiber70ReverseRow_26_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_27_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 27) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk13_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 26) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep27 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 5) (mmFiber70StateAt 27) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 5) (mmFiber70StateAt 27)
    (mmFiber70RowAt 27).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 27) (by decide) mmFiber70ReverseRow_27_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_28_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 28) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk14_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 28) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber70ReverseSingleStep28 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 0) (mmFiber70StateAt 28) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 0) (mmFiber70StateAt 28)
    (mmFiber70RowAt 28).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 28) (by decide) mmFiber70ReverseRow_28_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_29_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 29) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk14_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 28) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep29 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 1) (mmFiber70StateAt 29) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 1) (mmFiber70StateAt 29)
    (mmFiber70RowAt 29).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 29) (by decide) mmFiber70ReverseRow_29_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_30_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 30) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk15_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 30) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber70ReverseSingleStep30 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 2) (mmFiber70StateAt 30) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 2) (mmFiber70StateAt 30)
    (mmFiber70RowAt 30).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 30) (by decide) mmFiber70ReverseRow_30_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_31_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 31) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk15_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 30) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep31 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 3) (mmFiber70StateAt 31) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 3) (mmFiber70StateAt 31)
    (mmFiber70RowAt 31).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 31) (by decide) mmFiber70ReverseRow_31_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_32_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 32) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk16_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 32) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber70ReverseSingleStep32 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 0) (mmFiber70StateAt 32) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 0) (mmFiber70StateAt 32)
    (mmFiber70RowAt 32).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 32) (by decide) mmFiber70ReverseRow_32_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_33_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 33) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk16_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 32) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep33 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 1) (mmFiber70StateAt 33) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 1) (mmFiber70StateAt 33)
    (mmFiber70RowAt 33).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 33) (by decide) mmFiber70ReverseRow_33_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_34_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 34) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk17_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 34) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber70ReverseSingleStep34 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 2) (mmFiber70StateAt 34) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 2) (mmFiber70StateAt 34)
    (mmFiber70RowAt 34).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 34) (by decide) mmFiber70ReverseRow_34_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_35_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 35) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk17_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 34) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep35 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 3) (mmFiber70StateAt 35) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 3) (mmFiber70StateAt 35)
    (mmFiber70RowAt 35).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 35) (by decide) mmFiber70ReverseRow_35_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_36_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 36) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk18_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 36) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber70ReverseSingleStep36 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 4) (mmFiber70StateAt 36) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 4) (mmFiber70StateAt 36)
    (mmFiber70RowAt 36).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 36) (by decide) mmFiber70ReverseRow_36_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_37_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 37) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk18_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 36) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep37 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 5) (mmFiber70StateAt 37) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 5) (mmFiber70StateAt 37)
    (mmFiber70RowAt 37).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 37) (by decide) mmFiber70ReverseRow_37_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_38_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 38) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk19_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 38) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber70ReverseSingleStep38 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 6) (mmFiber70StateAt 38) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 6) (mmFiber70StateAt 38)
    (mmFiber70RowAt 38).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 38) (by decide) mmFiber70ReverseRow_38_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_39_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 39) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk19_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 38) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep39 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 7) (mmFiber70StateAt 39) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 7) (mmFiber70StateAt 39)
    (mmFiber70RowAt 39).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 39) (by decide) mmFiber70ReverseRow_39_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_40_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 40) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk20_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 40) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber70ReverseSingleStep40 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 8) (mmFiber70StateAt 40) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 8) (mmFiber70StateAt 40)
    (mmFiber70RowAt 40).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 40) (by decide) mmFiber70ReverseRow_40_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_41_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 41) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk20_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 40) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep41 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 9) (mmFiber70StateAt 41) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 9) (mmFiber70StateAt 41)
    (mmFiber70RowAt 41).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 41) (by decide) mmFiber70ReverseRow_41_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_42_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 42) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk21_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 42) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber70ReverseSingleStep42 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 10) (mmFiber70StateAt 42) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 10) (mmFiber70StateAt 42)
    (mmFiber70RowAt 42).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 42) (by decide) mmFiber70ReverseRow_42_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_43_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 43) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk21_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 42) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep43 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 11) (mmFiber70StateAt 43) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 11) (mmFiber70StateAt 43)
    (mmFiber70RowAt 43).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 43) (by decide) mmFiber70ReverseRow_43_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_44_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 44) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk22_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 44) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber70ReverseSingleStep44 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 12) (mmFiber70StateAt 44) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 12) (mmFiber70StateAt 44)
    (mmFiber70RowAt 44).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 44) (by decide) mmFiber70ReverseRow_44_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_45_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 45) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk22_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 44) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep45 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 13) (mmFiber70StateAt 45) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 13) (mmFiber70StateAt 45)
    (mmFiber70RowAt 45).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 45) (by decide) mmFiber70ReverseRow_45_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_46_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 46) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk23_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 46) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber70ReverseSingleStep46 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 14) (mmFiber70StateAt 46) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 14) (mmFiber70StateAt 46)
    (mmFiber70RowAt 46).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 46) (by decide) mmFiber70ReverseRow_46_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_47_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 47) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk23_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 46) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep47 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 15) (mmFiber70StateAt 47) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 15) (mmFiber70StateAt 47)
    (mmFiber70RowAt 47).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 47) (by decide) mmFiber70ReverseRow_47_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_48_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 48) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk24_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 48) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber70ReverseSingleStep48 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 32) (mmFiber70StateAt 48) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 32) (mmFiber70StateAt 48)
    (mmFiber70RowAt 48).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 48) (by decide) mmFiber70ReverseRow_48_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_49_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 49) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk24_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 48) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep49 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 33) (mmFiber70StateAt 49) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 33) (mmFiber70StateAt 49)
    (mmFiber70RowAt 49).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 49) (by decide) mmFiber70ReverseRow_49_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_50_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 50) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk25_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 50) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber70ReverseSingleStep50 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 48) (mmFiber70StateAt 50) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 48) (mmFiber70StateAt 50)
    (mmFiber70RowAt 50).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 50) (by decide) mmFiber70ReverseRow_50_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_51_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 51) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk25_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 50) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep51 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 35) (mmFiber70StateAt 51) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 35) (mmFiber70StateAt 51)
    (mmFiber70RowAt 51).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 51) (by decide) mmFiber70ReverseRow_51_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_52_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 52) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk26_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 52) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber70ReverseSingleStep52 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 36) (mmFiber70StateAt 52) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 36) (mmFiber70StateAt 52)
    (mmFiber70RowAt 52).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 52) (by decide) mmFiber70ReverseRow_52_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_53_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 53) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk26_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 52) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep53 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 37) (mmFiber70StateAt 53) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 37) (mmFiber70StateAt 53)
    (mmFiber70RowAt 53).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 53) (by decide) mmFiber70ReverseRow_53_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_54_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 54) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk27_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 54) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber70ReverseSingleStep54 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 49) (mmFiber70StateAt 54) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 49) (mmFiber70StateAt 54)
    (mmFiber70RowAt 54).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 54) (by decide) mmFiber70ReverseRow_54_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_55_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 55) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk27_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 54) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep55 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 48) (mmFiber70StateAt 55) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 48) (mmFiber70StateAt 55)
    (mmFiber70RowAt 55).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 55) (by decide) mmFiber70ReverseRow_55_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_56_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 56) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk28_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 56) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber70ReverseSingleStep56 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 40) (mmFiber70StateAt 56) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 40) (mmFiber70StateAt 56)
    (mmFiber70RowAt 56).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 56) (by decide) mmFiber70ReverseRow_56_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_57_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 57) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk28_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 56) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep57 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 41) (mmFiber70StateAt 57) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 41) (mmFiber70StateAt 57)
    (mmFiber70RowAt 57).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 57) (by decide) mmFiber70ReverseRow_57_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_58_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 58) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk29_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 58) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber70ReverseSingleStep58 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 26) (mmFiber70StateAt 58) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 26) (mmFiber70StateAt 58)
    (mmFiber70RowAt 58).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 58) (by decide) mmFiber70ReverseRow_58_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_59_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 59) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk29_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 58) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep59 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 27) (mmFiber70StateAt 59) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 27) (mmFiber70StateAt 59)
    (mmFiber70RowAt 59).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 59) (by decide) mmFiber70ReverseRow_59_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_60_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 60) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk30_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 60) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber70ReverseSingleStep60 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 28) (mmFiber70StateAt 60) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 28) (mmFiber70StateAt 60)
    (mmFiber70RowAt 60).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 60) (by decide) mmFiber70ReverseRow_60_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_61_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 61) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk30_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 60) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep61 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 29) (mmFiber70StateAt 61) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 29) (mmFiber70StateAt 61)
    (mmFiber70RowAt 61).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 61) (by decide) mmFiber70ReverseRow_61_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_62_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 62) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk31_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 62) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber70ReverseSingleStep62 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 60) (mmFiber70StateAt 62) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 60) (mmFiber70StateAt 62)
    (mmFiber70RowAt 62).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 62) (by decide) mmFiber70ReverseRow_62_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70ReverseRow_63_ok :
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 63) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber70Chunk31_ok
  change (mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 62) &&
    mmRowReverseValid mmFiber70Key mmFiber70Expected (mmFiber70RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber70ReverseSingleStep63 :
    chainSingleKempeStep mmWord (mmFiber70StateAt 31) (mmFiber70StateAt 63) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber70StateAt 31) (mmFiber70StateAt 63)
    (mmFiber70RowAt 63).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber70Key mmFiber70Expected
        (mmFiber70RowAt 63) (by decide) mmFiber70ReverseRow_63_ok
      simpa [mmFiber70StateAt, mmFiber70RowAt, mmFiber70Rows, listGetD, directRow] using h)

theorem mmFiber70State0_in_close :
    mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  change mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 64 [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 0 64 [mmFiber70StateAt 0] (mmFiber70StateAt 0) (by simp [closeChainFiber])

theorem mmFiber70State1_in_close :
    mmFiber70StateAt 1 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 1 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 1) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep1
  change mmFiber70StateAt 1 ∈ closeChainFiber mmWord mmFiber70DirectStates (1 + 63) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 1 63 [mmFiber70StateAt 0] (mmFiber70StateAt 1) h1

theorem mmFiber70State2_in_close :
    mmFiber70StateAt 2 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 1 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 1) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep1
  have h2 : mmFiber70StateAt 2 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 1) (mmFiber70StateAt 2) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep2
  change mmFiber70StateAt 2 ∈ closeChainFiber mmWord mmFiber70DirectStates (2 + 62) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 2 62 [mmFiber70StateAt 0] (mmFiber70StateAt 2) h2

theorem mmFiber70State3_in_close :
    mmFiber70StateAt 3 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 3 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 3) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep3
  change mmFiber70StateAt 3 ∈ closeChainFiber mmWord mmFiber70DirectStates (1 + 63) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 1 63 [mmFiber70StateAt 0] (mmFiber70StateAt 3) h1

theorem mmFiber70State4_in_close :
    mmFiber70StateAt 4 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 4 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 4) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep4
  change mmFiber70StateAt 4 ∈ closeChainFiber mmWord mmFiber70DirectStates (1 + 63) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 1 63 [mmFiber70StateAt 0] (mmFiber70StateAt 4) h1

theorem mmFiber70State5_in_close :
    mmFiber70StateAt 5 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 1 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 1) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep1
  have h2 : mmFiber70StateAt 5 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 1) (mmFiber70StateAt 5) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep5
  change mmFiber70StateAt 5 ∈ closeChainFiber mmWord mmFiber70DirectStates (2 + 62) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 2 62 [mmFiber70StateAt 0] (mmFiber70StateAt 5) h2

theorem mmFiber70State6_in_close :
    mmFiber70StateAt 6 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 4 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 4) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep4
  have h2 : mmFiber70StateAt 6 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 4) (mmFiber70StateAt 6) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep6
  change mmFiber70StateAt 6 ∈ closeChainFiber mmWord mmFiber70DirectStates (2 + 62) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 2 62 [mmFiber70StateAt 0] (mmFiber70StateAt 6) h2

theorem mmFiber70State7_in_close :
    mmFiber70StateAt 7 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 3 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 3) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep3
  have h2 : mmFiber70StateAt 7 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 3) (mmFiber70StateAt 7) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep7
  change mmFiber70StateAt 7 ∈ closeChainFiber mmWord mmFiber70DirectStates (2 + 62) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 2 62 [mmFiber70StateAt 0] (mmFiber70StateAt 7) h2

theorem mmFiber70State8_in_close :
    mmFiber70StateAt 8 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 8 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 8) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep8
  change mmFiber70StateAt 8 ∈ closeChainFiber mmWord mmFiber70DirectStates (1 + 63) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 1 63 [mmFiber70StateAt 0] (mmFiber70StateAt 8) h1

theorem mmFiber70State9_in_close :
    mmFiber70StateAt 9 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 1 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 1) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep1
  have h2 : mmFiber70StateAt 9 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 1) (mmFiber70StateAt 9) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep9
  change mmFiber70StateAt 9 ∈ closeChainFiber mmWord mmFiber70DirectStates (2 + 62) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 2 62 [mmFiber70StateAt 0] (mmFiber70StateAt 9) h2

theorem mmFiber70State10_in_close :
    mmFiber70StateAt 10 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 1 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 1) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep1
  have h2 : mmFiber70StateAt 2 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 1) (mmFiber70StateAt 2) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep2
  have h3 : mmFiber70StateAt 10 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 2) (mmFiber70StateAt 10) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep10
  change mmFiber70StateAt 10 ∈ closeChainFiber mmWord mmFiber70DirectStates (3 + 61) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 3 61 [mmFiber70StateAt 0] (mmFiber70StateAt 10) h3

theorem mmFiber70State11_in_close :
    mmFiber70StateAt 11 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 3 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 3) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep3
  have h2 : mmFiber70StateAt 11 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 3) (mmFiber70StateAt 11) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep11
  change mmFiber70StateAt 11 ∈ closeChainFiber mmWord mmFiber70DirectStates (2 + 62) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 2 62 [mmFiber70StateAt 0] (mmFiber70StateAt 11) h2

theorem mmFiber70State12_in_close :
    mmFiber70StateAt 12 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 4 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 4) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep4
  have h2 : mmFiber70StateAt 12 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 4) (mmFiber70StateAt 12) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep12
  change mmFiber70StateAt 12 ∈ closeChainFiber mmWord mmFiber70DirectStates (2 + 62) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 2 62 [mmFiber70StateAt 0] (mmFiber70StateAt 12) h2

theorem mmFiber70State13_in_close :
    mmFiber70StateAt 13 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 1 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 1) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep1
  have h2 : mmFiber70StateAt 5 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 1) (mmFiber70StateAt 5) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep5
  have h3 : mmFiber70StateAt 13 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 5) (mmFiber70StateAt 13) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep13
  change mmFiber70StateAt 13 ∈ closeChainFiber mmWord mmFiber70DirectStates (3 + 61) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 3 61 [mmFiber70StateAt 0] (mmFiber70StateAt 13) h3

theorem mmFiber70State14_in_close :
    mmFiber70StateAt 14 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 4 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 4) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep4
  have h2 : mmFiber70StateAt 6 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 4) (mmFiber70StateAt 6) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep6
  have h3 : mmFiber70StateAt 14 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 6) (mmFiber70StateAt 14) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep14
  change mmFiber70StateAt 14 ∈ closeChainFiber mmWord mmFiber70DirectStates (3 + 61) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 3 61 [mmFiber70StateAt 0] (mmFiber70StateAt 14) h3

theorem mmFiber70State15_in_close :
    mmFiber70StateAt 15 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 3 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 3) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep3
  have h2 : mmFiber70StateAt 7 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 3) (mmFiber70StateAt 7) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep7
  have h3 : mmFiber70StateAt 15 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 7) (mmFiber70StateAt 15) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep15
  change mmFiber70StateAt 15 ∈ closeChainFiber mmWord mmFiber70DirectStates (3 + 61) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 3 61 [mmFiber70StateAt 0] (mmFiber70StateAt 15) h3

theorem mmFiber70State16_in_close :
    mmFiber70StateAt 16 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 8 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 8) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep8
  have h2 : mmFiber70StateAt 20 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 8) (mmFiber70StateAt 20) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep20
  have h3 : mmFiber70StateAt 16 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 20) (mmFiber70StateAt 16) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep16
  change mmFiber70StateAt 16 ∈ closeChainFiber mmWord mmFiber70DirectStates (3 + 61) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 3 61 [mmFiber70StateAt 0] (mmFiber70StateAt 16) h3

theorem mmFiber70State17_in_close :
    mmFiber70StateAt 17 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 1 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 1) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep1
  have h2 : mmFiber70StateAt 9 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 1) (mmFiber70StateAt 9) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep9
  have h3 : mmFiber70StateAt 21 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 9) (mmFiber70StateAt 21) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep21
  have h4 : mmFiber70StateAt 17 ∈ closeChainFiber mmWord mmFiber70DirectStates 4 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0]
      (mmFiber70StateAt 21) (mmFiber70StateAt 17) (by decide) h3 (by decide)
      mmFiber70ReverseSingleStep17
  change mmFiber70StateAt 17 ∈ closeChainFiber mmWord mmFiber70DirectStates (4 + 60) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 4 60 [mmFiber70StateAt 0] (mmFiber70StateAt 17) h4

theorem mmFiber70State18_in_close :
    mmFiber70StateAt 18 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 4 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 4) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep4
  have h2 : mmFiber70StateAt 12 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 4) (mmFiber70StateAt 12) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep12
  have h3 : mmFiber70StateAt 18 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 12) (mmFiber70StateAt 18) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep18
  change mmFiber70StateAt 18 ∈ closeChainFiber mmWord mmFiber70DirectStates (3 + 61) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 3 61 [mmFiber70StateAt 0] (mmFiber70StateAt 18) h3

theorem mmFiber70State19_in_close :
    mmFiber70StateAt 19 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 1 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 1) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep1
  have h2 : mmFiber70StateAt 5 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 1) (mmFiber70StateAt 5) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep5
  have h3 : mmFiber70StateAt 13 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 5) (mmFiber70StateAt 13) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep13
  have h4 : mmFiber70StateAt 19 ∈ closeChainFiber mmWord mmFiber70DirectStates 4 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0]
      (mmFiber70StateAt 13) (mmFiber70StateAt 19) (by decide) h3 (by decide)
      mmFiber70ReverseSingleStep19
  change mmFiber70StateAt 19 ∈ closeChainFiber mmWord mmFiber70DirectStates (4 + 60) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 4 60 [mmFiber70StateAt 0] (mmFiber70StateAt 19) h4

theorem mmFiber70State20_in_close :
    mmFiber70StateAt 20 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 8 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 8) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep8
  have h2 : mmFiber70StateAt 20 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 8) (mmFiber70StateAt 20) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep20
  change mmFiber70StateAt 20 ∈ closeChainFiber mmWord mmFiber70DirectStates (2 + 62) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 2 62 [mmFiber70StateAt 0] (mmFiber70StateAt 20) h2

theorem mmFiber70State21_in_close :
    mmFiber70StateAt 21 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 1 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 1) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep1
  have h2 : mmFiber70StateAt 9 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 1) (mmFiber70StateAt 9) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep9
  have h3 : mmFiber70StateAt 21 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 9) (mmFiber70StateAt 21) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep21
  change mmFiber70StateAt 21 ∈ closeChainFiber mmWord mmFiber70DirectStates (3 + 61) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 3 61 [mmFiber70StateAt 0] (mmFiber70StateAt 21) h3

theorem mmFiber70State22_in_close :
    mmFiber70StateAt 22 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 1 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 1) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep1
  have h2 : mmFiber70StateAt 2 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 1) (mmFiber70StateAt 2) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep2
  have h3 : mmFiber70StateAt 10 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 2) (mmFiber70StateAt 10) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep10
  have h4 : mmFiber70StateAt 22 ∈ closeChainFiber mmWord mmFiber70DirectStates 4 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0]
      (mmFiber70StateAt 10) (mmFiber70StateAt 22) (by decide) h3 (by decide)
      mmFiber70ReverseSingleStep22
  change mmFiber70StateAt 22 ∈ closeChainFiber mmWord mmFiber70DirectStates (4 + 60) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 4 60 [mmFiber70StateAt 0] (mmFiber70StateAt 22) h4

theorem mmFiber70State23_in_close :
    mmFiber70StateAt 23 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 3 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 3) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep3
  have h2 : mmFiber70StateAt 11 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 3) (mmFiber70StateAt 11) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep11
  have h3 : mmFiber70StateAt 23 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 11) (mmFiber70StateAt 23) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep23
  change mmFiber70StateAt 23 ∈ closeChainFiber mmWord mmFiber70DirectStates (3 + 61) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 3 61 [mmFiber70StateAt 0] (mmFiber70StateAt 23) h3

theorem mmFiber70State24_in_close :
    mmFiber70StateAt 24 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 28 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 28) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep28
  have h2 : mmFiber70StateAt 24 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 28) (mmFiber70StateAt 24) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep24
  change mmFiber70StateAt 24 ∈ closeChainFiber mmWord mmFiber70DirectStates (2 + 62) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 2 62 [mmFiber70StateAt 0] (mmFiber70StateAt 24) h2

theorem mmFiber70State25_in_close :
    mmFiber70StateAt 25 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 1 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 1) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep1
  have h2 : mmFiber70StateAt 29 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 1) (mmFiber70StateAt 29) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep29
  have h3 : mmFiber70StateAt 25 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 29) (mmFiber70StateAt 25) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep25
  change mmFiber70StateAt 25 ∈ closeChainFiber mmWord mmFiber70DirectStates (3 + 61) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 3 61 [mmFiber70StateAt 0] (mmFiber70StateAt 25) h3

theorem mmFiber70State26_in_close :
    mmFiber70StateAt 26 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 4 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 4) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep4
  have h2 : mmFiber70StateAt 26 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 4) (mmFiber70StateAt 26) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep26
  change mmFiber70StateAt 26 ∈ closeChainFiber mmWord mmFiber70DirectStates (2 + 62) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 2 62 [mmFiber70StateAt 0] (mmFiber70StateAt 26) h2

theorem mmFiber70State27_in_close :
    mmFiber70StateAt 27 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 1 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 1) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep1
  have h2 : mmFiber70StateAt 5 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 1) (mmFiber70StateAt 5) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep5
  have h3 : mmFiber70StateAt 27 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 5) (mmFiber70StateAt 27) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep27
  change mmFiber70StateAt 27 ∈ closeChainFiber mmWord mmFiber70DirectStates (3 + 61) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 3 61 [mmFiber70StateAt 0] (mmFiber70StateAt 27) h3

theorem mmFiber70State28_in_close :
    mmFiber70StateAt 28 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 28 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 28) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep28
  change mmFiber70StateAt 28 ∈ closeChainFiber mmWord mmFiber70DirectStates (1 + 63) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 1 63 [mmFiber70StateAt 0] (mmFiber70StateAt 28) h1

theorem mmFiber70State29_in_close :
    mmFiber70StateAt 29 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 1 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 1) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep1
  have h2 : mmFiber70StateAt 29 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 1) (mmFiber70StateAt 29) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep29
  change mmFiber70StateAt 29 ∈ closeChainFiber mmWord mmFiber70DirectStates (2 + 62) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 2 62 [mmFiber70StateAt 0] (mmFiber70StateAt 29) h2

theorem mmFiber70State30_in_close :
    mmFiber70StateAt 30 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 1 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 1) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep1
  have h2 : mmFiber70StateAt 2 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 1) (mmFiber70StateAt 2) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep2
  have h3 : mmFiber70StateAt 30 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 2) (mmFiber70StateAt 30) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep30
  change mmFiber70StateAt 30 ∈ closeChainFiber mmWord mmFiber70DirectStates (3 + 61) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 3 61 [mmFiber70StateAt 0] (mmFiber70StateAt 30) h3

theorem mmFiber70State31_in_close :
    mmFiber70StateAt 31 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 3 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 3) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep3
  have h2 : mmFiber70StateAt 31 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 3) (mmFiber70StateAt 31) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep31
  change mmFiber70StateAt 31 ∈ closeChainFiber mmWord mmFiber70DirectStates (2 + 62) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 2 62 [mmFiber70StateAt 0] (mmFiber70StateAt 31) h2

theorem mmFiber70State32_in_close :
    mmFiber70StateAt 32 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 32 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 32) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep32
  change mmFiber70StateAt 32 ∈ closeChainFiber mmWord mmFiber70DirectStates (1 + 63) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 1 63 [mmFiber70StateAt 0] (mmFiber70StateAt 32) h1

theorem mmFiber70State33_in_close :
    mmFiber70StateAt 33 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 1 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 1) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep1
  have h2 : mmFiber70StateAt 33 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 1) (mmFiber70StateAt 33) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep33
  change mmFiber70StateAt 33 ∈ closeChainFiber mmWord mmFiber70DirectStates (2 + 62) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 2 62 [mmFiber70StateAt 0] (mmFiber70StateAt 33) h2

theorem mmFiber70State34_in_close :
    mmFiber70StateAt 34 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 1 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 1) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep1
  have h2 : mmFiber70StateAt 2 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 1) (mmFiber70StateAt 2) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep2
  have h3 : mmFiber70StateAt 34 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 2) (mmFiber70StateAt 34) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep34
  change mmFiber70StateAt 34 ∈ closeChainFiber mmWord mmFiber70DirectStates (3 + 61) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 3 61 [mmFiber70StateAt 0] (mmFiber70StateAt 34) h3

theorem mmFiber70State35_in_close :
    mmFiber70StateAt 35 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 3 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 3) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep3
  have h2 : mmFiber70StateAt 35 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 3) (mmFiber70StateAt 35) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep35
  change mmFiber70StateAt 35 ∈ closeChainFiber mmWord mmFiber70DirectStates (2 + 62) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 2 62 [mmFiber70StateAt 0] (mmFiber70StateAt 35) h2

theorem mmFiber70State36_in_close :
    mmFiber70StateAt 36 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 4 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 4) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep4
  have h2 : mmFiber70StateAt 36 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 4) (mmFiber70StateAt 36) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep36
  change mmFiber70StateAt 36 ∈ closeChainFiber mmWord mmFiber70DirectStates (2 + 62) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 2 62 [mmFiber70StateAt 0] (mmFiber70StateAt 36) h2

theorem mmFiber70State37_in_close :
    mmFiber70StateAt 37 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 1 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 1) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep1
  have h2 : mmFiber70StateAt 5 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 1) (mmFiber70StateAt 5) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep5
  have h3 : mmFiber70StateAt 37 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 5) (mmFiber70StateAt 37) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep37
  change mmFiber70StateAt 37 ∈ closeChainFiber mmWord mmFiber70DirectStates (3 + 61) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 3 61 [mmFiber70StateAt 0] (mmFiber70StateAt 37) h3

theorem mmFiber70State38_in_close :
    mmFiber70StateAt 38 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 4 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 4) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep4
  have h2 : mmFiber70StateAt 6 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 4) (mmFiber70StateAt 6) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep6
  have h3 : mmFiber70StateAt 38 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 6) (mmFiber70StateAt 38) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep38
  change mmFiber70StateAt 38 ∈ closeChainFiber mmWord mmFiber70DirectStates (3 + 61) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 3 61 [mmFiber70StateAt 0] (mmFiber70StateAt 38) h3

theorem mmFiber70State39_in_close :
    mmFiber70StateAt 39 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 3 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 3) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep3
  have h2 : mmFiber70StateAt 7 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 3) (mmFiber70StateAt 7) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep7
  have h3 : mmFiber70StateAt 39 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 7) (mmFiber70StateAt 39) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep39
  change mmFiber70StateAt 39 ∈ closeChainFiber mmWord mmFiber70DirectStates (3 + 61) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 3 61 [mmFiber70StateAt 0] (mmFiber70StateAt 39) h3

theorem mmFiber70State40_in_close :
    mmFiber70StateAt 40 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 8 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 8) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep8
  have h2 : mmFiber70StateAt 40 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 8) (mmFiber70StateAt 40) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep40
  change mmFiber70StateAt 40 ∈ closeChainFiber mmWord mmFiber70DirectStates (2 + 62) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 2 62 [mmFiber70StateAt 0] (mmFiber70StateAt 40) h2

theorem mmFiber70State41_in_close :
    mmFiber70StateAt 41 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 1 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 1) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep1
  have h2 : mmFiber70StateAt 9 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 1) (mmFiber70StateAt 9) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep9
  have h3 : mmFiber70StateAt 41 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 9) (mmFiber70StateAt 41) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep41
  change mmFiber70StateAt 41 ∈ closeChainFiber mmWord mmFiber70DirectStates (3 + 61) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 3 61 [mmFiber70StateAt 0] (mmFiber70StateAt 41) h3

theorem mmFiber70State42_in_close :
    mmFiber70StateAt 42 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 1 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 1) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep1
  have h2 : mmFiber70StateAt 2 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 1) (mmFiber70StateAt 2) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep2
  have h3 : mmFiber70StateAt 10 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 2) (mmFiber70StateAt 10) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep10
  have h4 : mmFiber70StateAt 42 ∈ closeChainFiber mmWord mmFiber70DirectStates 4 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0]
      (mmFiber70StateAt 10) (mmFiber70StateAt 42) (by decide) h3 (by decide)
      mmFiber70ReverseSingleStep42
  change mmFiber70StateAt 42 ∈ closeChainFiber mmWord mmFiber70DirectStates (4 + 60) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 4 60 [mmFiber70StateAt 0] (mmFiber70StateAt 42) h4

theorem mmFiber70State43_in_close :
    mmFiber70StateAt 43 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 3 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 3) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep3
  have h2 : mmFiber70StateAt 11 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 3) (mmFiber70StateAt 11) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep11
  have h3 : mmFiber70StateAt 43 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 11) (mmFiber70StateAt 43) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep43
  change mmFiber70StateAt 43 ∈ closeChainFiber mmWord mmFiber70DirectStates (3 + 61) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 3 61 [mmFiber70StateAt 0] (mmFiber70StateAt 43) h3

theorem mmFiber70State44_in_close :
    mmFiber70StateAt 44 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 4 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 4) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep4
  have h2 : mmFiber70StateAt 12 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 4) (mmFiber70StateAt 12) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep12
  have h3 : mmFiber70StateAt 44 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 12) (mmFiber70StateAt 44) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep44
  change mmFiber70StateAt 44 ∈ closeChainFiber mmWord mmFiber70DirectStates (3 + 61) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 3 61 [mmFiber70StateAt 0] (mmFiber70StateAt 44) h3

theorem mmFiber70State45_in_close :
    mmFiber70StateAt 45 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 1 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 1) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep1
  have h2 : mmFiber70StateAt 5 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 1) (mmFiber70StateAt 5) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep5
  have h3 : mmFiber70StateAt 13 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 5) (mmFiber70StateAt 13) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep13
  have h4 : mmFiber70StateAt 45 ∈ closeChainFiber mmWord mmFiber70DirectStates 4 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0]
      (mmFiber70StateAt 13) (mmFiber70StateAt 45) (by decide) h3 (by decide)
      mmFiber70ReverseSingleStep45
  change mmFiber70StateAt 45 ∈ closeChainFiber mmWord mmFiber70DirectStates (4 + 60) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 4 60 [mmFiber70StateAt 0] (mmFiber70StateAt 45) h4

theorem mmFiber70State46_in_close :
    mmFiber70StateAt 46 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 4 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 4) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep4
  have h2 : mmFiber70StateAt 6 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 4) (mmFiber70StateAt 6) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep6
  have h3 : mmFiber70StateAt 14 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 6) (mmFiber70StateAt 14) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep14
  have h4 : mmFiber70StateAt 46 ∈ closeChainFiber mmWord mmFiber70DirectStates 4 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0]
      (mmFiber70StateAt 14) (mmFiber70StateAt 46) (by decide) h3 (by decide)
      mmFiber70ReverseSingleStep46
  change mmFiber70StateAt 46 ∈ closeChainFiber mmWord mmFiber70DirectStates (4 + 60) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 4 60 [mmFiber70StateAt 0] (mmFiber70StateAt 46) h4

theorem mmFiber70State47_in_close :
    mmFiber70StateAt 47 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 3 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 3) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep3
  have h2 : mmFiber70StateAt 7 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 3) (mmFiber70StateAt 7) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep7
  have h3 : mmFiber70StateAt 15 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 7) (mmFiber70StateAt 15) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep15
  have h4 : mmFiber70StateAt 47 ∈ closeChainFiber mmWord mmFiber70DirectStates 4 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0]
      (mmFiber70StateAt 15) (mmFiber70StateAt 47) (by decide) h3 (by decide)
      mmFiber70ReverseSingleStep47
  change mmFiber70StateAt 47 ∈ closeChainFiber mmWord mmFiber70DirectStates (4 + 60) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 4 60 [mmFiber70StateAt 0] (mmFiber70StateAt 47) h4

theorem mmFiber70State48_in_close :
    mmFiber70StateAt 48 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 32 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 32) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep32
  have h2 : mmFiber70StateAt 48 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 32) (mmFiber70StateAt 48) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep48
  change mmFiber70StateAt 48 ∈ closeChainFiber mmWord mmFiber70DirectStates (2 + 62) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 2 62 [mmFiber70StateAt 0] (mmFiber70StateAt 48) h2

theorem mmFiber70State49_in_close :
    mmFiber70StateAt 49 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 1 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 1) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep1
  have h2 : mmFiber70StateAt 33 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 1) (mmFiber70StateAt 33) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep33
  have h3 : mmFiber70StateAt 49 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 33) (mmFiber70StateAt 49) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep49
  change mmFiber70StateAt 49 ∈ closeChainFiber mmWord mmFiber70DirectStates (3 + 61) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 3 61 [mmFiber70StateAt 0] (mmFiber70StateAt 49) h3

theorem mmFiber70State50_in_close :
    mmFiber70StateAt 50 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 32 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 32) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep32
  have h2 : mmFiber70StateAt 48 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 32) (mmFiber70StateAt 48) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep48
  have h3 : mmFiber70StateAt 50 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 48) (mmFiber70StateAt 50) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep50
  change mmFiber70StateAt 50 ∈ closeChainFiber mmWord mmFiber70DirectStates (3 + 61) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 3 61 [mmFiber70StateAt 0] (mmFiber70StateAt 50) h3

theorem mmFiber70State51_in_close :
    mmFiber70StateAt 51 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 3 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 3) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep3
  have h2 : mmFiber70StateAt 35 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 3) (mmFiber70StateAt 35) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep35
  have h3 : mmFiber70StateAt 51 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 35) (mmFiber70StateAt 51) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep51
  change mmFiber70StateAt 51 ∈ closeChainFiber mmWord mmFiber70DirectStates (3 + 61) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 3 61 [mmFiber70StateAt 0] (mmFiber70StateAt 51) h3

theorem mmFiber70State52_in_close :
    mmFiber70StateAt 52 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 4 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 4) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep4
  have h2 : mmFiber70StateAt 36 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 4) (mmFiber70StateAt 36) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep36
  have h3 : mmFiber70StateAt 52 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 36) (mmFiber70StateAt 52) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep52
  change mmFiber70StateAt 52 ∈ closeChainFiber mmWord mmFiber70DirectStates (3 + 61) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 3 61 [mmFiber70StateAt 0] (mmFiber70StateAt 52) h3

theorem mmFiber70State53_in_close :
    mmFiber70StateAt 53 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 1 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 1) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep1
  have h2 : mmFiber70StateAt 5 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 1) (mmFiber70StateAt 5) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep5
  have h3 : mmFiber70StateAt 37 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 5) (mmFiber70StateAt 37) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep37
  have h4 : mmFiber70StateAt 53 ∈ closeChainFiber mmWord mmFiber70DirectStates 4 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0]
      (mmFiber70StateAt 37) (mmFiber70StateAt 53) (by decide) h3 (by decide)
      mmFiber70ReverseSingleStep53
  change mmFiber70StateAt 53 ∈ closeChainFiber mmWord mmFiber70DirectStates (4 + 60) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 4 60 [mmFiber70StateAt 0] (mmFiber70StateAt 53) h4

theorem mmFiber70State54_in_close :
    mmFiber70StateAt 54 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 1 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 1) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep1
  have h2 : mmFiber70StateAt 33 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 1) (mmFiber70StateAt 33) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep33
  have h3 : mmFiber70StateAt 49 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 33) (mmFiber70StateAt 49) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep49
  have h4 : mmFiber70StateAt 54 ∈ closeChainFiber mmWord mmFiber70DirectStates 4 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0]
      (mmFiber70StateAt 49) (mmFiber70StateAt 54) (by decide) h3 (by decide)
      mmFiber70ReverseSingleStep54
  change mmFiber70StateAt 54 ∈ closeChainFiber mmWord mmFiber70DirectStates (4 + 60) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 4 60 [mmFiber70StateAt 0] (mmFiber70StateAt 54) h4

theorem mmFiber70State55_in_close :
    mmFiber70StateAt 55 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 32 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 32) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep32
  have h2 : mmFiber70StateAt 48 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 32) (mmFiber70StateAt 48) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep48
  have h3 : mmFiber70StateAt 55 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 48) (mmFiber70StateAt 55) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep55
  change mmFiber70StateAt 55 ∈ closeChainFiber mmWord mmFiber70DirectStates (3 + 61) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 3 61 [mmFiber70StateAt 0] (mmFiber70StateAt 55) h3

theorem mmFiber70State56_in_close :
    mmFiber70StateAt 56 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 8 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 8) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep8
  have h2 : mmFiber70StateAt 40 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 8) (mmFiber70StateAt 40) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep40
  have h3 : mmFiber70StateAt 56 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 40) (mmFiber70StateAt 56) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep56
  change mmFiber70StateAt 56 ∈ closeChainFiber mmWord mmFiber70DirectStates (3 + 61) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 3 61 [mmFiber70StateAt 0] (mmFiber70StateAt 56) h3

theorem mmFiber70State57_in_close :
    mmFiber70StateAt 57 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 1 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 1) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep1
  have h2 : mmFiber70StateAt 9 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 1) (mmFiber70StateAt 9) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep9
  have h3 : mmFiber70StateAt 41 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 9) (mmFiber70StateAt 41) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep41
  have h4 : mmFiber70StateAt 57 ∈ closeChainFiber mmWord mmFiber70DirectStates 4 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0]
      (mmFiber70StateAt 41) (mmFiber70StateAt 57) (by decide) h3 (by decide)
      mmFiber70ReverseSingleStep57
  change mmFiber70StateAt 57 ∈ closeChainFiber mmWord mmFiber70DirectStates (4 + 60) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 4 60 [mmFiber70StateAt 0] (mmFiber70StateAt 57) h4

theorem mmFiber70State58_in_close :
    mmFiber70StateAt 58 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 4 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 4) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep4
  have h2 : mmFiber70StateAt 26 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 4) (mmFiber70StateAt 26) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep26
  have h3 : mmFiber70StateAt 58 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 26) (mmFiber70StateAt 58) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep58
  change mmFiber70StateAt 58 ∈ closeChainFiber mmWord mmFiber70DirectStates (3 + 61) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 3 61 [mmFiber70StateAt 0] (mmFiber70StateAt 58) h3

theorem mmFiber70State59_in_close :
    mmFiber70StateAt 59 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 1 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 1) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep1
  have h2 : mmFiber70StateAt 5 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 1) (mmFiber70StateAt 5) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep5
  have h3 : mmFiber70StateAt 27 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 5) (mmFiber70StateAt 27) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep27
  have h4 : mmFiber70StateAt 59 ∈ closeChainFiber mmWord mmFiber70DirectStates 4 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0]
      (mmFiber70StateAt 27) (mmFiber70StateAt 59) (by decide) h3 (by decide)
      mmFiber70ReverseSingleStep59
  change mmFiber70StateAt 59 ∈ closeChainFiber mmWord mmFiber70DirectStates (4 + 60) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 4 60 [mmFiber70StateAt 0] (mmFiber70StateAt 59) h4

theorem mmFiber70State60_in_close :
    mmFiber70StateAt 60 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 28 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 28) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep28
  have h2 : mmFiber70StateAt 60 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 28) (mmFiber70StateAt 60) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep60
  change mmFiber70StateAt 60 ∈ closeChainFiber mmWord mmFiber70DirectStates (2 + 62) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 2 62 [mmFiber70StateAt 0] (mmFiber70StateAt 60) h2

theorem mmFiber70State61_in_close :
    mmFiber70StateAt 61 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 1 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 1) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep1
  have h2 : mmFiber70StateAt 29 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 1) (mmFiber70StateAt 29) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep29
  have h3 : mmFiber70StateAt 61 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 29) (mmFiber70StateAt 61) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep61
  change mmFiber70StateAt 61 ∈ closeChainFiber mmWord mmFiber70DirectStates (3 + 61) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 3 61 [mmFiber70StateAt 0] (mmFiber70StateAt 61) h3

theorem mmFiber70State62_in_close :
    mmFiber70StateAt 62 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 28 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 28) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep28
  have h2 : mmFiber70StateAt 60 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 28) (mmFiber70StateAt 60) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep60
  have h3 : mmFiber70StateAt 62 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 60) (mmFiber70StateAt 62) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep62
  change mmFiber70StateAt 62 ∈ closeChainFiber mmWord mmFiber70DirectStates (3 + 61) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 3 61 [mmFiber70StateAt 0] (mmFiber70StateAt 62) h3

theorem mmFiber70State63_in_close :
    mmFiber70StateAt 63 ∈ closeChainFiber mmWord mmFiber70DirectStates mmFiber70DirectStates.length [mmFiber70StateAt 0] := by
  have h0 : mmFiber70StateAt 0 ∈ closeChainFiber mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber70StateAt 3 ∈ closeChainFiber mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 0 [mmFiber70StateAt 0]
      (mmFiber70StateAt 0) (mmFiber70StateAt 3) (by decide) h0 (by decide)
      mmFiber70ReverseSingleStep3
  have h2 : mmFiber70StateAt 31 ∈ closeChainFiber mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 1 [mmFiber70StateAt 0]
      (mmFiber70StateAt 3) (mmFiber70StateAt 31) (by decide) h1 (by decide)
      mmFiber70ReverseSingleStep31
  have h3 : mmFiber70StateAt 63 ∈ closeChainFiber mmWord mmFiber70DirectStates 3 [mmFiber70StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber70DirectStates 2 [mmFiber70StateAt 0]
      (mmFiber70StateAt 31) (mmFiber70StateAt 63) (by decide) h2 (by decide)
      mmFiber70ReverseSingleStep63
  change mmFiber70StateAt 63 ∈ closeChainFiber mmWord mmFiber70DirectStates (3 + 61) [mmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber70DirectStates 3 61 [mmFiber70StateAt 0] (mmFiber70StateAt 63) h3

theorem mmFiber70DirectConnected :
    chainFiberConnected mmWord mmFiber70DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber70DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber70State0_in_close
  · subst state
    exact mmFiber70State1_in_close
  · subst state
    exact mmFiber70State2_in_close
  · subst state
    exact mmFiber70State3_in_close
  · subst state
    exact mmFiber70State4_in_close
  · subst state
    exact mmFiber70State5_in_close
  · subst state
    exact mmFiber70State6_in_close
  · subst state
    exact mmFiber70State7_in_close
  · subst state
    exact mmFiber70State8_in_close
  · subst state
    exact mmFiber70State9_in_close
  · subst state
    exact mmFiber70State10_in_close
  · subst state
    exact mmFiber70State11_in_close
  · subst state
    exact mmFiber70State12_in_close
  · subst state
    exact mmFiber70State13_in_close
  · subst state
    exact mmFiber70State14_in_close
  · subst state
    exact mmFiber70State15_in_close
  · subst state
    exact mmFiber70State16_in_close
  · subst state
    exact mmFiber70State17_in_close
  · subst state
    exact mmFiber70State18_in_close
  · subst state
    exact mmFiber70State19_in_close
  · subst state
    exact mmFiber70State20_in_close
  · subst state
    exact mmFiber70State21_in_close
  · subst state
    exact mmFiber70State22_in_close
  · subst state
    exact mmFiber70State23_in_close
  · subst state
    exact mmFiber70State24_in_close
  · subst state
    exact mmFiber70State25_in_close
  · subst state
    exact mmFiber70State26_in_close
  · subst state
    exact mmFiber70State27_in_close
  · subst state
    exact mmFiber70State28_in_close
  · subst state
    exact mmFiber70State29_in_close
  · subst state
    exact mmFiber70State30_in_close
  · subst state
    exact mmFiber70State31_in_close
  · subst state
    exact mmFiber70State32_in_close
  · subst state
    exact mmFiber70State33_in_close
  · subst state
    exact mmFiber70State34_in_close
  · subst state
    exact mmFiber70State35_in_close
  · subst state
    exact mmFiber70State36_in_close
  · subst state
    exact mmFiber70State37_in_close
  · subst state
    exact mmFiber70State38_in_close
  · subst state
    exact mmFiber70State39_in_close
  · subst state
    exact mmFiber70State40_in_close
  · subst state
    exact mmFiber70State41_in_close
  · subst state
    exact mmFiber70State42_in_close
  · subst state
    exact mmFiber70State43_in_close
  · subst state
    exact mmFiber70State44_in_close
  · subst state
    exact mmFiber70State45_in_close
  · subst state
    exact mmFiber70State46_in_close
  · subst state
    exact mmFiber70State47_in_close
  · subst state
    exact mmFiber70State48_in_close
  · subst state
    exact mmFiber70State49_in_close
  · subst state
    exact mmFiber70State50_in_close
  · subst state
    exact mmFiber70State51_in_close
  · subst state
    exact mmFiber70State52_in_close
  · subst state
    exact mmFiber70State53_in_close
  · subst state
    exact mmFiber70State54_in_close
  · subst state
    exact mmFiber70State55_in_close
  · subst state
    exact mmFiber70State56_in_close
  · subst state
    exact mmFiber70State57_in_close
  · subst state
    exact mmFiber70State58_in_close
  · subst state
    exact mmFiber70State59_in_close
  · subst state
    exact mmFiber70State60_in_close
  · subst state
    exact mmFiber70State61_in_close
  · subst state
    exact mmFiber70State62_in_close
  · subst state
    exact mmFiber70State63_in_close
  · cases h
end GoertzelLemma818LengthTwoMMBridge

end Mettapedia.GraphTheory.FourColor
