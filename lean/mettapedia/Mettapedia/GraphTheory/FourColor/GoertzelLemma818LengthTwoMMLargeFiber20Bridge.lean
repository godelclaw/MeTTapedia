import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for `mirror,mirror` size-64 fiber 20

This module proves direct connectedness for one generated size-64 fiber from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMMBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorMirrorCertificate
open GoertzelLemma818MirrorMirrorReverseAudit

def mmFiber20StateAt (i : Nat) : List TauState :=
  directStates (mmFiber20RowAt i).sourceLeft (mmFiber20RowAt i).sourceRight

def mmFiber20DirectStates : List (List TauState) :=
  [mmFiber20StateAt 0, mmFiber20StateAt 1, mmFiber20StateAt 2, mmFiber20StateAt 3, mmFiber20StateAt 4, mmFiber20StateAt 5, mmFiber20StateAt 6, mmFiber20StateAt 7, mmFiber20StateAt 8, mmFiber20StateAt 9, mmFiber20StateAt 10, mmFiber20StateAt 11, mmFiber20StateAt 12, mmFiber20StateAt 13, mmFiber20StateAt 14, mmFiber20StateAt 15, mmFiber20StateAt 16, mmFiber20StateAt 17, mmFiber20StateAt 18, mmFiber20StateAt 19, mmFiber20StateAt 20, mmFiber20StateAt 21, mmFiber20StateAt 22, mmFiber20StateAt 23, mmFiber20StateAt 24, mmFiber20StateAt 25, mmFiber20StateAt 26, mmFiber20StateAt 27, mmFiber20StateAt 28, mmFiber20StateAt 29, mmFiber20StateAt 30, mmFiber20StateAt 31, mmFiber20StateAt 32, mmFiber20StateAt 33, mmFiber20StateAt 34, mmFiber20StateAt 35, mmFiber20StateAt 36, mmFiber20StateAt 37, mmFiber20StateAt 38, mmFiber20StateAt 39, mmFiber20StateAt 40, mmFiber20StateAt 41, mmFiber20StateAt 42, mmFiber20StateAt 43, mmFiber20StateAt 44, mmFiber20StateAt 45, mmFiber20StateAt 46, mmFiber20StateAt 47, mmFiber20StateAt 48, mmFiber20StateAt 49, mmFiber20StateAt 50, mmFiber20StateAt 51, mmFiber20StateAt 52, mmFiber20StateAt 53, mmFiber20StateAt 54, mmFiber20StateAt 55, mmFiber20StateAt 56, mmFiber20StateAt 57, mmFiber20StateAt 58, mmFiber20StateAt 59, mmFiber20StateAt 60, mmFiber20StateAt 61, mmFiber20StateAt 62, mmFiber20StateAt 63]

theorem mmFiber20ReverseRow_1_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk0_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 0) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 0) (mmFiber20StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 0) (mmFiber20StateAt 1)
    (mmFiber20RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 1) (by decide) mmFiber20ReverseRow_1_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_2_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk1_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 2) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber20ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 0) (mmFiber20StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 0) (mmFiber20StateAt 2)
    (mmFiber20RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 2) (by decide) mmFiber20ReverseRow_2_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_3_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk1_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 2) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 1) (mmFiber20StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 1) (mmFiber20StateAt 3)
    (mmFiber20RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 3) (by decide) mmFiber20ReverseRow_3_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_4_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk2_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 4) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber20ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 2) (mmFiber20StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 2) (mmFiber20StateAt 4)
    (mmFiber20RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 4) (by decide) mmFiber20ReverseRow_4_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_5_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk2_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 4) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 7) (mmFiber20StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 7) (mmFiber20StateAt 5)
    (mmFiber20RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 5) (by decide) mmFiber20ReverseRow_5_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_6_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk3_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 6) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber20ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 1) (mmFiber20StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 1) (mmFiber20StateAt 6)
    (mmFiber20RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 6) (by decide) mmFiber20ReverseRow_6_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_7_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk3_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 6) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 0) (mmFiber20StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 0) (mmFiber20StateAt 7)
    (mmFiber20RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 7) (by decide) mmFiber20ReverseRow_7_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_8_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 8) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk4_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 8) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber20ReverseSingleStep8 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 0) (mmFiber20StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 0) (mmFiber20StateAt 8)
    (mmFiber20RowAt 8).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 8) (by decide) mmFiber20ReverseRow_8_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_9_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 9) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk4_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 8) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep9 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 1) (mmFiber20StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 1) (mmFiber20StateAt 9)
    (mmFiber20RowAt 9).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 9) (by decide) mmFiber20ReverseRow_9_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_10_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 10) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk5_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 10) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber20ReverseSingleStep10 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 2) (mmFiber20StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 2) (mmFiber20StateAt 10)
    (mmFiber20RowAt 10).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 10) (by decide) mmFiber20ReverseRow_10_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_11_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 11) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk5_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 10) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep11 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 3) (mmFiber20StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 3) (mmFiber20StateAt 11)
    (mmFiber20RowAt 11).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 11) (by decide) mmFiber20ReverseRow_11_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_12_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 12) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk6_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 12) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber20ReverseSingleStep12 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 4) (mmFiber20StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 4) (mmFiber20StateAt 12)
    (mmFiber20RowAt 12).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 12) (by decide) mmFiber20ReverseRow_12_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_13_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 13) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk6_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 12) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep13 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 5) (mmFiber20StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 5) (mmFiber20StateAt 13)
    (mmFiber20RowAt 13).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 13) (by decide) mmFiber20ReverseRow_13_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_14_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 14) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk7_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 14) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber20ReverseSingleStep14 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 6) (mmFiber20StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 6) (mmFiber20StateAt 14)
    (mmFiber20RowAt 14).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 14) (by decide) mmFiber20ReverseRow_14_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_15_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 15) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk7_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 14) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep15 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 7) (mmFiber20StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 7) (mmFiber20StateAt 15)
    (mmFiber20RowAt 15).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 15) (by decide) mmFiber20ReverseRow_15_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_16_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 16) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk8_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 16) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber20ReverseSingleStep16 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 0) (mmFiber20StateAt 16) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 0) (mmFiber20StateAt 16)
    (mmFiber20RowAt 16).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 16) (by decide) mmFiber20ReverseRow_16_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_17_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 17) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk8_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 16) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep17 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 1) (mmFiber20StateAt 17) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 1) (mmFiber20StateAt 17)
    (mmFiber20RowAt 17).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 17) (by decide) mmFiber20ReverseRow_17_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_18_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 18) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk9_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 18) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber20ReverseSingleStep18 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 2) (mmFiber20StateAt 18) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 2) (mmFiber20StateAt 18)
    (mmFiber20RowAt 18).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 18) (by decide) mmFiber20ReverseRow_18_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_19_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 19) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk9_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 18) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep19 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 3) (mmFiber20StateAt 19) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 3) (mmFiber20StateAt 19)
    (mmFiber20RowAt 19).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 19) (by decide) mmFiber20ReverseRow_19_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_20_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 20) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk10_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 20) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber20ReverseSingleStep20 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 16) (mmFiber20StateAt 20) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 16) (mmFiber20StateAt 20)
    (mmFiber20RowAt 20).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 20) (by decide) mmFiber20ReverseRow_20_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_21_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 21) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk10_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 20) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep21 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 17) (mmFiber20StateAt 21) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 17) (mmFiber20StateAt 21)
    (mmFiber20RowAt 21).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 21) (by decide) mmFiber20ReverseRow_21_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_22_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 22) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk11_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 22) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber20ReverseSingleStep22 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 6) (mmFiber20StateAt 22) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 6) (mmFiber20StateAt 22)
    (mmFiber20RowAt 22).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 22) (by decide) mmFiber20ReverseRow_22_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_23_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 23) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk11_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 22) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep23 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 7) (mmFiber20StateAt 23) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 7) (mmFiber20StateAt 23)
    (mmFiber20RowAt 23).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 23) (by decide) mmFiber20ReverseRow_23_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_24_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 24) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk12_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 24) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber20ReverseSingleStep24 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 8) (mmFiber20StateAt 24) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 8) (mmFiber20StateAt 24)
    (mmFiber20RowAt 24).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 24) (by decide) mmFiber20ReverseRow_24_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_25_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 25) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk12_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 24) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep25 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 9) (mmFiber20StateAt 25) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 9) (mmFiber20StateAt 25)
    (mmFiber20RowAt 25).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 25) (by decide) mmFiber20ReverseRow_25_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_26_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 26) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk13_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 26) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber20ReverseSingleStep26 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 10) (mmFiber20StateAt 26) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 10) (mmFiber20StateAt 26)
    (mmFiber20RowAt 26).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 26) (by decide) mmFiber20ReverseRow_26_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_27_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 27) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk13_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 26) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep27 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 11) (mmFiber20StateAt 27) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 11) (mmFiber20StateAt 27)
    (mmFiber20RowAt 27).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 27) (by decide) mmFiber20ReverseRow_27_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_28_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 28) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk14_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 28) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber20ReverseSingleStep28 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 24) (mmFiber20StateAt 28) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 24) (mmFiber20StateAt 28)
    (mmFiber20RowAt 28).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 28) (by decide) mmFiber20ReverseRow_28_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_29_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 29) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk14_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 28) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep29 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 25) (mmFiber20StateAt 29) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 25) (mmFiber20StateAt 29)
    (mmFiber20RowAt 29).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 29) (by decide) mmFiber20ReverseRow_29_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_30_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 30) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk15_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 30) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber20ReverseSingleStep30 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 14) (mmFiber20StateAt 30) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 14) (mmFiber20StateAt 30)
    (mmFiber20RowAt 30).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 30) (by decide) mmFiber20ReverseRow_30_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_31_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 31) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk15_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 30) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep31 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 15) (mmFiber20StateAt 31) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 15) (mmFiber20StateAt 31)
    (mmFiber20RowAt 31).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 31) (by decide) mmFiber20ReverseRow_31_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_32_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 32) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk16_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 32) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber20ReverseSingleStep32 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 0) (mmFiber20StateAt 32) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 0) (mmFiber20StateAt 32)
    (mmFiber20RowAt 32).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 32) (by decide) mmFiber20ReverseRow_32_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_33_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 33) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk16_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 32) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep33 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 1) (mmFiber20StateAt 33) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 1) (mmFiber20StateAt 33)
    (mmFiber20RowAt 33).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 33) (by decide) mmFiber20ReverseRow_33_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_34_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 34) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk17_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 34) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber20ReverseSingleStep34 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 2) (mmFiber20StateAt 34) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 2) (mmFiber20StateAt 34)
    (mmFiber20RowAt 34).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 34) (by decide) mmFiber20ReverseRow_34_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_35_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 35) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk17_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 34) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep35 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 32) (mmFiber20StateAt 35) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 32) (mmFiber20StateAt 35)
    (mmFiber20RowAt 35).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 35) (by decide) mmFiber20ReverseRow_35_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_36_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 36) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk18_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 36) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber20ReverseSingleStep36 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 32) (mmFiber20StateAt 36) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 32) (mmFiber20StateAt 36)
    (mmFiber20RowAt 36).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 36) (by decide) mmFiber20ReverseRow_36_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_37_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 37) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk18_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 36) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep37 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 33) (mmFiber20StateAt 37) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 33) (mmFiber20StateAt 37)
    (mmFiber20RowAt 37).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 37) (by decide) mmFiber20ReverseRow_37_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_38_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 38) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk19_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 38) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber20ReverseSingleStep38 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 6) (mmFiber20StateAt 38) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 6) (mmFiber20StateAt 38)
    (mmFiber20RowAt 38).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 38) (by decide) mmFiber20ReverseRow_38_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_39_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 39) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk19_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 38) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep39 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 7) (mmFiber20StateAt 39) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 7) (mmFiber20StateAt 39)
    (mmFiber20RowAt 39).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 39) (by decide) mmFiber20ReverseRow_39_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_40_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 40) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk20_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 40) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber20ReverseSingleStep40 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 8) (mmFiber20StateAt 40) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 8) (mmFiber20StateAt 40)
    (mmFiber20RowAt 40).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 40) (by decide) mmFiber20ReverseRow_40_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_41_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 41) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk20_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 40) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep41 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 9) (mmFiber20StateAt 41) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 9) (mmFiber20StateAt 41)
    (mmFiber20RowAt 41).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 41) (by decide) mmFiber20ReverseRow_41_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_42_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 42) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk21_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 42) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber20ReverseSingleStep42 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 10) (mmFiber20StateAt 42) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 10) (mmFiber20StateAt 42)
    (mmFiber20RowAt 42).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 42) (by decide) mmFiber20ReverseRow_42_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_43_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 43) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk21_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 42) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep43 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 40) (mmFiber20StateAt 43) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 40) (mmFiber20StateAt 43)
    (mmFiber20RowAt 43).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 43) (by decide) mmFiber20ReverseRow_43_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_44_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 44) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk22_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 44) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber20ReverseSingleStep44 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 40) (mmFiber20StateAt 44) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 40) (mmFiber20StateAt 44)
    (mmFiber20RowAt 44).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 44) (by decide) mmFiber20ReverseRow_44_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_45_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 45) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk22_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 44) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep45 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 41) (mmFiber20StateAt 45) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 41) (mmFiber20StateAt 45)
    (mmFiber20RowAt 45).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 45) (by decide) mmFiber20ReverseRow_45_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_46_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 46) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk23_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 46) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber20ReverseSingleStep46 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 14) (mmFiber20StateAt 46) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 14) (mmFiber20StateAt 46)
    (mmFiber20RowAt 46).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 46) (by decide) mmFiber20ReverseRow_46_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_47_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 47) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk23_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 46) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep47 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 15) (mmFiber20StateAt 47) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 15) (mmFiber20StateAt 47)
    (mmFiber20RowAt 47).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 47) (by decide) mmFiber20ReverseRow_47_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_48_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 48) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk24_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 48) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber20ReverseSingleStep48 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 16) (mmFiber20StateAt 48) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 16) (mmFiber20StateAt 48)
    (mmFiber20RowAt 48).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 48) (by decide) mmFiber20ReverseRow_48_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_49_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 49) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk24_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 48) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep49 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 17) (mmFiber20StateAt 49) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 17) (mmFiber20StateAt 49)
    (mmFiber20RowAt 49).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 49) (by decide) mmFiber20ReverseRow_49_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_50_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 50) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk25_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 50) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber20ReverseSingleStep50 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 18) (mmFiber20StateAt 50) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 18) (mmFiber20StateAt 50)
    (mmFiber20RowAt 50).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 50) (by decide) mmFiber20ReverseRow_50_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_51_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 51) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk25_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 50) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep51 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 19) (mmFiber20StateAt 51) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 19) (mmFiber20StateAt 51)
    (mmFiber20RowAt 51).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 51) (by decide) mmFiber20ReverseRow_51_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_52_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 52) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk26_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 52) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber20ReverseSingleStep52 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 40) (mmFiber20StateAt 52) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 40) (mmFiber20StateAt 52)
    (mmFiber20RowAt 52).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 52) (by decide) mmFiber20ReverseRow_52_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_53_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 53) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk26_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 52) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep53 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 41) (mmFiber20StateAt 53) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 41) (mmFiber20StateAt 53)
    (mmFiber20RowAt 53).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 53) (by decide) mmFiber20ReverseRow_53_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_54_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 54) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk27_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 54) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber20ReverseSingleStep54 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 22) (mmFiber20StateAt 54) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 22) (mmFiber20StateAt 54)
    (mmFiber20RowAt 54).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 54) (by decide) mmFiber20ReverseRow_54_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_55_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 55) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk27_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 54) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep55 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 23) (mmFiber20StateAt 55) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 23) (mmFiber20StateAt 55)
    (mmFiber20RowAt 55).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 55) (by decide) mmFiber20ReverseRow_55_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_56_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 56) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk28_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 56) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber20ReverseSingleStep56 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 39) (mmFiber20StateAt 56) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 39) (mmFiber20StateAt 56)
    (mmFiber20RowAt 56).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 56) (by decide) mmFiber20ReverseRow_56_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_57_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 57) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk28_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 56) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep57 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 38) (mmFiber20StateAt 57) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 38) (mmFiber20StateAt 57)
    (mmFiber20RowAt 57).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 57) (by decide) mmFiber20ReverseRow_57_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_58_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 58) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk29_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 58) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber20ReverseSingleStep58 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 36) (mmFiber20StateAt 58) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 36) (mmFiber20StateAt 58)
    (mmFiber20RowAt 58).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 58) (by decide) mmFiber20ReverseRow_58_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_59_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 59) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk29_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 58) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep59 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 37) (mmFiber20StateAt 59) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 37) (mmFiber20StateAt 59)
    (mmFiber20RowAt 59).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 59) (by decide) mmFiber20ReverseRow_59_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_60_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 60) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk30_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 60) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber20ReverseSingleStep60 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 32) (mmFiber20StateAt 60) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 32) (mmFiber20StateAt 60)
    (mmFiber20RowAt 60).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 60) (by decide) mmFiber20ReverseRow_60_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_61_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 61) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk30_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 60) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep61 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 33) (mmFiber20StateAt 61) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 33) (mmFiber20StateAt 61)
    (mmFiber20RowAt 61).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 61) (by decide) mmFiber20ReverseRow_61_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_62_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 62) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk31_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 62) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber20ReverseSingleStep62 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 34) (mmFiber20StateAt 62) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 34) (mmFiber20StateAt 62)
    (mmFiber20RowAt 62).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 62) (by decide) mmFiber20ReverseRow_62_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20ReverseRow_63_ok :
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 63) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber20Chunk31_ok
  change (mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 62) &&
    mmRowReverseValid mmFiber20Key mmFiber20Expected (mmFiber20RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber20ReverseSingleStep63 :
    chainSingleKempeStep mmWord (mmFiber20StateAt 35) (mmFiber20StateAt 63) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber20StateAt 35) (mmFiber20StateAt 63)
    (mmFiber20RowAt 63).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber20Key mmFiber20Expected
        (mmFiber20RowAt 63) (by decide) mmFiber20ReverseRow_63_ok
      simpa [mmFiber20StateAt, mmFiber20RowAt, mmFiber20Rows, listGetD, directRow] using h)

theorem mmFiber20State0_in_close :
    mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  change mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 64 [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 0 64 [mmFiber20StateAt 0] (mmFiber20StateAt 0) (by simp [closeChainFiber])

theorem mmFiber20State1_in_close :
    mmFiber20StateAt 1 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 1 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 1) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep1
  change mmFiber20StateAt 1 ∈ closeChainFiber mmWord mmFiber20DirectStates (1 + 63) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 1 63 [mmFiber20StateAt 0] (mmFiber20StateAt 1) h1

theorem mmFiber20State2_in_close :
    mmFiber20StateAt 2 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 2 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 2) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep2
  change mmFiber20StateAt 2 ∈ closeChainFiber mmWord mmFiber20DirectStates (1 + 63) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 1 63 [mmFiber20StateAt 0] (mmFiber20StateAt 2) h1

theorem mmFiber20State3_in_close :
    mmFiber20StateAt 3 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 1 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 1) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep1
  have h2 : mmFiber20StateAt 3 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 1) (mmFiber20StateAt 3) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep3
  change mmFiber20StateAt 3 ∈ closeChainFiber mmWord mmFiber20DirectStates (2 + 62) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 2 62 [mmFiber20StateAt 0] (mmFiber20StateAt 3) h2

theorem mmFiber20State4_in_close :
    mmFiber20StateAt 4 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 2 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 2) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep2
  have h2 : mmFiber20StateAt 4 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 2) (mmFiber20StateAt 4) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep4
  change mmFiber20StateAt 4 ∈ closeChainFiber mmWord mmFiber20DirectStates (2 + 62) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 2 62 [mmFiber20StateAt 0] (mmFiber20StateAt 4) h2

theorem mmFiber20State5_in_close :
    mmFiber20StateAt 5 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 7 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 7) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep7
  have h2 : mmFiber20StateAt 5 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 7) (mmFiber20StateAt 5) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep5
  change mmFiber20StateAt 5 ∈ closeChainFiber mmWord mmFiber20DirectStates (2 + 62) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 2 62 [mmFiber20StateAt 0] (mmFiber20StateAt 5) h2

theorem mmFiber20State6_in_close :
    mmFiber20StateAt 6 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 1 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 1) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep1
  have h2 : mmFiber20StateAt 6 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 1) (mmFiber20StateAt 6) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep6
  change mmFiber20StateAt 6 ∈ closeChainFiber mmWord mmFiber20DirectStates (2 + 62) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 2 62 [mmFiber20StateAt 0] (mmFiber20StateAt 6) h2

theorem mmFiber20State7_in_close :
    mmFiber20StateAt 7 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 7 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 7) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep7
  change mmFiber20StateAt 7 ∈ closeChainFiber mmWord mmFiber20DirectStates (1 + 63) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 1 63 [mmFiber20StateAt 0] (mmFiber20StateAt 7) h1

theorem mmFiber20State8_in_close :
    mmFiber20StateAt 8 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 8 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 8) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep8
  change mmFiber20StateAt 8 ∈ closeChainFiber mmWord mmFiber20DirectStates (1 + 63) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 1 63 [mmFiber20StateAt 0] (mmFiber20StateAt 8) h1

theorem mmFiber20State9_in_close :
    mmFiber20StateAt 9 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 1 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 1) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep1
  have h2 : mmFiber20StateAt 9 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 1) (mmFiber20StateAt 9) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep9
  change mmFiber20StateAt 9 ∈ closeChainFiber mmWord mmFiber20DirectStates (2 + 62) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 2 62 [mmFiber20StateAt 0] (mmFiber20StateAt 9) h2

theorem mmFiber20State10_in_close :
    mmFiber20StateAt 10 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 2 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 2) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep2
  have h2 : mmFiber20StateAt 10 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 2) (mmFiber20StateAt 10) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep10
  change mmFiber20StateAt 10 ∈ closeChainFiber mmWord mmFiber20DirectStates (2 + 62) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 2 62 [mmFiber20StateAt 0] (mmFiber20StateAt 10) h2

theorem mmFiber20State11_in_close :
    mmFiber20StateAt 11 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 1 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 1) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep1
  have h2 : mmFiber20StateAt 3 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 1) (mmFiber20StateAt 3) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep3
  have h3 : mmFiber20StateAt 11 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 3) (mmFiber20StateAt 11) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep11
  change mmFiber20StateAt 11 ∈ closeChainFiber mmWord mmFiber20DirectStates (3 + 61) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 3 61 [mmFiber20StateAt 0] (mmFiber20StateAt 11) h3

theorem mmFiber20State12_in_close :
    mmFiber20StateAt 12 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 2 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 2) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep2
  have h2 : mmFiber20StateAt 4 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 2) (mmFiber20StateAt 4) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep4
  have h3 : mmFiber20StateAt 12 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 4) (mmFiber20StateAt 12) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep12
  change mmFiber20StateAt 12 ∈ closeChainFiber mmWord mmFiber20DirectStates (3 + 61) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 3 61 [mmFiber20StateAt 0] (mmFiber20StateAt 12) h3

theorem mmFiber20State13_in_close :
    mmFiber20StateAt 13 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 7 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 7) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep7
  have h2 : mmFiber20StateAt 5 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 7) (mmFiber20StateAt 5) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep5
  have h3 : mmFiber20StateAt 13 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 5) (mmFiber20StateAt 13) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep13
  change mmFiber20StateAt 13 ∈ closeChainFiber mmWord mmFiber20DirectStates (3 + 61) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 3 61 [mmFiber20StateAt 0] (mmFiber20StateAt 13) h3

theorem mmFiber20State14_in_close :
    mmFiber20StateAt 14 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 1 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 1) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep1
  have h2 : mmFiber20StateAt 6 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 1) (mmFiber20StateAt 6) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep6
  have h3 : mmFiber20StateAt 14 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 6) (mmFiber20StateAt 14) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep14
  change mmFiber20StateAt 14 ∈ closeChainFiber mmWord mmFiber20DirectStates (3 + 61) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 3 61 [mmFiber20StateAt 0] (mmFiber20StateAt 14) h3

theorem mmFiber20State15_in_close :
    mmFiber20StateAt 15 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 7 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 7) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep7
  have h2 : mmFiber20StateAt 15 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 7) (mmFiber20StateAt 15) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep15
  change mmFiber20StateAt 15 ∈ closeChainFiber mmWord mmFiber20DirectStates (2 + 62) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 2 62 [mmFiber20StateAt 0] (mmFiber20StateAt 15) h2

theorem mmFiber20State16_in_close :
    mmFiber20StateAt 16 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 16 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 16) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep16
  change mmFiber20StateAt 16 ∈ closeChainFiber mmWord mmFiber20DirectStates (1 + 63) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 1 63 [mmFiber20StateAt 0] (mmFiber20StateAt 16) h1

theorem mmFiber20State17_in_close :
    mmFiber20StateAt 17 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 1 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 1) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep1
  have h2 : mmFiber20StateAt 17 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 1) (mmFiber20StateAt 17) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep17
  change mmFiber20StateAt 17 ∈ closeChainFiber mmWord mmFiber20DirectStates (2 + 62) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 2 62 [mmFiber20StateAt 0] (mmFiber20StateAt 17) h2

theorem mmFiber20State18_in_close :
    mmFiber20StateAt 18 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 2 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 2) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep2
  have h2 : mmFiber20StateAt 18 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 2) (mmFiber20StateAt 18) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep18
  change mmFiber20StateAt 18 ∈ closeChainFiber mmWord mmFiber20DirectStates (2 + 62) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 2 62 [mmFiber20StateAt 0] (mmFiber20StateAt 18) h2

theorem mmFiber20State19_in_close :
    mmFiber20StateAt 19 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 1 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 1) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep1
  have h2 : mmFiber20StateAt 3 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 1) (mmFiber20StateAt 3) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep3
  have h3 : mmFiber20StateAt 19 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 3) (mmFiber20StateAt 19) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep19
  change mmFiber20StateAt 19 ∈ closeChainFiber mmWord mmFiber20DirectStates (3 + 61) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 3 61 [mmFiber20StateAt 0] (mmFiber20StateAt 19) h3

theorem mmFiber20State20_in_close :
    mmFiber20StateAt 20 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 16 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 16) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep16
  have h2 : mmFiber20StateAt 20 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 16) (mmFiber20StateAt 20) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep20
  change mmFiber20StateAt 20 ∈ closeChainFiber mmWord mmFiber20DirectStates (2 + 62) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 2 62 [mmFiber20StateAt 0] (mmFiber20StateAt 20) h2

theorem mmFiber20State21_in_close :
    mmFiber20StateAt 21 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 1 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 1) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep1
  have h2 : mmFiber20StateAt 17 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 1) (mmFiber20StateAt 17) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep17
  have h3 : mmFiber20StateAt 21 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 17) (mmFiber20StateAt 21) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep21
  change mmFiber20StateAt 21 ∈ closeChainFiber mmWord mmFiber20DirectStates (3 + 61) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 3 61 [mmFiber20StateAt 0] (mmFiber20StateAt 21) h3

theorem mmFiber20State22_in_close :
    mmFiber20StateAt 22 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 1 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 1) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep1
  have h2 : mmFiber20StateAt 6 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 1) (mmFiber20StateAt 6) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep6
  have h3 : mmFiber20StateAt 22 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 6) (mmFiber20StateAt 22) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep22
  change mmFiber20StateAt 22 ∈ closeChainFiber mmWord mmFiber20DirectStates (3 + 61) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 3 61 [mmFiber20StateAt 0] (mmFiber20StateAt 22) h3

theorem mmFiber20State23_in_close :
    mmFiber20StateAt 23 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 7 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 7) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep7
  have h2 : mmFiber20StateAt 23 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 7) (mmFiber20StateAt 23) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep23
  change mmFiber20StateAt 23 ∈ closeChainFiber mmWord mmFiber20DirectStates (2 + 62) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 2 62 [mmFiber20StateAt 0] (mmFiber20StateAt 23) h2

theorem mmFiber20State24_in_close :
    mmFiber20StateAt 24 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 8 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 8) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep8
  have h2 : mmFiber20StateAt 24 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 8) (mmFiber20StateAt 24) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep24
  change mmFiber20StateAt 24 ∈ closeChainFiber mmWord mmFiber20DirectStates (2 + 62) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 2 62 [mmFiber20StateAt 0] (mmFiber20StateAt 24) h2

theorem mmFiber20State25_in_close :
    mmFiber20StateAt 25 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 1 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 1) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep1
  have h2 : mmFiber20StateAt 9 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 1) (mmFiber20StateAt 9) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep9
  have h3 : mmFiber20StateAt 25 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 9) (mmFiber20StateAt 25) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep25
  change mmFiber20StateAt 25 ∈ closeChainFiber mmWord mmFiber20DirectStates (3 + 61) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 3 61 [mmFiber20StateAt 0] (mmFiber20StateAt 25) h3

theorem mmFiber20State26_in_close :
    mmFiber20StateAt 26 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 2 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 2) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep2
  have h2 : mmFiber20StateAt 10 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 2) (mmFiber20StateAt 10) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep10
  have h3 : mmFiber20StateAt 26 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 10) (mmFiber20StateAt 26) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep26
  change mmFiber20StateAt 26 ∈ closeChainFiber mmWord mmFiber20DirectStates (3 + 61) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 3 61 [mmFiber20StateAt 0] (mmFiber20StateAt 26) h3

theorem mmFiber20State27_in_close :
    mmFiber20StateAt 27 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 1 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 1) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep1
  have h2 : mmFiber20StateAt 3 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 1) (mmFiber20StateAt 3) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep3
  have h3 : mmFiber20StateAt 11 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 3) (mmFiber20StateAt 11) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep11
  have h4 : mmFiber20StateAt 27 ∈ closeChainFiber mmWord mmFiber20DirectStates 4 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0]
      (mmFiber20StateAt 11) (mmFiber20StateAt 27) (by decide) h3 (by decide)
      mmFiber20ReverseSingleStep27
  change mmFiber20StateAt 27 ∈ closeChainFiber mmWord mmFiber20DirectStates (4 + 60) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 4 60 [mmFiber20StateAt 0] (mmFiber20StateAt 27) h4

theorem mmFiber20State28_in_close :
    mmFiber20StateAt 28 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 8 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 8) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep8
  have h2 : mmFiber20StateAt 24 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 8) (mmFiber20StateAt 24) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep24
  have h3 : mmFiber20StateAt 28 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 24) (mmFiber20StateAt 28) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep28
  change mmFiber20StateAt 28 ∈ closeChainFiber mmWord mmFiber20DirectStates (3 + 61) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 3 61 [mmFiber20StateAt 0] (mmFiber20StateAt 28) h3

theorem mmFiber20State29_in_close :
    mmFiber20StateAt 29 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 1 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 1) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep1
  have h2 : mmFiber20StateAt 9 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 1) (mmFiber20StateAt 9) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep9
  have h3 : mmFiber20StateAt 25 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 9) (mmFiber20StateAt 25) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep25
  have h4 : mmFiber20StateAt 29 ∈ closeChainFiber mmWord mmFiber20DirectStates 4 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0]
      (mmFiber20StateAt 25) (mmFiber20StateAt 29) (by decide) h3 (by decide)
      mmFiber20ReverseSingleStep29
  change mmFiber20StateAt 29 ∈ closeChainFiber mmWord mmFiber20DirectStates (4 + 60) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 4 60 [mmFiber20StateAt 0] (mmFiber20StateAt 29) h4

theorem mmFiber20State30_in_close :
    mmFiber20StateAt 30 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 1 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 1) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep1
  have h2 : mmFiber20StateAt 6 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 1) (mmFiber20StateAt 6) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep6
  have h3 : mmFiber20StateAt 14 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 6) (mmFiber20StateAt 14) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep14
  have h4 : mmFiber20StateAt 30 ∈ closeChainFiber mmWord mmFiber20DirectStates 4 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0]
      (mmFiber20StateAt 14) (mmFiber20StateAt 30) (by decide) h3 (by decide)
      mmFiber20ReverseSingleStep30
  change mmFiber20StateAt 30 ∈ closeChainFiber mmWord mmFiber20DirectStates (4 + 60) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 4 60 [mmFiber20StateAt 0] (mmFiber20StateAt 30) h4

theorem mmFiber20State31_in_close :
    mmFiber20StateAt 31 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 7 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 7) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep7
  have h2 : mmFiber20StateAt 15 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 7) (mmFiber20StateAt 15) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep15
  have h3 : mmFiber20StateAt 31 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 15) (mmFiber20StateAt 31) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep31
  change mmFiber20StateAt 31 ∈ closeChainFiber mmWord mmFiber20DirectStates (3 + 61) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 3 61 [mmFiber20StateAt 0] (mmFiber20StateAt 31) h3

theorem mmFiber20State32_in_close :
    mmFiber20StateAt 32 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 32 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 32) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep32
  change mmFiber20StateAt 32 ∈ closeChainFiber mmWord mmFiber20DirectStates (1 + 63) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 1 63 [mmFiber20StateAt 0] (mmFiber20StateAt 32) h1

theorem mmFiber20State33_in_close :
    mmFiber20StateAt 33 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 1 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 1) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep1
  have h2 : mmFiber20StateAt 33 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 1) (mmFiber20StateAt 33) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep33
  change mmFiber20StateAt 33 ∈ closeChainFiber mmWord mmFiber20DirectStates (2 + 62) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 2 62 [mmFiber20StateAt 0] (mmFiber20StateAt 33) h2

theorem mmFiber20State34_in_close :
    mmFiber20StateAt 34 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 2 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 2) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep2
  have h2 : mmFiber20StateAt 34 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 2) (mmFiber20StateAt 34) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep34
  change mmFiber20StateAt 34 ∈ closeChainFiber mmWord mmFiber20DirectStates (2 + 62) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 2 62 [mmFiber20StateAt 0] (mmFiber20StateAt 34) h2

theorem mmFiber20State35_in_close :
    mmFiber20StateAt 35 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 32 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 32) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep32
  have h2 : mmFiber20StateAt 35 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 32) (mmFiber20StateAt 35) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep35
  change mmFiber20StateAt 35 ∈ closeChainFiber mmWord mmFiber20DirectStates (2 + 62) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 2 62 [mmFiber20StateAt 0] (mmFiber20StateAt 35) h2

theorem mmFiber20State36_in_close :
    mmFiber20StateAt 36 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 32 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 32) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep32
  have h2 : mmFiber20StateAt 36 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 32) (mmFiber20StateAt 36) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep36
  change mmFiber20StateAt 36 ∈ closeChainFiber mmWord mmFiber20DirectStates (2 + 62) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 2 62 [mmFiber20StateAt 0] (mmFiber20StateAt 36) h2

theorem mmFiber20State37_in_close :
    mmFiber20StateAt 37 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 1 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 1) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep1
  have h2 : mmFiber20StateAt 33 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 1) (mmFiber20StateAt 33) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep33
  have h3 : mmFiber20StateAt 37 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 33) (mmFiber20StateAt 37) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep37
  change mmFiber20StateAt 37 ∈ closeChainFiber mmWord mmFiber20DirectStates (3 + 61) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 3 61 [mmFiber20StateAt 0] (mmFiber20StateAt 37) h3

theorem mmFiber20State38_in_close :
    mmFiber20StateAt 38 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 1 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 1) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep1
  have h2 : mmFiber20StateAt 6 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 1) (mmFiber20StateAt 6) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep6
  have h3 : mmFiber20StateAt 38 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 6) (mmFiber20StateAt 38) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep38
  change mmFiber20StateAt 38 ∈ closeChainFiber mmWord mmFiber20DirectStates (3 + 61) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 3 61 [mmFiber20StateAt 0] (mmFiber20StateAt 38) h3

theorem mmFiber20State39_in_close :
    mmFiber20StateAt 39 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 7 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 7) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep7
  have h2 : mmFiber20StateAt 39 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 7) (mmFiber20StateAt 39) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep39
  change mmFiber20StateAt 39 ∈ closeChainFiber mmWord mmFiber20DirectStates (2 + 62) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 2 62 [mmFiber20StateAt 0] (mmFiber20StateAt 39) h2

theorem mmFiber20State40_in_close :
    mmFiber20StateAt 40 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 8 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 8) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep8
  have h2 : mmFiber20StateAt 40 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 8) (mmFiber20StateAt 40) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep40
  change mmFiber20StateAt 40 ∈ closeChainFiber mmWord mmFiber20DirectStates (2 + 62) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 2 62 [mmFiber20StateAt 0] (mmFiber20StateAt 40) h2

theorem mmFiber20State41_in_close :
    mmFiber20StateAt 41 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 1 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 1) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep1
  have h2 : mmFiber20StateAt 9 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 1) (mmFiber20StateAt 9) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep9
  have h3 : mmFiber20StateAt 41 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 9) (mmFiber20StateAt 41) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep41
  change mmFiber20StateAt 41 ∈ closeChainFiber mmWord mmFiber20DirectStates (3 + 61) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 3 61 [mmFiber20StateAt 0] (mmFiber20StateAt 41) h3

theorem mmFiber20State42_in_close :
    mmFiber20StateAt 42 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 2 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 2) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep2
  have h2 : mmFiber20StateAt 10 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 2) (mmFiber20StateAt 10) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep10
  have h3 : mmFiber20StateAt 42 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 10) (mmFiber20StateAt 42) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep42
  change mmFiber20StateAt 42 ∈ closeChainFiber mmWord mmFiber20DirectStates (3 + 61) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 3 61 [mmFiber20StateAt 0] (mmFiber20StateAt 42) h3

theorem mmFiber20State43_in_close :
    mmFiber20StateAt 43 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 8 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 8) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep8
  have h2 : mmFiber20StateAt 40 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 8) (mmFiber20StateAt 40) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep40
  have h3 : mmFiber20StateAt 43 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 40) (mmFiber20StateAt 43) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep43
  change mmFiber20StateAt 43 ∈ closeChainFiber mmWord mmFiber20DirectStates (3 + 61) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 3 61 [mmFiber20StateAt 0] (mmFiber20StateAt 43) h3

theorem mmFiber20State44_in_close :
    mmFiber20StateAt 44 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 8 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 8) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep8
  have h2 : mmFiber20StateAt 40 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 8) (mmFiber20StateAt 40) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep40
  have h3 : mmFiber20StateAt 44 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 40) (mmFiber20StateAt 44) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep44
  change mmFiber20StateAt 44 ∈ closeChainFiber mmWord mmFiber20DirectStates (3 + 61) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 3 61 [mmFiber20StateAt 0] (mmFiber20StateAt 44) h3

theorem mmFiber20State45_in_close :
    mmFiber20StateAt 45 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 1 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 1) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep1
  have h2 : mmFiber20StateAt 9 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 1) (mmFiber20StateAt 9) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep9
  have h3 : mmFiber20StateAt 41 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 9) (mmFiber20StateAt 41) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep41
  have h4 : mmFiber20StateAt 45 ∈ closeChainFiber mmWord mmFiber20DirectStates 4 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0]
      (mmFiber20StateAt 41) (mmFiber20StateAt 45) (by decide) h3 (by decide)
      mmFiber20ReverseSingleStep45
  change mmFiber20StateAt 45 ∈ closeChainFiber mmWord mmFiber20DirectStates (4 + 60) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 4 60 [mmFiber20StateAt 0] (mmFiber20StateAt 45) h4

theorem mmFiber20State46_in_close :
    mmFiber20StateAt 46 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 1 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 1) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep1
  have h2 : mmFiber20StateAt 6 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 1) (mmFiber20StateAt 6) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep6
  have h3 : mmFiber20StateAt 14 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 6) (mmFiber20StateAt 14) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep14
  have h4 : mmFiber20StateAt 46 ∈ closeChainFiber mmWord mmFiber20DirectStates 4 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0]
      (mmFiber20StateAt 14) (mmFiber20StateAt 46) (by decide) h3 (by decide)
      mmFiber20ReverseSingleStep46
  change mmFiber20StateAt 46 ∈ closeChainFiber mmWord mmFiber20DirectStates (4 + 60) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 4 60 [mmFiber20StateAt 0] (mmFiber20StateAt 46) h4

theorem mmFiber20State47_in_close :
    mmFiber20StateAt 47 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 7 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 7) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep7
  have h2 : mmFiber20StateAt 15 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 7) (mmFiber20StateAt 15) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep15
  have h3 : mmFiber20StateAt 47 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 15) (mmFiber20StateAt 47) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep47
  change mmFiber20StateAt 47 ∈ closeChainFiber mmWord mmFiber20DirectStates (3 + 61) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 3 61 [mmFiber20StateAt 0] (mmFiber20StateAt 47) h3

theorem mmFiber20State48_in_close :
    mmFiber20StateAt 48 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 16 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 16) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep16
  have h2 : mmFiber20StateAt 48 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 16) (mmFiber20StateAt 48) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep48
  change mmFiber20StateAt 48 ∈ closeChainFiber mmWord mmFiber20DirectStates (2 + 62) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 2 62 [mmFiber20StateAt 0] (mmFiber20StateAt 48) h2

theorem mmFiber20State49_in_close :
    mmFiber20StateAt 49 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 1 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 1) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep1
  have h2 : mmFiber20StateAt 17 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 1) (mmFiber20StateAt 17) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep17
  have h3 : mmFiber20StateAt 49 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 17) (mmFiber20StateAt 49) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep49
  change mmFiber20StateAt 49 ∈ closeChainFiber mmWord mmFiber20DirectStates (3 + 61) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 3 61 [mmFiber20StateAt 0] (mmFiber20StateAt 49) h3

theorem mmFiber20State50_in_close :
    mmFiber20StateAt 50 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 2 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 2) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep2
  have h2 : mmFiber20StateAt 18 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 2) (mmFiber20StateAt 18) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep18
  have h3 : mmFiber20StateAt 50 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 18) (mmFiber20StateAt 50) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep50
  change mmFiber20StateAt 50 ∈ closeChainFiber mmWord mmFiber20DirectStates (3 + 61) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 3 61 [mmFiber20StateAt 0] (mmFiber20StateAt 50) h3

theorem mmFiber20State51_in_close :
    mmFiber20StateAt 51 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 1 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 1) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep1
  have h2 : mmFiber20StateAt 3 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 1) (mmFiber20StateAt 3) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep3
  have h3 : mmFiber20StateAt 19 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 3) (mmFiber20StateAt 19) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep19
  have h4 : mmFiber20StateAt 51 ∈ closeChainFiber mmWord mmFiber20DirectStates 4 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0]
      (mmFiber20StateAt 19) (mmFiber20StateAt 51) (by decide) h3 (by decide)
      mmFiber20ReverseSingleStep51
  change mmFiber20StateAt 51 ∈ closeChainFiber mmWord mmFiber20DirectStates (4 + 60) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 4 60 [mmFiber20StateAt 0] (mmFiber20StateAt 51) h4

theorem mmFiber20State52_in_close :
    mmFiber20StateAt 52 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 8 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 8) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep8
  have h2 : mmFiber20StateAt 40 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 8) (mmFiber20StateAt 40) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep40
  have h3 : mmFiber20StateAt 52 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 40) (mmFiber20StateAt 52) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep52
  change mmFiber20StateAt 52 ∈ closeChainFiber mmWord mmFiber20DirectStates (3 + 61) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 3 61 [mmFiber20StateAt 0] (mmFiber20StateAt 52) h3

theorem mmFiber20State53_in_close :
    mmFiber20StateAt 53 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 1 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 1) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep1
  have h2 : mmFiber20StateAt 9 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 1) (mmFiber20StateAt 9) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep9
  have h3 : mmFiber20StateAt 41 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 9) (mmFiber20StateAt 41) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep41
  have h4 : mmFiber20StateAt 53 ∈ closeChainFiber mmWord mmFiber20DirectStates 4 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0]
      (mmFiber20StateAt 41) (mmFiber20StateAt 53) (by decide) h3 (by decide)
      mmFiber20ReverseSingleStep53
  change mmFiber20StateAt 53 ∈ closeChainFiber mmWord mmFiber20DirectStates (4 + 60) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 4 60 [mmFiber20StateAt 0] (mmFiber20StateAt 53) h4

theorem mmFiber20State54_in_close :
    mmFiber20StateAt 54 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 1 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 1) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep1
  have h2 : mmFiber20StateAt 6 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 1) (mmFiber20StateAt 6) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep6
  have h3 : mmFiber20StateAt 22 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 6) (mmFiber20StateAt 22) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep22
  have h4 : mmFiber20StateAt 54 ∈ closeChainFiber mmWord mmFiber20DirectStates 4 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0]
      (mmFiber20StateAt 22) (mmFiber20StateAt 54) (by decide) h3 (by decide)
      mmFiber20ReverseSingleStep54
  change mmFiber20StateAt 54 ∈ closeChainFiber mmWord mmFiber20DirectStates (4 + 60) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 4 60 [mmFiber20StateAt 0] (mmFiber20StateAt 54) h4

theorem mmFiber20State55_in_close :
    mmFiber20StateAt 55 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 7 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 7) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep7
  have h2 : mmFiber20StateAt 23 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 7) (mmFiber20StateAt 23) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep23
  have h3 : mmFiber20StateAt 55 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 23) (mmFiber20StateAt 55) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep55
  change mmFiber20StateAt 55 ∈ closeChainFiber mmWord mmFiber20DirectStates (3 + 61) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 3 61 [mmFiber20StateAt 0] (mmFiber20StateAt 55) h3

theorem mmFiber20State56_in_close :
    mmFiber20StateAt 56 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 7 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 7) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep7
  have h2 : mmFiber20StateAt 39 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 7) (mmFiber20StateAt 39) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep39
  have h3 : mmFiber20StateAt 56 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 39) (mmFiber20StateAt 56) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep56
  change mmFiber20StateAt 56 ∈ closeChainFiber mmWord mmFiber20DirectStates (3 + 61) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 3 61 [mmFiber20StateAt 0] (mmFiber20StateAt 56) h3

theorem mmFiber20State57_in_close :
    mmFiber20StateAt 57 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 1 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 1) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep1
  have h2 : mmFiber20StateAt 6 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 1) (mmFiber20StateAt 6) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep6
  have h3 : mmFiber20StateAt 38 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 6) (mmFiber20StateAt 38) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep38
  have h4 : mmFiber20StateAt 57 ∈ closeChainFiber mmWord mmFiber20DirectStates 4 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0]
      (mmFiber20StateAt 38) (mmFiber20StateAt 57) (by decide) h3 (by decide)
      mmFiber20ReverseSingleStep57
  change mmFiber20StateAt 57 ∈ closeChainFiber mmWord mmFiber20DirectStates (4 + 60) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 4 60 [mmFiber20StateAt 0] (mmFiber20StateAt 57) h4

theorem mmFiber20State58_in_close :
    mmFiber20StateAt 58 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 32 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 32) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep32
  have h2 : mmFiber20StateAt 36 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 32) (mmFiber20StateAt 36) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep36
  have h3 : mmFiber20StateAt 58 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 36) (mmFiber20StateAt 58) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep58
  change mmFiber20StateAt 58 ∈ closeChainFiber mmWord mmFiber20DirectStates (3 + 61) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 3 61 [mmFiber20StateAt 0] (mmFiber20StateAt 58) h3

theorem mmFiber20State59_in_close :
    mmFiber20StateAt 59 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 1 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 1) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep1
  have h2 : mmFiber20StateAt 33 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 1) (mmFiber20StateAt 33) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep33
  have h3 : mmFiber20StateAt 37 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 33) (mmFiber20StateAt 37) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep37
  have h4 : mmFiber20StateAt 59 ∈ closeChainFiber mmWord mmFiber20DirectStates 4 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0]
      (mmFiber20StateAt 37) (mmFiber20StateAt 59) (by decide) h3 (by decide)
      mmFiber20ReverseSingleStep59
  change mmFiber20StateAt 59 ∈ closeChainFiber mmWord mmFiber20DirectStates (4 + 60) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 4 60 [mmFiber20StateAt 0] (mmFiber20StateAt 59) h4

theorem mmFiber20State60_in_close :
    mmFiber20StateAt 60 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 32 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 32) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep32
  have h2 : mmFiber20StateAt 60 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 32) (mmFiber20StateAt 60) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep60
  change mmFiber20StateAt 60 ∈ closeChainFiber mmWord mmFiber20DirectStates (2 + 62) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 2 62 [mmFiber20StateAt 0] (mmFiber20StateAt 60) h2

theorem mmFiber20State61_in_close :
    mmFiber20StateAt 61 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 1 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 1) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep1
  have h2 : mmFiber20StateAt 33 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 1) (mmFiber20StateAt 33) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep33
  have h3 : mmFiber20StateAt 61 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 33) (mmFiber20StateAt 61) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep61
  change mmFiber20StateAt 61 ∈ closeChainFiber mmWord mmFiber20DirectStates (3 + 61) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 3 61 [mmFiber20StateAt 0] (mmFiber20StateAt 61) h3

theorem mmFiber20State62_in_close :
    mmFiber20StateAt 62 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 2 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 2) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep2
  have h2 : mmFiber20StateAt 34 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 2) (mmFiber20StateAt 34) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep34
  have h3 : mmFiber20StateAt 62 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 34) (mmFiber20StateAt 62) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep62
  change mmFiber20StateAt 62 ∈ closeChainFiber mmWord mmFiber20DirectStates (3 + 61) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 3 61 [mmFiber20StateAt 0] (mmFiber20StateAt 62) h3

theorem mmFiber20State63_in_close :
    mmFiber20StateAt 63 ∈ closeChainFiber mmWord mmFiber20DirectStates mmFiber20DirectStates.length [mmFiber20StateAt 0] := by
  have h0 : mmFiber20StateAt 0 ∈ closeChainFiber mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber20StateAt 32 ∈ closeChainFiber mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 0 [mmFiber20StateAt 0]
      (mmFiber20StateAt 0) (mmFiber20StateAt 32) (by decide) h0 (by decide)
      mmFiber20ReverseSingleStep32
  have h2 : mmFiber20StateAt 35 ∈ closeChainFiber mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 1 [mmFiber20StateAt 0]
      (mmFiber20StateAt 32) (mmFiber20StateAt 35) (by decide) h1 (by decide)
      mmFiber20ReverseSingleStep35
  have h3 : mmFiber20StateAt 63 ∈ closeChainFiber mmWord mmFiber20DirectStates 3 [mmFiber20StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber20DirectStates 2 [mmFiber20StateAt 0]
      (mmFiber20StateAt 35) (mmFiber20StateAt 63) (by decide) h2 (by decide)
      mmFiber20ReverseSingleStep63
  change mmFiber20StateAt 63 ∈ closeChainFiber mmWord mmFiber20DirectStates (3 + 61) [mmFiber20StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber20DirectStates 3 61 [mmFiber20StateAt 0] (mmFiber20StateAt 63) h3

theorem mmFiber20DirectConnected :
    chainFiberConnected mmWord mmFiber20DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber20DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber20State0_in_close
  · subst state
    exact mmFiber20State1_in_close
  · subst state
    exact mmFiber20State2_in_close
  · subst state
    exact mmFiber20State3_in_close
  · subst state
    exact mmFiber20State4_in_close
  · subst state
    exact mmFiber20State5_in_close
  · subst state
    exact mmFiber20State6_in_close
  · subst state
    exact mmFiber20State7_in_close
  · subst state
    exact mmFiber20State8_in_close
  · subst state
    exact mmFiber20State9_in_close
  · subst state
    exact mmFiber20State10_in_close
  · subst state
    exact mmFiber20State11_in_close
  · subst state
    exact mmFiber20State12_in_close
  · subst state
    exact mmFiber20State13_in_close
  · subst state
    exact mmFiber20State14_in_close
  · subst state
    exact mmFiber20State15_in_close
  · subst state
    exact mmFiber20State16_in_close
  · subst state
    exact mmFiber20State17_in_close
  · subst state
    exact mmFiber20State18_in_close
  · subst state
    exact mmFiber20State19_in_close
  · subst state
    exact mmFiber20State20_in_close
  · subst state
    exact mmFiber20State21_in_close
  · subst state
    exact mmFiber20State22_in_close
  · subst state
    exact mmFiber20State23_in_close
  · subst state
    exact mmFiber20State24_in_close
  · subst state
    exact mmFiber20State25_in_close
  · subst state
    exact mmFiber20State26_in_close
  · subst state
    exact mmFiber20State27_in_close
  · subst state
    exact mmFiber20State28_in_close
  · subst state
    exact mmFiber20State29_in_close
  · subst state
    exact mmFiber20State30_in_close
  · subst state
    exact mmFiber20State31_in_close
  · subst state
    exact mmFiber20State32_in_close
  · subst state
    exact mmFiber20State33_in_close
  · subst state
    exact mmFiber20State34_in_close
  · subst state
    exact mmFiber20State35_in_close
  · subst state
    exact mmFiber20State36_in_close
  · subst state
    exact mmFiber20State37_in_close
  · subst state
    exact mmFiber20State38_in_close
  · subst state
    exact mmFiber20State39_in_close
  · subst state
    exact mmFiber20State40_in_close
  · subst state
    exact mmFiber20State41_in_close
  · subst state
    exact mmFiber20State42_in_close
  · subst state
    exact mmFiber20State43_in_close
  · subst state
    exact mmFiber20State44_in_close
  · subst state
    exact mmFiber20State45_in_close
  · subst state
    exact mmFiber20State46_in_close
  · subst state
    exact mmFiber20State47_in_close
  · subst state
    exact mmFiber20State48_in_close
  · subst state
    exact mmFiber20State49_in_close
  · subst state
    exact mmFiber20State50_in_close
  · subst state
    exact mmFiber20State51_in_close
  · subst state
    exact mmFiber20State52_in_close
  · subst state
    exact mmFiber20State53_in_close
  · subst state
    exact mmFiber20State54_in_close
  · subst state
    exact mmFiber20State55_in_close
  · subst state
    exact mmFiber20State56_in_close
  · subst state
    exact mmFiber20State57_in_close
  · subst state
    exact mmFiber20State58_in_close
  · subst state
    exact mmFiber20State59_in_close
  · subst state
    exact mmFiber20State60_in_close
  · subst state
    exact mmFiber20State61_in_close
  · subst state
    exact mmFiber20State62_in_close
  · subst state
    exact mmFiber20State63_in_close
  · cases h
end GoertzelLemma818LengthTwoMMBridge

end Mettapedia.GraphTheory.FourColor
