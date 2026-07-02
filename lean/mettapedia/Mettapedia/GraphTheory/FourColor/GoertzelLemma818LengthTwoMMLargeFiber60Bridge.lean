import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for `mirror,mirror` size-64 fiber 60

This module proves direct connectedness for one generated size-64 fiber from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMMBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorMirrorCertificate
open GoertzelLemma818MirrorMirrorReverseAudit

def mmFiber60StateAt (i : Nat) : List TauState :=
  directStates (mmFiber60RowAt i).sourceLeft (mmFiber60RowAt i).sourceRight

def mmFiber60DirectStates : List (List TauState) :=
  [mmFiber60StateAt 0, mmFiber60StateAt 1, mmFiber60StateAt 2, mmFiber60StateAt 3, mmFiber60StateAt 4, mmFiber60StateAt 5, mmFiber60StateAt 6, mmFiber60StateAt 7, mmFiber60StateAt 8, mmFiber60StateAt 9, mmFiber60StateAt 10, mmFiber60StateAt 11, mmFiber60StateAt 12, mmFiber60StateAt 13, mmFiber60StateAt 14, mmFiber60StateAt 15, mmFiber60StateAt 16, mmFiber60StateAt 17, mmFiber60StateAt 18, mmFiber60StateAt 19, mmFiber60StateAt 20, mmFiber60StateAt 21, mmFiber60StateAt 22, mmFiber60StateAt 23, mmFiber60StateAt 24, mmFiber60StateAt 25, mmFiber60StateAt 26, mmFiber60StateAt 27, mmFiber60StateAt 28, mmFiber60StateAt 29, mmFiber60StateAt 30, mmFiber60StateAt 31, mmFiber60StateAt 32, mmFiber60StateAt 33, mmFiber60StateAt 34, mmFiber60StateAt 35, mmFiber60StateAt 36, mmFiber60StateAt 37, mmFiber60StateAt 38, mmFiber60StateAt 39, mmFiber60StateAt 40, mmFiber60StateAt 41, mmFiber60StateAt 42, mmFiber60StateAt 43, mmFiber60StateAt 44, mmFiber60StateAt 45, mmFiber60StateAt 46, mmFiber60StateAt 47, mmFiber60StateAt 48, mmFiber60StateAt 49, mmFiber60StateAt 50, mmFiber60StateAt 51, mmFiber60StateAt 52, mmFiber60StateAt 53, mmFiber60StateAt 54, mmFiber60StateAt 55, mmFiber60StateAt 56, mmFiber60StateAt 57, mmFiber60StateAt 58, mmFiber60StateAt 59, mmFiber60StateAt 60, mmFiber60StateAt 61, mmFiber60StateAt 62, mmFiber60StateAt 63]

theorem mmFiber60ReverseRow_1_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk0_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 0) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 0) (mmFiber60StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 0) (mmFiber60StateAt 1)
    (mmFiber60RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 1) (by decide) mmFiber60ReverseRow_1_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_2_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk1_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 2) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber60ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 1) (mmFiber60StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 1) (mmFiber60StateAt 2)
    (mmFiber60RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 2) (by decide) mmFiber60ReverseRow_2_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_3_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk1_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 2) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 0) (mmFiber60StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 0) (mmFiber60StateAt 3)
    (mmFiber60RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 3) (by decide) mmFiber60ReverseRow_3_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_4_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk2_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 4) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber60ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 0) (mmFiber60StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 0) (mmFiber60StateAt 4)
    (mmFiber60RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 4) (by decide) mmFiber60ReverseRow_4_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_5_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk2_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 4) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 1) (mmFiber60StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 1) (mmFiber60StateAt 5)
    (mmFiber60RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 5) (by decide) mmFiber60ReverseRow_5_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_6_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk3_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 6) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber60ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 4) (mmFiber60StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 4) (mmFiber60StateAt 6)
    (mmFiber60RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 6) (by decide) mmFiber60ReverseRow_6_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_7_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk3_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 6) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 3) (mmFiber60StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 3) (mmFiber60StateAt 7)
    (mmFiber60RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 7) (by decide) mmFiber60ReverseRow_7_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_8_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 8) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk4_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 8) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber60ReverseSingleStep8 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 0) (mmFiber60StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 0) (mmFiber60StateAt 8)
    (mmFiber60RowAt 8).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 8) (by decide) mmFiber60ReverseRow_8_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_9_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 9) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk4_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 8) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep9 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 1) (mmFiber60StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 1) (mmFiber60StateAt 9)
    (mmFiber60RowAt 9).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 9) (by decide) mmFiber60ReverseRow_9_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_10_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 10) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk5_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 10) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber60ReverseSingleStep10 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 2) (mmFiber60StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 2) (mmFiber60StateAt 10)
    (mmFiber60RowAt 10).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 10) (by decide) mmFiber60ReverseRow_10_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_11_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 11) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk5_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 10) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep11 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 3) (mmFiber60StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 3) (mmFiber60StateAt 11)
    (mmFiber60RowAt 11).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 11) (by decide) mmFiber60ReverseRow_11_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_12_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 12) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk6_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 12) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber60ReverseSingleStep12 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 4) (mmFiber60StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 4) (mmFiber60StateAt 12)
    (mmFiber60RowAt 12).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 12) (by decide) mmFiber60ReverseRow_12_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_13_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 13) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk6_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 12) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep13 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 5) (mmFiber60StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 5) (mmFiber60StateAt 13)
    (mmFiber60RowAt 13).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 13) (by decide) mmFiber60ReverseRow_13_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_14_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 14) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk7_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 14) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber60ReverseSingleStep14 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 6) (mmFiber60StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 6) (mmFiber60StateAt 14)
    (mmFiber60RowAt 14).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 14) (by decide) mmFiber60ReverseRow_14_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_15_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 15) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk7_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 14) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep15 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 7) (mmFiber60StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 7) (mmFiber60StateAt 15)
    (mmFiber60RowAt 15).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 15) (by decide) mmFiber60ReverseRow_15_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_16_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 16) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk8_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 16) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber60ReverseSingleStep16 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 20) (mmFiber60StateAt 16) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 20) (mmFiber60StateAt 16)
    (mmFiber60RowAt 16).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 16) (by decide) mmFiber60ReverseRow_16_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_17_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 17) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk8_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 16) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep17 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 21) (mmFiber60StateAt 17) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 21) (mmFiber60StateAt 17)
    (mmFiber60RowAt 17).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 17) (by decide) mmFiber60ReverseRow_17_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_18_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 18) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk9_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 18) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber60ReverseSingleStep18 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 12) (mmFiber60StateAt 18) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 12) (mmFiber60StateAt 18)
    (mmFiber60RowAt 18).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 18) (by decide) mmFiber60ReverseRow_18_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_19_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 19) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk9_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 18) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep19 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 13) (mmFiber60StateAt 19) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 13) (mmFiber60StateAt 19)
    (mmFiber60RowAt 19).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 19) (by decide) mmFiber60ReverseRow_19_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_20_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 20) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk10_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 20) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber60ReverseSingleStep20 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 8) (mmFiber60StateAt 20) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 8) (mmFiber60StateAt 20)
    (mmFiber60RowAt 20).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 20) (by decide) mmFiber60ReverseRow_20_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_21_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 21) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk10_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 20) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep21 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 9) (mmFiber60StateAt 21) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 9) (mmFiber60StateAt 21)
    (mmFiber60RowAt 21).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 21) (by decide) mmFiber60ReverseRow_21_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_22_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 22) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk11_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 22) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber60ReverseSingleStep22 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 10) (mmFiber60StateAt 22) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 10) (mmFiber60StateAt 22)
    (mmFiber60RowAt 22).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 22) (by decide) mmFiber60ReverseRow_22_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_23_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 23) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk11_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 22) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep23 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 11) (mmFiber60StateAt 23) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 11) (mmFiber60StateAt 23)
    (mmFiber60RowAt 23).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 23) (by decide) mmFiber60ReverseRow_23_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_24_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 24) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk12_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 24) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber60ReverseSingleStep24 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 28) (mmFiber60StateAt 24) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 28) (mmFiber60StateAt 24)
    (mmFiber60RowAt 24).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 24) (by decide) mmFiber60ReverseRow_24_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_25_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 25) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk12_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 24) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep25 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 29) (mmFiber60StateAt 25) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 29) (mmFiber60StateAt 25)
    (mmFiber60RowAt 25).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 25) (by decide) mmFiber60ReverseRow_25_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_26_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 26) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk13_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 26) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber60ReverseSingleStep26 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 4) (mmFiber60StateAt 26) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 4) (mmFiber60StateAt 26)
    (mmFiber60RowAt 26).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 26) (by decide) mmFiber60ReverseRow_26_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_27_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 27) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk13_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 26) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep27 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 5) (mmFiber60StateAt 27) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 5) (mmFiber60StateAt 27)
    (mmFiber60RowAt 27).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 27) (by decide) mmFiber60ReverseRow_27_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_28_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 28) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk14_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 28) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber60ReverseSingleStep28 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 0) (mmFiber60StateAt 28) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 0) (mmFiber60StateAt 28)
    (mmFiber60RowAt 28).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 28) (by decide) mmFiber60ReverseRow_28_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_29_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 29) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk14_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 28) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep29 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 1) (mmFiber60StateAt 29) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 1) (mmFiber60StateAt 29)
    (mmFiber60RowAt 29).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 29) (by decide) mmFiber60ReverseRow_29_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_30_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 30) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk15_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 30) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber60ReverseSingleStep30 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 2) (mmFiber60StateAt 30) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 2) (mmFiber60StateAt 30)
    (mmFiber60RowAt 30).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 30) (by decide) mmFiber60ReverseRow_30_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_31_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 31) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk15_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 30) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep31 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 3) (mmFiber60StateAt 31) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 3) (mmFiber60StateAt 31)
    (mmFiber60RowAt 31).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 31) (by decide) mmFiber60ReverseRow_31_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_32_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 32) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk16_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 32) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber60ReverseSingleStep32 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 0) (mmFiber60StateAt 32) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 0) (mmFiber60StateAt 32)
    (mmFiber60RowAt 32).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 32) (by decide) mmFiber60ReverseRow_32_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_33_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 33) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk16_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 32) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep33 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 1) (mmFiber60StateAt 33) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 1) (mmFiber60StateAt 33)
    (mmFiber60RowAt 33).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 33) (by decide) mmFiber60ReverseRow_33_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_34_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 34) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk17_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 34) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber60ReverseSingleStep34 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 2) (mmFiber60StateAt 34) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 2) (mmFiber60StateAt 34)
    (mmFiber60RowAt 34).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 34) (by decide) mmFiber60ReverseRow_34_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_35_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 35) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk17_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 34) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep35 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 3) (mmFiber60StateAt 35) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 3) (mmFiber60StateAt 35)
    (mmFiber60RowAt 35).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 35) (by decide) mmFiber60ReverseRow_35_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_36_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 36) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk18_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 36) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber60ReverseSingleStep36 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 4) (mmFiber60StateAt 36) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 4) (mmFiber60StateAt 36)
    (mmFiber60RowAt 36).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 36) (by decide) mmFiber60ReverseRow_36_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_37_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 37) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk18_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 36) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep37 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 5) (mmFiber60StateAt 37) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 5) (mmFiber60StateAt 37)
    (mmFiber60RowAt 37).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 37) (by decide) mmFiber60ReverseRow_37_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_38_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 38) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk19_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 38) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber60ReverseSingleStep38 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 6) (mmFiber60StateAt 38) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 6) (mmFiber60StateAt 38)
    (mmFiber60RowAt 38).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 38) (by decide) mmFiber60ReverseRow_38_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_39_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 39) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk19_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 38) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep39 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 7) (mmFiber60StateAt 39) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 7) (mmFiber60StateAt 39)
    (mmFiber60RowAt 39).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 39) (by decide) mmFiber60ReverseRow_39_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_40_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 40) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk20_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 40) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber60ReverseSingleStep40 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 8) (mmFiber60StateAt 40) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 8) (mmFiber60StateAt 40)
    (mmFiber60RowAt 40).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 40) (by decide) mmFiber60ReverseRow_40_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_41_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 41) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk20_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 40) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep41 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 9) (mmFiber60StateAt 41) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 9) (mmFiber60StateAt 41)
    (mmFiber60RowAt 41).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 41) (by decide) mmFiber60ReverseRow_41_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_42_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 42) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk21_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 42) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber60ReverseSingleStep42 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 10) (mmFiber60StateAt 42) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 10) (mmFiber60StateAt 42)
    (mmFiber60RowAt 42).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 42) (by decide) mmFiber60ReverseRow_42_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_43_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 43) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk21_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 42) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep43 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 11) (mmFiber60StateAt 43) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 11) (mmFiber60StateAt 43)
    (mmFiber60RowAt 43).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 43) (by decide) mmFiber60ReverseRow_43_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_44_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 44) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk22_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 44) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber60ReverseSingleStep44 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 12) (mmFiber60StateAt 44) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 12) (mmFiber60StateAt 44)
    (mmFiber60RowAt 44).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 44) (by decide) mmFiber60ReverseRow_44_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_45_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 45) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk22_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 44) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep45 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 13) (mmFiber60StateAt 45) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 13) (mmFiber60StateAt 45)
    (mmFiber60RowAt 45).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 45) (by decide) mmFiber60ReverseRow_45_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_46_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 46) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk23_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 46) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber60ReverseSingleStep46 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 14) (mmFiber60StateAt 46) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 14) (mmFiber60StateAt 46)
    (mmFiber60RowAt 46).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 46) (by decide) mmFiber60ReverseRow_46_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_47_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 47) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk23_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 46) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep47 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 15) (mmFiber60StateAt 47) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 15) (mmFiber60StateAt 47)
    (mmFiber60RowAt 47).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 47) (by decide) mmFiber60ReverseRow_47_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_48_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 48) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk24_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 48) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber60ReverseSingleStep48 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 32) (mmFiber60StateAt 48) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 32) (mmFiber60StateAt 48)
    (mmFiber60RowAt 48).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 48) (by decide) mmFiber60ReverseRow_48_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_49_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 49) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk24_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 48) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep49 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 33) (mmFiber60StateAt 49) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 33) (mmFiber60StateAt 49)
    (mmFiber60RowAt 49).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 49) (by decide) mmFiber60ReverseRow_49_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_50_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 50) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk25_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 50) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber60ReverseSingleStep50 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 48) (mmFiber60StateAt 50) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 48) (mmFiber60StateAt 50)
    (mmFiber60RowAt 50).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 50) (by decide) mmFiber60ReverseRow_50_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_51_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 51) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk25_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 50) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep51 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 35) (mmFiber60StateAt 51) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 35) (mmFiber60StateAt 51)
    (mmFiber60RowAt 51).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 51) (by decide) mmFiber60ReverseRow_51_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_52_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 52) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk26_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 52) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber60ReverseSingleStep52 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 36) (mmFiber60StateAt 52) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 36) (mmFiber60StateAt 52)
    (mmFiber60RowAt 52).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 52) (by decide) mmFiber60ReverseRow_52_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_53_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 53) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk26_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 52) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep53 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 37) (mmFiber60StateAt 53) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 37) (mmFiber60StateAt 53)
    (mmFiber60RowAt 53).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 53) (by decide) mmFiber60ReverseRow_53_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_54_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 54) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk27_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 54) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber60ReverseSingleStep54 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 49) (mmFiber60StateAt 54) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 49) (mmFiber60StateAt 54)
    (mmFiber60RowAt 54).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 54) (by decide) mmFiber60ReverseRow_54_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_55_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 55) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk27_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 54) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep55 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 48) (mmFiber60StateAt 55) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 48) (mmFiber60StateAt 55)
    (mmFiber60RowAt 55).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 55) (by decide) mmFiber60ReverseRow_55_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_56_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 56) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk28_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 56) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber60ReverseSingleStep56 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 40) (mmFiber60StateAt 56) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 40) (mmFiber60StateAt 56)
    (mmFiber60RowAt 56).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 56) (by decide) mmFiber60ReverseRow_56_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_57_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 57) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk28_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 56) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep57 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 41) (mmFiber60StateAt 57) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 41) (mmFiber60StateAt 57)
    (mmFiber60RowAt 57).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 57) (by decide) mmFiber60ReverseRow_57_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_58_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 58) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk29_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 58) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber60ReverseSingleStep58 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 26) (mmFiber60StateAt 58) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 26) (mmFiber60StateAt 58)
    (mmFiber60RowAt 58).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 58) (by decide) mmFiber60ReverseRow_58_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_59_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 59) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk29_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 58) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep59 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 27) (mmFiber60StateAt 59) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 27) (mmFiber60StateAt 59)
    (mmFiber60RowAt 59).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 59) (by decide) mmFiber60ReverseRow_59_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_60_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 60) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk30_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 60) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber60ReverseSingleStep60 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 28) (mmFiber60StateAt 60) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 28) (mmFiber60StateAt 60)
    (mmFiber60RowAt 60).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 60) (by decide) mmFiber60ReverseRow_60_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_61_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 61) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk30_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 60) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep61 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 29) (mmFiber60StateAt 61) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 29) (mmFiber60StateAt 61)
    (mmFiber60RowAt 61).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 61) (by decide) mmFiber60ReverseRow_61_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_62_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 62) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk31_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 62) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber60ReverseSingleStep62 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 60) (mmFiber60StateAt 62) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 60) (mmFiber60StateAt 62)
    (mmFiber60RowAt 62).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 62) (by decide) mmFiber60ReverseRow_62_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60ReverseRow_63_ok :
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 63) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber60Chunk31_ok
  change (mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 62) &&
    mmRowReverseValid mmFiber60Key mmFiber60Expected (mmFiber60RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber60ReverseSingleStep63 :
    chainSingleKempeStep mmWord (mmFiber60StateAt 31) (mmFiber60StateAt 63) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber60StateAt 31) (mmFiber60StateAt 63)
    (mmFiber60RowAt 63).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber60Key mmFiber60Expected
        (mmFiber60RowAt 63) (by decide) mmFiber60ReverseRow_63_ok
      simpa [mmFiber60StateAt, mmFiber60RowAt, mmFiber60Rows, listGetD, directRow] using h)

theorem mmFiber60State0_in_close :
    mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  change mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 64 [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 0 64 [mmFiber60StateAt 0] (mmFiber60StateAt 0) (by simp [closeChainFiber])

theorem mmFiber60State1_in_close :
    mmFiber60StateAt 1 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 1 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 1) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep1
  change mmFiber60StateAt 1 ∈ closeChainFiber mmWord mmFiber60DirectStates (1 + 63) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 1 63 [mmFiber60StateAt 0] (mmFiber60StateAt 1) h1

theorem mmFiber60State2_in_close :
    mmFiber60StateAt 2 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 1 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 1) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep1
  have h2 : mmFiber60StateAt 2 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 1) (mmFiber60StateAt 2) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep2
  change mmFiber60StateAt 2 ∈ closeChainFiber mmWord mmFiber60DirectStates (2 + 62) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 2 62 [mmFiber60StateAt 0] (mmFiber60StateAt 2) h2

theorem mmFiber60State3_in_close :
    mmFiber60StateAt 3 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 3 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 3) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep3
  change mmFiber60StateAt 3 ∈ closeChainFiber mmWord mmFiber60DirectStates (1 + 63) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 1 63 [mmFiber60StateAt 0] (mmFiber60StateAt 3) h1

theorem mmFiber60State4_in_close :
    mmFiber60StateAt 4 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 4 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 4) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep4
  change mmFiber60StateAt 4 ∈ closeChainFiber mmWord mmFiber60DirectStates (1 + 63) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 1 63 [mmFiber60StateAt 0] (mmFiber60StateAt 4) h1

theorem mmFiber60State5_in_close :
    mmFiber60StateAt 5 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 1 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 1) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep1
  have h2 : mmFiber60StateAt 5 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 1) (mmFiber60StateAt 5) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep5
  change mmFiber60StateAt 5 ∈ closeChainFiber mmWord mmFiber60DirectStates (2 + 62) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 2 62 [mmFiber60StateAt 0] (mmFiber60StateAt 5) h2

theorem mmFiber60State6_in_close :
    mmFiber60StateAt 6 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 4 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 4) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep4
  have h2 : mmFiber60StateAt 6 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 4) (mmFiber60StateAt 6) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep6
  change mmFiber60StateAt 6 ∈ closeChainFiber mmWord mmFiber60DirectStates (2 + 62) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 2 62 [mmFiber60StateAt 0] (mmFiber60StateAt 6) h2

theorem mmFiber60State7_in_close :
    mmFiber60StateAt 7 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 3 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 3) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep3
  have h2 : mmFiber60StateAt 7 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 3) (mmFiber60StateAt 7) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep7
  change mmFiber60StateAt 7 ∈ closeChainFiber mmWord mmFiber60DirectStates (2 + 62) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 2 62 [mmFiber60StateAt 0] (mmFiber60StateAt 7) h2

theorem mmFiber60State8_in_close :
    mmFiber60StateAt 8 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 8 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 8) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep8
  change mmFiber60StateAt 8 ∈ closeChainFiber mmWord mmFiber60DirectStates (1 + 63) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 1 63 [mmFiber60StateAt 0] (mmFiber60StateAt 8) h1

theorem mmFiber60State9_in_close :
    mmFiber60StateAt 9 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 1 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 1) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep1
  have h2 : mmFiber60StateAt 9 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 1) (mmFiber60StateAt 9) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep9
  change mmFiber60StateAt 9 ∈ closeChainFiber mmWord mmFiber60DirectStates (2 + 62) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 2 62 [mmFiber60StateAt 0] (mmFiber60StateAt 9) h2

theorem mmFiber60State10_in_close :
    mmFiber60StateAt 10 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 1 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 1) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep1
  have h2 : mmFiber60StateAt 2 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 1) (mmFiber60StateAt 2) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep2
  have h3 : mmFiber60StateAt 10 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 2) (mmFiber60StateAt 10) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep10
  change mmFiber60StateAt 10 ∈ closeChainFiber mmWord mmFiber60DirectStates (3 + 61) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 3 61 [mmFiber60StateAt 0] (mmFiber60StateAt 10) h3

theorem mmFiber60State11_in_close :
    mmFiber60StateAt 11 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 3 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 3) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep3
  have h2 : mmFiber60StateAt 11 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 3) (mmFiber60StateAt 11) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep11
  change mmFiber60StateAt 11 ∈ closeChainFiber mmWord mmFiber60DirectStates (2 + 62) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 2 62 [mmFiber60StateAt 0] (mmFiber60StateAt 11) h2

theorem mmFiber60State12_in_close :
    mmFiber60StateAt 12 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 4 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 4) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep4
  have h2 : mmFiber60StateAt 12 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 4) (mmFiber60StateAt 12) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep12
  change mmFiber60StateAt 12 ∈ closeChainFiber mmWord mmFiber60DirectStates (2 + 62) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 2 62 [mmFiber60StateAt 0] (mmFiber60StateAt 12) h2

theorem mmFiber60State13_in_close :
    mmFiber60StateAt 13 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 1 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 1) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep1
  have h2 : mmFiber60StateAt 5 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 1) (mmFiber60StateAt 5) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep5
  have h3 : mmFiber60StateAt 13 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 5) (mmFiber60StateAt 13) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep13
  change mmFiber60StateAt 13 ∈ closeChainFiber mmWord mmFiber60DirectStates (3 + 61) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 3 61 [mmFiber60StateAt 0] (mmFiber60StateAt 13) h3

theorem mmFiber60State14_in_close :
    mmFiber60StateAt 14 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 4 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 4) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep4
  have h2 : mmFiber60StateAt 6 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 4) (mmFiber60StateAt 6) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep6
  have h3 : mmFiber60StateAt 14 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 6) (mmFiber60StateAt 14) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep14
  change mmFiber60StateAt 14 ∈ closeChainFiber mmWord mmFiber60DirectStates (3 + 61) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 3 61 [mmFiber60StateAt 0] (mmFiber60StateAt 14) h3

theorem mmFiber60State15_in_close :
    mmFiber60StateAt 15 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 3 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 3) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep3
  have h2 : mmFiber60StateAt 7 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 3) (mmFiber60StateAt 7) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep7
  have h3 : mmFiber60StateAt 15 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 7) (mmFiber60StateAt 15) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep15
  change mmFiber60StateAt 15 ∈ closeChainFiber mmWord mmFiber60DirectStates (3 + 61) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 3 61 [mmFiber60StateAt 0] (mmFiber60StateAt 15) h3

theorem mmFiber60State16_in_close :
    mmFiber60StateAt 16 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 8 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 8) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep8
  have h2 : mmFiber60StateAt 20 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 8) (mmFiber60StateAt 20) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep20
  have h3 : mmFiber60StateAt 16 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 20) (mmFiber60StateAt 16) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep16
  change mmFiber60StateAt 16 ∈ closeChainFiber mmWord mmFiber60DirectStates (3 + 61) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 3 61 [mmFiber60StateAt 0] (mmFiber60StateAt 16) h3

theorem mmFiber60State17_in_close :
    mmFiber60StateAt 17 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 1 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 1) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep1
  have h2 : mmFiber60StateAt 9 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 1) (mmFiber60StateAt 9) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep9
  have h3 : mmFiber60StateAt 21 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 9) (mmFiber60StateAt 21) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep21
  have h4 : mmFiber60StateAt 17 ∈ closeChainFiber mmWord mmFiber60DirectStates 4 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0]
      (mmFiber60StateAt 21) (mmFiber60StateAt 17) (by decide) h3 (by decide)
      mmFiber60ReverseSingleStep17
  change mmFiber60StateAt 17 ∈ closeChainFiber mmWord mmFiber60DirectStates (4 + 60) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 4 60 [mmFiber60StateAt 0] (mmFiber60StateAt 17) h4

theorem mmFiber60State18_in_close :
    mmFiber60StateAt 18 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 4 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 4) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep4
  have h2 : mmFiber60StateAt 12 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 4) (mmFiber60StateAt 12) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep12
  have h3 : mmFiber60StateAt 18 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 12) (mmFiber60StateAt 18) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep18
  change mmFiber60StateAt 18 ∈ closeChainFiber mmWord mmFiber60DirectStates (3 + 61) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 3 61 [mmFiber60StateAt 0] (mmFiber60StateAt 18) h3

theorem mmFiber60State19_in_close :
    mmFiber60StateAt 19 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 1 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 1) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep1
  have h2 : mmFiber60StateAt 5 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 1) (mmFiber60StateAt 5) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep5
  have h3 : mmFiber60StateAt 13 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 5) (mmFiber60StateAt 13) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep13
  have h4 : mmFiber60StateAt 19 ∈ closeChainFiber mmWord mmFiber60DirectStates 4 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0]
      (mmFiber60StateAt 13) (mmFiber60StateAt 19) (by decide) h3 (by decide)
      mmFiber60ReverseSingleStep19
  change mmFiber60StateAt 19 ∈ closeChainFiber mmWord mmFiber60DirectStates (4 + 60) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 4 60 [mmFiber60StateAt 0] (mmFiber60StateAt 19) h4

theorem mmFiber60State20_in_close :
    mmFiber60StateAt 20 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 8 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 8) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep8
  have h2 : mmFiber60StateAt 20 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 8) (mmFiber60StateAt 20) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep20
  change mmFiber60StateAt 20 ∈ closeChainFiber mmWord mmFiber60DirectStates (2 + 62) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 2 62 [mmFiber60StateAt 0] (mmFiber60StateAt 20) h2

theorem mmFiber60State21_in_close :
    mmFiber60StateAt 21 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 1 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 1) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep1
  have h2 : mmFiber60StateAt 9 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 1) (mmFiber60StateAt 9) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep9
  have h3 : mmFiber60StateAt 21 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 9) (mmFiber60StateAt 21) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep21
  change mmFiber60StateAt 21 ∈ closeChainFiber mmWord mmFiber60DirectStates (3 + 61) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 3 61 [mmFiber60StateAt 0] (mmFiber60StateAt 21) h3

theorem mmFiber60State22_in_close :
    mmFiber60StateAt 22 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 1 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 1) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep1
  have h2 : mmFiber60StateAt 2 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 1) (mmFiber60StateAt 2) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep2
  have h3 : mmFiber60StateAt 10 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 2) (mmFiber60StateAt 10) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep10
  have h4 : mmFiber60StateAt 22 ∈ closeChainFiber mmWord mmFiber60DirectStates 4 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0]
      (mmFiber60StateAt 10) (mmFiber60StateAt 22) (by decide) h3 (by decide)
      mmFiber60ReverseSingleStep22
  change mmFiber60StateAt 22 ∈ closeChainFiber mmWord mmFiber60DirectStates (4 + 60) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 4 60 [mmFiber60StateAt 0] (mmFiber60StateAt 22) h4

theorem mmFiber60State23_in_close :
    mmFiber60StateAt 23 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 3 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 3) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep3
  have h2 : mmFiber60StateAt 11 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 3) (mmFiber60StateAt 11) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep11
  have h3 : mmFiber60StateAt 23 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 11) (mmFiber60StateAt 23) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep23
  change mmFiber60StateAt 23 ∈ closeChainFiber mmWord mmFiber60DirectStates (3 + 61) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 3 61 [mmFiber60StateAt 0] (mmFiber60StateAt 23) h3

theorem mmFiber60State24_in_close :
    mmFiber60StateAt 24 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 28 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 28) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep28
  have h2 : mmFiber60StateAt 24 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 28) (mmFiber60StateAt 24) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep24
  change mmFiber60StateAt 24 ∈ closeChainFiber mmWord mmFiber60DirectStates (2 + 62) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 2 62 [mmFiber60StateAt 0] (mmFiber60StateAt 24) h2

theorem mmFiber60State25_in_close :
    mmFiber60StateAt 25 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 1 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 1) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep1
  have h2 : mmFiber60StateAt 29 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 1) (mmFiber60StateAt 29) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep29
  have h3 : mmFiber60StateAt 25 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 29) (mmFiber60StateAt 25) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep25
  change mmFiber60StateAt 25 ∈ closeChainFiber mmWord mmFiber60DirectStates (3 + 61) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 3 61 [mmFiber60StateAt 0] (mmFiber60StateAt 25) h3

theorem mmFiber60State26_in_close :
    mmFiber60StateAt 26 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 4 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 4) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep4
  have h2 : mmFiber60StateAt 26 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 4) (mmFiber60StateAt 26) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep26
  change mmFiber60StateAt 26 ∈ closeChainFiber mmWord mmFiber60DirectStates (2 + 62) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 2 62 [mmFiber60StateAt 0] (mmFiber60StateAt 26) h2

theorem mmFiber60State27_in_close :
    mmFiber60StateAt 27 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 1 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 1) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep1
  have h2 : mmFiber60StateAt 5 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 1) (mmFiber60StateAt 5) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep5
  have h3 : mmFiber60StateAt 27 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 5) (mmFiber60StateAt 27) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep27
  change mmFiber60StateAt 27 ∈ closeChainFiber mmWord mmFiber60DirectStates (3 + 61) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 3 61 [mmFiber60StateAt 0] (mmFiber60StateAt 27) h3

theorem mmFiber60State28_in_close :
    mmFiber60StateAt 28 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 28 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 28) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep28
  change mmFiber60StateAt 28 ∈ closeChainFiber mmWord mmFiber60DirectStates (1 + 63) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 1 63 [mmFiber60StateAt 0] (mmFiber60StateAt 28) h1

theorem mmFiber60State29_in_close :
    mmFiber60StateAt 29 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 1 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 1) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep1
  have h2 : mmFiber60StateAt 29 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 1) (mmFiber60StateAt 29) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep29
  change mmFiber60StateAt 29 ∈ closeChainFiber mmWord mmFiber60DirectStates (2 + 62) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 2 62 [mmFiber60StateAt 0] (mmFiber60StateAt 29) h2

theorem mmFiber60State30_in_close :
    mmFiber60StateAt 30 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 1 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 1) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep1
  have h2 : mmFiber60StateAt 2 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 1) (mmFiber60StateAt 2) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep2
  have h3 : mmFiber60StateAt 30 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 2) (mmFiber60StateAt 30) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep30
  change mmFiber60StateAt 30 ∈ closeChainFiber mmWord mmFiber60DirectStates (3 + 61) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 3 61 [mmFiber60StateAt 0] (mmFiber60StateAt 30) h3

theorem mmFiber60State31_in_close :
    mmFiber60StateAt 31 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 3 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 3) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep3
  have h2 : mmFiber60StateAt 31 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 3) (mmFiber60StateAt 31) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep31
  change mmFiber60StateAt 31 ∈ closeChainFiber mmWord mmFiber60DirectStates (2 + 62) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 2 62 [mmFiber60StateAt 0] (mmFiber60StateAt 31) h2

theorem mmFiber60State32_in_close :
    mmFiber60StateAt 32 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 32 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 32) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep32
  change mmFiber60StateAt 32 ∈ closeChainFiber mmWord mmFiber60DirectStates (1 + 63) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 1 63 [mmFiber60StateAt 0] (mmFiber60StateAt 32) h1

theorem mmFiber60State33_in_close :
    mmFiber60StateAt 33 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 1 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 1) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep1
  have h2 : mmFiber60StateAt 33 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 1) (mmFiber60StateAt 33) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep33
  change mmFiber60StateAt 33 ∈ closeChainFiber mmWord mmFiber60DirectStates (2 + 62) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 2 62 [mmFiber60StateAt 0] (mmFiber60StateAt 33) h2

theorem mmFiber60State34_in_close :
    mmFiber60StateAt 34 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 1 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 1) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep1
  have h2 : mmFiber60StateAt 2 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 1) (mmFiber60StateAt 2) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep2
  have h3 : mmFiber60StateAt 34 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 2) (mmFiber60StateAt 34) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep34
  change mmFiber60StateAt 34 ∈ closeChainFiber mmWord mmFiber60DirectStates (3 + 61) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 3 61 [mmFiber60StateAt 0] (mmFiber60StateAt 34) h3

theorem mmFiber60State35_in_close :
    mmFiber60StateAt 35 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 3 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 3) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep3
  have h2 : mmFiber60StateAt 35 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 3) (mmFiber60StateAt 35) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep35
  change mmFiber60StateAt 35 ∈ closeChainFiber mmWord mmFiber60DirectStates (2 + 62) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 2 62 [mmFiber60StateAt 0] (mmFiber60StateAt 35) h2

theorem mmFiber60State36_in_close :
    mmFiber60StateAt 36 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 4 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 4) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep4
  have h2 : mmFiber60StateAt 36 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 4) (mmFiber60StateAt 36) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep36
  change mmFiber60StateAt 36 ∈ closeChainFiber mmWord mmFiber60DirectStates (2 + 62) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 2 62 [mmFiber60StateAt 0] (mmFiber60StateAt 36) h2

theorem mmFiber60State37_in_close :
    mmFiber60StateAt 37 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 1 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 1) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep1
  have h2 : mmFiber60StateAt 5 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 1) (mmFiber60StateAt 5) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep5
  have h3 : mmFiber60StateAt 37 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 5) (mmFiber60StateAt 37) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep37
  change mmFiber60StateAt 37 ∈ closeChainFiber mmWord mmFiber60DirectStates (3 + 61) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 3 61 [mmFiber60StateAt 0] (mmFiber60StateAt 37) h3

theorem mmFiber60State38_in_close :
    mmFiber60StateAt 38 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 4 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 4) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep4
  have h2 : mmFiber60StateAt 6 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 4) (mmFiber60StateAt 6) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep6
  have h3 : mmFiber60StateAt 38 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 6) (mmFiber60StateAt 38) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep38
  change mmFiber60StateAt 38 ∈ closeChainFiber mmWord mmFiber60DirectStates (3 + 61) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 3 61 [mmFiber60StateAt 0] (mmFiber60StateAt 38) h3

theorem mmFiber60State39_in_close :
    mmFiber60StateAt 39 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 3 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 3) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep3
  have h2 : mmFiber60StateAt 7 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 3) (mmFiber60StateAt 7) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep7
  have h3 : mmFiber60StateAt 39 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 7) (mmFiber60StateAt 39) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep39
  change mmFiber60StateAt 39 ∈ closeChainFiber mmWord mmFiber60DirectStates (3 + 61) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 3 61 [mmFiber60StateAt 0] (mmFiber60StateAt 39) h3

theorem mmFiber60State40_in_close :
    mmFiber60StateAt 40 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 8 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 8) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep8
  have h2 : mmFiber60StateAt 40 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 8) (mmFiber60StateAt 40) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep40
  change mmFiber60StateAt 40 ∈ closeChainFiber mmWord mmFiber60DirectStates (2 + 62) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 2 62 [mmFiber60StateAt 0] (mmFiber60StateAt 40) h2

theorem mmFiber60State41_in_close :
    mmFiber60StateAt 41 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 1 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 1) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep1
  have h2 : mmFiber60StateAt 9 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 1) (mmFiber60StateAt 9) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep9
  have h3 : mmFiber60StateAt 41 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 9) (mmFiber60StateAt 41) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep41
  change mmFiber60StateAt 41 ∈ closeChainFiber mmWord mmFiber60DirectStates (3 + 61) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 3 61 [mmFiber60StateAt 0] (mmFiber60StateAt 41) h3

theorem mmFiber60State42_in_close :
    mmFiber60StateAt 42 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 1 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 1) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep1
  have h2 : mmFiber60StateAt 2 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 1) (mmFiber60StateAt 2) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep2
  have h3 : mmFiber60StateAt 10 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 2) (mmFiber60StateAt 10) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep10
  have h4 : mmFiber60StateAt 42 ∈ closeChainFiber mmWord mmFiber60DirectStates 4 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0]
      (mmFiber60StateAt 10) (mmFiber60StateAt 42) (by decide) h3 (by decide)
      mmFiber60ReverseSingleStep42
  change mmFiber60StateAt 42 ∈ closeChainFiber mmWord mmFiber60DirectStates (4 + 60) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 4 60 [mmFiber60StateAt 0] (mmFiber60StateAt 42) h4

theorem mmFiber60State43_in_close :
    mmFiber60StateAt 43 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 3 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 3) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep3
  have h2 : mmFiber60StateAt 11 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 3) (mmFiber60StateAt 11) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep11
  have h3 : mmFiber60StateAt 43 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 11) (mmFiber60StateAt 43) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep43
  change mmFiber60StateAt 43 ∈ closeChainFiber mmWord mmFiber60DirectStates (3 + 61) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 3 61 [mmFiber60StateAt 0] (mmFiber60StateAt 43) h3

theorem mmFiber60State44_in_close :
    mmFiber60StateAt 44 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 4 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 4) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep4
  have h2 : mmFiber60StateAt 12 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 4) (mmFiber60StateAt 12) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep12
  have h3 : mmFiber60StateAt 44 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 12) (mmFiber60StateAt 44) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep44
  change mmFiber60StateAt 44 ∈ closeChainFiber mmWord mmFiber60DirectStates (3 + 61) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 3 61 [mmFiber60StateAt 0] (mmFiber60StateAt 44) h3

theorem mmFiber60State45_in_close :
    mmFiber60StateAt 45 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 1 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 1) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep1
  have h2 : mmFiber60StateAt 5 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 1) (mmFiber60StateAt 5) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep5
  have h3 : mmFiber60StateAt 13 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 5) (mmFiber60StateAt 13) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep13
  have h4 : mmFiber60StateAt 45 ∈ closeChainFiber mmWord mmFiber60DirectStates 4 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0]
      (mmFiber60StateAt 13) (mmFiber60StateAt 45) (by decide) h3 (by decide)
      mmFiber60ReverseSingleStep45
  change mmFiber60StateAt 45 ∈ closeChainFiber mmWord mmFiber60DirectStates (4 + 60) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 4 60 [mmFiber60StateAt 0] (mmFiber60StateAt 45) h4

theorem mmFiber60State46_in_close :
    mmFiber60StateAt 46 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 4 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 4) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep4
  have h2 : mmFiber60StateAt 6 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 4) (mmFiber60StateAt 6) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep6
  have h3 : mmFiber60StateAt 14 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 6) (mmFiber60StateAt 14) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep14
  have h4 : mmFiber60StateAt 46 ∈ closeChainFiber mmWord mmFiber60DirectStates 4 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0]
      (mmFiber60StateAt 14) (mmFiber60StateAt 46) (by decide) h3 (by decide)
      mmFiber60ReverseSingleStep46
  change mmFiber60StateAt 46 ∈ closeChainFiber mmWord mmFiber60DirectStates (4 + 60) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 4 60 [mmFiber60StateAt 0] (mmFiber60StateAt 46) h4

theorem mmFiber60State47_in_close :
    mmFiber60StateAt 47 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 3 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 3) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep3
  have h2 : mmFiber60StateAt 7 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 3) (mmFiber60StateAt 7) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep7
  have h3 : mmFiber60StateAt 15 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 7) (mmFiber60StateAt 15) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep15
  have h4 : mmFiber60StateAt 47 ∈ closeChainFiber mmWord mmFiber60DirectStates 4 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0]
      (mmFiber60StateAt 15) (mmFiber60StateAt 47) (by decide) h3 (by decide)
      mmFiber60ReverseSingleStep47
  change mmFiber60StateAt 47 ∈ closeChainFiber mmWord mmFiber60DirectStates (4 + 60) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 4 60 [mmFiber60StateAt 0] (mmFiber60StateAt 47) h4

theorem mmFiber60State48_in_close :
    mmFiber60StateAt 48 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 32 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 32) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep32
  have h2 : mmFiber60StateAt 48 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 32) (mmFiber60StateAt 48) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep48
  change mmFiber60StateAt 48 ∈ closeChainFiber mmWord mmFiber60DirectStates (2 + 62) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 2 62 [mmFiber60StateAt 0] (mmFiber60StateAt 48) h2

theorem mmFiber60State49_in_close :
    mmFiber60StateAt 49 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 1 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 1) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep1
  have h2 : mmFiber60StateAt 33 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 1) (mmFiber60StateAt 33) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep33
  have h3 : mmFiber60StateAt 49 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 33) (mmFiber60StateAt 49) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep49
  change mmFiber60StateAt 49 ∈ closeChainFiber mmWord mmFiber60DirectStates (3 + 61) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 3 61 [mmFiber60StateAt 0] (mmFiber60StateAt 49) h3

theorem mmFiber60State50_in_close :
    mmFiber60StateAt 50 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 32 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 32) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep32
  have h2 : mmFiber60StateAt 48 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 32) (mmFiber60StateAt 48) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep48
  have h3 : mmFiber60StateAt 50 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 48) (mmFiber60StateAt 50) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep50
  change mmFiber60StateAt 50 ∈ closeChainFiber mmWord mmFiber60DirectStates (3 + 61) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 3 61 [mmFiber60StateAt 0] (mmFiber60StateAt 50) h3

theorem mmFiber60State51_in_close :
    mmFiber60StateAt 51 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 3 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 3) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep3
  have h2 : mmFiber60StateAt 35 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 3) (mmFiber60StateAt 35) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep35
  have h3 : mmFiber60StateAt 51 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 35) (mmFiber60StateAt 51) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep51
  change mmFiber60StateAt 51 ∈ closeChainFiber mmWord mmFiber60DirectStates (3 + 61) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 3 61 [mmFiber60StateAt 0] (mmFiber60StateAt 51) h3

theorem mmFiber60State52_in_close :
    mmFiber60StateAt 52 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 4 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 4) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep4
  have h2 : mmFiber60StateAt 36 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 4) (mmFiber60StateAt 36) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep36
  have h3 : mmFiber60StateAt 52 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 36) (mmFiber60StateAt 52) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep52
  change mmFiber60StateAt 52 ∈ closeChainFiber mmWord mmFiber60DirectStates (3 + 61) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 3 61 [mmFiber60StateAt 0] (mmFiber60StateAt 52) h3

theorem mmFiber60State53_in_close :
    mmFiber60StateAt 53 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 1 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 1) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep1
  have h2 : mmFiber60StateAt 5 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 1) (mmFiber60StateAt 5) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep5
  have h3 : mmFiber60StateAt 37 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 5) (mmFiber60StateAt 37) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep37
  have h4 : mmFiber60StateAt 53 ∈ closeChainFiber mmWord mmFiber60DirectStates 4 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0]
      (mmFiber60StateAt 37) (mmFiber60StateAt 53) (by decide) h3 (by decide)
      mmFiber60ReverseSingleStep53
  change mmFiber60StateAt 53 ∈ closeChainFiber mmWord mmFiber60DirectStates (4 + 60) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 4 60 [mmFiber60StateAt 0] (mmFiber60StateAt 53) h4

theorem mmFiber60State54_in_close :
    mmFiber60StateAt 54 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 1 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 1) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep1
  have h2 : mmFiber60StateAt 33 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 1) (mmFiber60StateAt 33) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep33
  have h3 : mmFiber60StateAt 49 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 33) (mmFiber60StateAt 49) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep49
  have h4 : mmFiber60StateAt 54 ∈ closeChainFiber mmWord mmFiber60DirectStates 4 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0]
      (mmFiber60StateAt 49) (mmFiber60StateAt 54) (by decide) h3 (by decide)
      mmFiber60ReverseSingleStep54
  change mmFiber60StateAt 54 ∈ closeChainFiber mmWord mmFiber60DirectStates (4 + 60) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 4 60 [mmFiber60StateAt 0] (mmFiber60StateAt 54) h4

theorem mmFiber60State55_in_close :
    mmFiber60StateAt 55 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 32 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 32) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep32
  have h2 : mmFiber60StateAt 48 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 32) (mmFiber60StateAt 48) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep48
  have h3 : mmFiber60StateAt 55 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 48) (mmFiber60StateAt 55) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep55
  change mmFiber60StateAt 55 ∈ closeChainFiber mmWord mmFiber60DirectStates (3 + 61) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 3 61 [mmFiber60StateAt 0] (mmFiber60StateAt 55) h3

theorem mmFiber60State56_in_close :
    mmFiber60StateAt 56 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 8 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 8) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep8
  have h2 : mmFiber60StateAt 40 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 8) (mmFiber60StateAt 40) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep40
  have h3 : mmFiber60StateAt 56 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 40) (mmFiber60StateAt 56) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep56
  change mmFiber60StateAt 56 ∈ closeChainFiber mmWord mmFiber60DirectStates (3 + 61) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 3 61 [mmFiber60StateAt 0] (mmFiber60StateAt 56) h3

theorem mmFiber60State57_in_close :
    mmFiber60StateAt 57 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 1 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 1) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep1
  have h2 : mmFiber60StateAt 9 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 1) (mmFiber60StateAt 9) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep9
  have h3 : mmFiber60StateAt 41 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 9) (mmFiber60StateAt 41) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep41
  have h4 : mmFiber60StateAt 57 ∈ closeChainFiber mmWord mmFiber60DirectStates 4 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0]
      (mmFiber60StateAt 41) (mmFiber60StateAt 57) (by decide) h3 (by decide)
      mmFiber60ReverseSingleStep57
  change mmFiber60StateAt 57 ∈ closeChainFiber mmWord mmFiber60DirectStates (4 + 60) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 4 60 [mmFiber60StateAt 0] (mmFiber60StateAt 57) h4

theorem mmFiber60State58_in_close :
    mmFiber60StateAt 58 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 4 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 4) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep4
  have h2 : mmFiber60StateAt 26 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 4) (mmFiber60StateAt 26) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep26
  have h3 : mmFiber60StateAt 58 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 26) (mmFiber60StateAt 58) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep58
  change mmFiber60StateAt 58 ∈ closeChainFiber mmWord mmFiber60DirectStates (3 + 61) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 3 61 [mmFiber60StateAt 0] (mmFiber60StateAt 58) h3

theorem mmFiber60State59_in_close :
    mmFiber60StateAt 59 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 1 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 1) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep1
  have h2 : mmFiber60StateAt 5 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 1) (mmFiber60StateAt 5) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep5
  have h3 : mmFiber60StateAt 27 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 5) (mmFiber60StateAt 27) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep27
  have h4 : mmFiber60StateAt 59 ∈ closeChainFiber mmWord mmFiber60DirectStates 4 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0]
      (mmFiber60StateAt 27) (mmFiber60StateAt 59) (by decide) h3 (by decide)
      mmFiber60ReverseSingleStep59
  change mmFiber60StateAt 59 ∈ closeChainFiber mmWord mmFiber60DirectStates (4 + 60) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 4 60 [mmFiber60StateAt 0] (mmFiber60StateAt 59) h4

theorem mmFiber60State60_in_close :
    mmFiber60StateAt 60 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 28 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 28) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep28
  have h2 : mmFiber60StateAt 60 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 28) (mmFiber60StateAt 60) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep60
  change mmFiber60StateAt 60 ∈ closeChainFiber mmWord mmFiber60DirectStates (2 + 62) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 2 62 [mmFiber60StateAt 0] (mmFiber60StateAt 60) h2

theorem mmFiber60State61_in_close :
    mmFiber60StateAt 61 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 1 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 1) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep1
  have h2 : mmFiber60StateAt 29 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 1) (mmFiber60StateAt 29) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep29
  have h3 : mmFiber60StateAt 61 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 29) (mmFiber60StateAt 61) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep61
  change mmFiber60StateAt 61 ∈ closeChainFiber mmWord mmFiber60DirectStates (3 + 61) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 3 61 [mmFiber60StateAt 0] (mmFiber60StateAt 61) h3

theorem mmFiber60State62_in_close :
    mmFiber60StateAt 62 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 28 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 28) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep28
  have h2 : mmFiber60StateAt 60 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 28) (mmFiber60StateAt 60) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep60
  have h3 : mmFiber60StateAt 62 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 60) (mmFiber60StateAt 62) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep62
  change mmFiber60StateAt 62 ∈ closeChainFiber mmWord mmFiber60DirectStates (3 + 61) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 3 61 [mmFiber60StateAt 0] (mmFiber60StateAt 62) h3

theorem mmFiber60State63_in_close :
    mmFiber60StateAt 63 ∈ closeChainFiber mmWord mmFiber60DirectStates mmFiber60DirectStates.length [mmFiber60StateAt 0] := by
  have h0 : mmFiber60StateAt 0 ∈ closeChainFiber mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber60StateAt 3 ∈ closeChainFiber mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 0 [mmFiber60StateAt 0]
      (mmFiber60StateAt 0) (mmFiber60StateAt 3) (by decide) h0 (by decide)
      mmFiber60ReverseSingleStep3
  have h2 : mmFiber60StateAt 31 ∈ closeChainFiber mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 1 [mmFiber60StateAt 0]
      (mmFiber60StateAt 3) (mmFiber60StateAt 31) (by decide) h1 (by decide)
      mmFiber60ReverseSingleStep31
  have h3 : mmFiber60StateAt 63 ∈ closeChainFiber mmWord mmFiber60DirectStates 3 [mmFiber60StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber60DirectStates 2 [mmFiber60StateAt 0]
      (mmFiber60StateAt 31) (mmFiber60StateAt 63) (by decide) h2 (by decide)
      mmFiber60ReverseSingleStep63
  change mmFiber60StateAt 63 ∈ closeChainFiber mmWord mmFiber60DirectStates (3 + 61) [mmFiber60StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber60DirectStates 3 61 [mmFiber60StateAt 0] (mmFiber60StateAt 63) h3

theorem mmFiber60DirectConnected :
    chainFiberConnected mmWord mmFiber60DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber60DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber60State0_in_close
  · subst state
    exact mmFiber60State1_in_close
  · subst state
    exact mmFiber60State2_in_close
  · subst state
    exact mmFiber60State3_in_close
  · subst state
    exact mmFiber60State4_in_close
  · subst state
    exact mmFiber60State5_in_close
  · subst state
    exact mmFiber60State6_in_close
  · subst state
    exact mmFiber60State7_in_close
  · subst state
    exact mmFiber60State8_in_close
  · subst state
    exact mmFiber60State9_in_close
  · subst state
    exact mmFiber60State10_in_close
  · subst state
    exact mmFiber60State11_in_close
  · subst state
    exact mmFiber60State12_in_close
  · subst state
    exact mmFiber60State13_in_close
  · subst state
    exact mmFiber60State14_in_close
  · subst state
    exact mmFiber60State15_in_close
  · subst state
    exact mmFiber60State16_in_close
  · subst state
    exact mmFiber60State17_in_close
  · subst state
    exact mmFiber60State18_in_close
  · subst state
    exact mmFiber60State19_in_close
  · subst state
    exact mmFiber60State20_in_close
  · subst state
    exact mmFiber60State21_in_close
  · subst state
    exact mmFiber60State22_in_close
  · subst state
    exact mmFiber60State23_in_close
  · subst state
    exact mmFiber60State24_in_close
  · subst state
    exact mmFiber60State25_in_close
  · subst state
    exact mmFiber60State26_in_close
  · subst state
    exact mmFiber60State27_in_close
  · subst state
    exact mmFiber60State28_in_close
  · subst state
    exact mmFiber60State29_in_close
  · subst state
    exact mmFiber60State30_in_close
  · subst state
    exact mmFiber60State31_in_close
  · subst state
    exact mmFiber60State32_in_close
  · subst state
    exact mmFiber60State33_in_close
  · subst state
    exact mmFiber60State34_in_close
  · subst state
    exact mmFiber60State35_in_close
  · subst state
    exact mmFiber60State36_in_close
  · subst state
    exact mmFiber60State37_in_close
  · subst state
    exact mmFiber60State38_in_close
  · subst state
    exact mmFiber60State39_in_close
  · subst state
    exact mmFiber60State40_in_close
  · subst state
    exact mmFiber60State41_in_close
  · subst state
    exact mmFiber60State42_in_close
  · subst state
    exact mmFiber60State43_in_close
  · subst state
    exact mmFiber60State44_in_close
  · subst state
    exact mmFiber60State45_in_close
  · subst state
    exact mmFiber60State46_in_close
  · subst state
    exact mmFiber60State47_in_close
  · subst state
    exact mmFiber60State48_in_close
  · subst state
    exact mmFiber60State49_in_close
  · subst state
    exact mmFiber60State50_in_close
  · subst state
    exact mmFiber60State51_in_close
  · subst state
    exact mmFiber60State52_in_close
  · subst state
    exact mmFiber60State53_in_close
  · subst state
    exact mmFiber60State54_in_close
  · subst state
    exact mmFiber60State55_in_close
  · subst state
    exact mmFiber60State56_in_close
  · subst state
    exact mmFiber60State57_in_close
  · subst state
    exact mmFiber60State58_in_close
  · subst state
    exact mmFiber60State59_in_close
  · subst state
    exact mmFiber60State60_in_close
  · subst state
    exact mmFiber60State61_in_close
  · subst state
    exact mmFiber60State62_in_close
  · subst state
    exact mmFiber60State63_in_close
  · cases h
end GoertzelLemma818LengthTwoMMBridge

end Mettapedia.GraphTheory.FourColor
