import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for `mirror,mirror` size-64 fiber 76

This module proves direct connectedness for one generated size-64 fiber from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMMBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorMirrorCertificate
open GoertzelLemma818MirrorMirrorReverseAudit

def mmFiber76StateAt (i : Nat) : List TauState :=
  directStates (mmFiber76RowAt i).sourceLeft (mmFiber76RowAt i).sourceRight

def mmFiber76DirectStates : List (List TauState) :=
  [mmFiber76StateAt 0, mmFiber76StateAt 1, mmFiber76StateAt 2, mmFiber76StateAt 3, mmFiber76StateAt 4, mmFiber76StateAt 5, mmFiber76StateAt 6, mmFiber76StateAt 7, mmFiber76StateAt 8, mmFiber76StateAt 9, mmFiber76StateAt 10, mmFiber76StateAt 11, mmFiber76StateAt 12, mmFiber76StateAt 13, mmFiber76StateAt 14, mmFiber76StateAt 15, mmFiber76StateAt 16, mmFiber76StateAt 17, mmFiber76StateAt 18, mmFiber76StateAt 19, mmFiber76StateAt 20, mmFiber76StateAt 21, mmFiber76StateAt 22, mmFiber76StateAt 23, mmFiber76StateAt 24, mmFiber76StateAt 25, mmFiber76StateAt 26, mmFiber76StateAt 27, mmFiber76StateAt 28, mmFiber76StateAt 29, mmFiber76StateAt 30, mmFiber76StateAt 31, mmFiber76StateAt 32, mmFiber76StateAt 33, mmFiber76StateAt 34, mmFiber76StateAt 35, mmFiber76StateAt 36, mmFiber76StateAt 37, mmFiber76StateAt 38, mmFiber76StateAt 39, mmFiber76StateAt 40, mmFiber76StateAt 41, mmFiber76StateAt 42, mmFiber76StateAt 43, mmFiber76StateAt 44, mmFiber76StateAt 45, mmFiber76StateAt 46, mmFiber76StateAt 47, mmFiber76StateAt 48, mmFiber76StateAt 49, mmFiber76StateAt 50, mmFiber76StateAt 51, mmFiber76StateAt 52, mmFiber76StateAt 53, mmFiber76StateAt 54, mmFiber76StateAt 55, mmFiber76StateAt 56, mmFiber76StateAt 57, mmFiber76StateAt 58, mmFiber76StateAt 59, mmFiber76StateAt 60, mmFiber76StateAt 61, mmFiber76StateAt 62, mmFiber76StateAt 63]

theorem mmFiber76ReverseRow_1_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk0_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 0) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 0) (mmFiber76StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 0) (mmFiber76StateAt 1)
    (mmFiber76RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 1) (by decide) mmFiber76ReverseRow_1_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_2_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk1_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 2) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber76ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 1) (mmFiber76StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 1) (mmFiber76StateAt 2)
    (mmFiber76RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 2) (by decide) mmFiber76ReverseRow_2_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_3_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk1_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 2) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 0) (mmFiber76StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 0) (mmFiber76StateAt 3)
    (mmFiber76RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 3) (by decide) mmFiber76ReverseRow_3_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_4_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk2_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 4) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber76ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 0) (mmFiber76StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 0) (mmFiber76StateAt 4)
    (mmFiber76RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 4) (by decide) mmFiber76ReverseRow_4_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_5_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk2_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 4) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 1) (mmFiber76StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 1) (mmFiber76StateAt 5)
    (mmFiber76RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 5) (by decide) mmFiber76ReverseRow_5_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_6_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk3_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 6) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber76ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 4) (mmFiber76StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 4) (mmFiber76StateAt 6)
    (mmFiber76RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 6) (by decide) mmFiber76ReverseRow_6_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_7_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk3_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 6) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 3) (mmFiber76StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 3) (mmFiber76StateAt 7)
    (mmFiber76RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 7) (by decide) mmFiber76ReverseRow_7_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_8_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 8) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk4_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 8) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber76ReverseSingleStep8 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 0) (mmFiber76StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 0) (mmFiber76StateAt 8)
    (mmFiber76RowAt 8).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 8) (by decide) mmFiber76ReverseRow_8_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_9_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 9) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk4_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 8) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep9 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 1) (mmFiber76StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 1) (mmFiber76StateAt 9)
    (mmFiber76RowAt 9).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 9) (by decide) mmFiber76ReverseRow_9_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_10_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 10) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk5_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 10) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber76ReverseSingleStep10 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 2) (mmFiber76StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 2) (mmFiber76StateAt 10)
    (mmFiber76RowAt 10).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 10) (by decide) mmFiber76ReverseRow_10_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_11_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 11) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk5_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 10) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep11 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 3) (mmFiber76StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 3) (mmFiber76StateAt 11)
    (mmFiber76RowAt 11).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 11) (by decide) mmFiber76ReverseRow_11_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_12_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 12) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk6_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 12) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber76ReverseSingleStep12 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 4) (mmFiber76StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 4) (mmFiber76StateAt 12)
    (mmFiber76RowAt 12).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 12) (by decide) mmFiber76ReverseRow_12_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_13_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 13) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk6_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 12) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep13 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 5) (mmFiber76StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 5) (mmFiber76StateAt 13)
    (mmFiber76RowAt 13).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 13) (by decide) mmFiber76ReverseRow_13_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_14_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 14) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk7_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 14) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber76ReverseSingleStep14 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 6) (mmFiber76StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 6) (mmFiber76StateAt 14)
    (mmFiber76RowAt 14).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 14) (by decide) mmFiber76ReverseRow_14_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_15_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 15) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk7_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 14) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep15 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 7) (mmFiber76StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 7) (mmFiber76StateAt 15)
    (mmFiber76RowAt 15).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 15) (by decide) mmFiber76ReverseRow_15_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_16_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 16) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk8_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 16) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber76ReverseSingleStep16 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 20) (mmFiber76StateAt 16) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 20) (mmFiber76StateAt 16)
    (mmFiber76RowAt 16).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 16) (by decide) mmFiber76ReverseRow_16_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_17_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 17) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk8_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 16) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep17 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 21) (mmFiber76StateAt 17) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 21) (mmFiber76StateAt 17)
    (mmFiber76RowAt 17).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 17) (by decide) mmFiber76ReverseRow_17_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_18_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 18) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk9_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 18) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber76ReverseSingleStep18 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 12) (mmFiber76StateAt 18) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 12) (mmFiber76StateAt 18)
    (mmFiber76RowAt 18).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 18) (by decide) mmFiber76ReverseRow_18_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_19_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 19) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk9_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 18) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep19 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 13) (mmFiber76StateAt 19) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 13) (mmFiber76StateAt 19)
    (mmFiber76RowAt 19).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 19) (by decide) mmFiber76ReverseRow_19_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_20_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 20) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk10_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 20) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber76ReverseSingleStep20 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 8) (mmFiber76StateAt 20) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 8) (mmFiber76StateAt 20)
    (mmFiber76RowAt 20).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 20) (by decide) mmFiber76ReverseRow_20_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_21_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 21) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk10_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 20) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep21 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 9) (mmFiber76StateAt 21) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 9) (mmFiber76StateAt 21)
    (mmFiber76RowAt 21).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 21) (by decide) mmFiber76ReverseRow_21_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_22_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 22) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk11_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 22) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber76ReverseSingleStep22 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 10) (mmFiber76StateAt 22) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 10) (mmFiber76StateAt 22)
    (mmFiber76RowAt 22).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 22) (by decide) mmFiber76ReverseRow_22_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_23_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 23) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk11_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 22) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep23 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 11) (mmFiber76StateAt 23) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 11) (mmFiber76StateAt 23)
    (mmFiber76RowAt 23).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 23) (by decide) mmFiber76ReverseRow_23_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_24_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 24) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk12_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 24) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber76ReverseSingleStep24 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 28) (mmFiber76StateAt 24) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 28) (mmFiber76StateAt 24)
    (mmFiber76RowAt 24).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 24) (by decide) mmFiber76ReverseRow_24_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_25_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 25) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk12_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 24) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep25 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 29) (mmFiber76StateAt 25) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 29) (mmFiber76StateAt 25)
    (mmFiber76RowAt 25).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 25) (by decide) mmFiber76ReverseRow_25_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_26_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 26) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk13_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 26) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber76ReverseSingleStep26 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 4) (mmFiber76StateAt 26) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 4) (mmFiber76StateAt 26)
    (mmFiber76RowAt 26).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 26) (by decide) mmFiber76ReverseRow_26_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_27_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 27) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk13_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 26) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep27 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 5) (mmFiber76StateAt 27) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 5) (mmFiber76StateAt 27)
    (mmFiber76RowAt 27).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 27) (by decide) mmFiber76ReverseRow_27_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_28_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 28) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk14_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 28) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber76ReverseSingleStep28 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 0) (mmFiber76StateAt 28) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 0) (mmFiber76StateAt 28)
    (mmFiber76RowAt 28).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 28) (by decide) mmFiber76ReverseRow_28_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_29_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 29) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk14_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 28) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep29 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 1) (mmFiber76StateAt 29) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 1) (mmFiber76StateAt 29)
    (mmFiber76RowAt 29).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 29) (by decide) mmFiber76ReverseRow_29_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_30_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 30) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk15_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 30) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber76ReverseSingleStep30 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 2) (mmFiber76StateAt 30) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 2) (mmFiber76StateAt 30)
    (mmFiber76RowAt 30).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 30) (by decide) mmFiber76ReverseRow_30_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_31_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 31) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk15_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 30) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep31 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 3) (mmFiber76StateAt 31) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 3) (mmFiber76StateAt 31)
    (mmFiber76RowAt 31).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 31) (by decide) mmFiber76ReverseRow_31_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_32_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 32) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk16_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 32) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber76ReverseSingleStep32 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 0) (mmFiber76StateAt 32) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 0) (mmFiber76StateAt 32)
    (mmFiber76RowAt 32).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 32) (by decide) mmFiber76ReverseRow_32_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_33_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 33) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk16_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 32) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep33 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 1) (mmFiber76StateAt 33) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 1) (mmFiber76StateAt 33)
    (mmFiber76RowAt 33).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 33) (by decide) mmFiber76ReverseRow_33_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_34_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 34) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk17_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 34) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber76ReverseSingleStep34 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 2) (mmFiber76StateAt 34) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 2) (mmFiber76StateAt 34)
    (mmFiber76RowAt 34).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 34) (by decide) mmFiber76ReverseRow_34_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_35_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 35) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk17_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 34) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep35 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 3) (mmFiber76StateAt 35) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 3) (mmFiber76StateAt 35)
    (mmFiber76RowAt 35).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 35) (by decide) mmFiber76ReverseRow_35_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_36_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 36) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk18_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 36) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber76ReverseSingleStep36 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 4) (mmFiber76StateAt 36) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 4) (mmFiber76StateAt 36)
    (mmFiber76RowAt 36).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 36) (by decide) mmFiber76ReverseRow_36_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_37_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 37) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk18_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 36) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep37 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 5) (mmFiber76StateAt 37) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 5) (mmFiber76StateAt 37)
    (mmFiber76RowAt 37).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 37) (by decide) mmFiber76ReverseRow_37_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_38_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 38) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk19_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 38) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber76ReverseSingleStep38 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 6) (mmFiber76StateAt 38) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 6) (mmFiber76StateAt 38)
    (mmFiber76RowAt 38).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 38) (by decide) mmFiber76ReverseRow_38_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_39_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 39) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk19_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 38) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep39 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 7) (mmFiber76StateAt 39) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 7) (mmFiber76StateAt 39)
    (mmFiber76RowAt 39).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 39) (by decide) mmFiber76ReverseRow_39_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_40_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 40) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk20_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 40) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber76ReverseSingleStep40 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 8) (mmFiber76StateAt 40) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 8) (mmFiber76StateAt 40)
    (mmFiber76RowAt 40).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 40) (by decide) mmFiber76ReverseRow_40_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_41_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 41) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk20_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 40) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep41 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 9) (mmFiber76StateAt 41) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 9) (mmFiber76StateAt 41)
    (mmFiber76RowAt 41).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 41) (by decide) mmFiber76ReverseRow_41_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_42_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 42) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk21_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 42) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber76ReverseSingleStep42 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 10) (mmFiber76StateAt 42) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 10) (mmFiber76StateAt 42)
    (mmFiber76RowAt 42).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 42) (by decide) mmFiber76ReverseRow_42_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_43_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 43) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk21_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 42) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep43 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 11) (mmFiber76StateAt 43) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 11) (mmFiber76StateAt 43)
    (mmFiber76RowAt 43).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 43) (by decide) mmFiber76ReverseRow_43_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_44_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 44) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk22_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 44) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber76ReverseSingleStep44 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 12) (mmFiber76StateAt 44) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 12) (mmFiber76StateAt 44)
    (mmFiber76RowAt 44).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 44) (by decide) mmFiber76ReverseRow_44_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_45_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 45) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk22_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 44) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep45 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 13) (mmFiber76StateAt 45) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 13) (mmFiber76StateAt 45)
    (mmFiber76RowAt 45).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 45) (by decide) mmFiber76ReverseRow_45_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_46_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 46) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk23_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 46) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber76ReverseSingleStep46 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 14) (mmFiber76StateAt 46) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 14) (mmFiber76StateAt 46)
    (mmFiber76RowAt 46).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 46) (by decide) mmFiber76ReverseRow_46_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_47_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 47) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk23_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 46) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep47 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 15) (mmFiber76StateAt 47) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 15) (mmFiber76StateAt 47)
    (mmFiber76RowAt 47).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 47) (by decide) mmFiber76ReverseRow_47_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_48_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 48) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk24_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 48) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber76ReverseSingleStep48 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 32) (mmFiber76StateAt 48) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 32) (mmFiber76StateAt 48)
    (mmFiber76RowAt 48).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 48) (by decide) mmFiber76ReverseRow_48_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_49_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 49) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk24_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 48) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep49 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 33) (mmFiber76StateAt 49) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 33) (mmFiber76StateAt 49)
    (mmFiber76RowAt 49).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 49) (by decide) mmFiber76ReverseRow_49_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_50_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 50) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk25_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 50) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber76ReverseSingleStep50 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 48) (mmFiber76StateAt 50) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 48) (mmFiber76StateAt 50)
    (mmFiber76RowAt 50).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 50) (by decide) mmFiber76ReverseRow_50_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_51_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 51) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk25_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 50) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep51 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 35) (mmFiber76StateAt 51) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 35) (mmFiber76StateAt 51)
    (mmFiber76RowAt 51).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 51) (by decide) mmFiber76ReverseRow_51_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_52_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 52) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk26_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 52) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber76ReverseSingleStep52 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 36) (mmFiber76StateAt 52) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 36) (mmFiber76StateAt 52)
    (mmFiber76RowAt 52).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 52) (by decide) mmFiber76ReverseRow_52_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_53_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 53) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk26_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 52) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep53 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 37) (mmFiber76StateAt 53) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 37) (mmFiber76StateAt 53)
    (mmFiber76RowAt 53).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 53) (by decide) mmFiber76ReverseRow_53_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_54_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 54) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk27_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 54) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber76ReverseSingleStep54 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 49) (mmFiber76StateAt 54) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 49) (mmFiber76StateAt 54)
    (mmFiber76RowAt 54).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 54) (by decide) mmFiber76ReverseRow_54_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_55_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 55) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk27_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 54) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep55 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 48) (mmFiber76StateAt 55) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 48) (mmFiber76StateAt 55)
    (mmFiber76RowAt 55).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 55) (by decide) mmFiber76ReverseRow_55_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_56_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 56) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk28_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 56) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber76ReverseSingleStep56 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 40) (mmFiber76StateAt 56) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 40) (mmFiber76StateAt 56)
    (mmFiber76RowAt 56).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 56) (by decide) mmFiber76ReverseRow_56_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_57_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 57) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk28_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 56) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep57 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 41) (mmFiber76StateAt 57) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 41) (mmFiber76StateAt 57)
    (mmFiber76RowAt 57).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 57) (by decide) mmFiber76ReverseRow_57_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_58_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 58) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk29_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 58) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber76ReverseSingleStep58 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 26) (mmFiber76StateAt 58) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 26) (mmFiber76StateAt 58)
    (mmFiber76RowAt 58).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 58) (by decide) mmFiber76ReverseRow_58_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_59_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 59) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk29_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 58) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep59 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 27) (mmFiber76StateAt 59) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 27) (mmFiber76StateAt 59)
    (mmFiber76RowAt 59).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 59) (by decide) mmFiber76ReverseRow_59_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_60_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 60) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk30_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 60) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber76ReverseSingleStep60 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 28) (mmFiber76StateAt 60) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 28) (mmFiber76StateAt 60)
    (mmFiber76RowAt 60).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 60) (by decide) mmFiber76ReverseRow_60_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_61_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 61) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk30_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 60) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep61 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 29) (mmFiber76StateAt 61) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 29) (mmFiber76StateAt 61)
    (mmFiber76RowAt 61).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 61) (by decide) mmFiber76ReverseRow_61_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_62_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 62) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk31_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 62) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber76ReverseSingleStep62 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 60) (mmFiber76StateAt 62) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 60) (mmFiber76StateAt 62)
    (mmFiber76RowAt 62).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 62) (by decide) mmFiber76ReverseRow_62_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76ReverseRow_63_ok :
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 63) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber76Chunk31_ok
  change (mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 62) &&
    mmRowReverseValid mmFiber76Key mmFiber76Expected (mmFiber76RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber76ReverseSingleStep63 :
    chainSingleKempeStep mmWord (mmFiber76StateAt 31) (mmFiber76StateAt 63) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber76StateAt 31) (mmFiber76StateAt 63)
    (mmFiber76RowAt 63).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber76Key mmFiber76Expected
        (mmFiber76RowAt 63) (by decide) mmFiber76ReverseRow_63_ok
      simpa [mmFiber76StateAt, mmFiber76RowAt, mmFiber76Rows, listGetD, directRow] using h)

theorem mmFiber76State0_in_close :
    mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  change mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 64 [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 0 64 [mmFiber76StateAt 0] (mmFiber76StateAt 0) (by simp [closeChainFiber])

theorem mmFiber76State1_in_close :
    mmFiber76StateAt 1 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 1 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 1) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep1
  change mmFiber76StateAt 1 ∈ closeChainFiber mmWord mmFiber76DirectStates (1 + 63) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 1 63 [mmFiber76StateAt 0] (mmFiber76StateAt 1) h1

theorem mmFiber76State2_in_close :
    mmFiber76StateAt 2 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 1 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 1) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep1
  have h2 : mmFiber76StateAt 2 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 1) (mmFiber76StateAt 2) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep2
  change mmFiber76StateAt 2 ∈ closeChainFiber mmWord mmFiber76DirectStates (2 + 62) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 2 62 [mmFiber76StateAt 0] (mmFiber76StateAt 2) h2

theorem mmFiber76State3_in_close :
    mmFiber76StateAt 3 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 3 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 3) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep3
  change mmFiber76StateAt 3 ∈ closeChainFiber mmWord mmFiber76DirectStates (1 + 63) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 1 63 [mmFiber76StateAt 0] (mmFiber76StateAt 3) h1

theorem mmFiber76State4_in_close :
    mmFiber76StateAt 4 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 4 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 4) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep4
  change mmFiber76StateAt 4 ∈ closeChainFiber mmWord mmFiber76DirectStates (1 + 63) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 1 63 [mmFiber76StateAt 0] (mmFiber76StateAt 4) h1

theorem mmFiber76State5_in_close :
    mmFiber76StateAt 5 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 1 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 1) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep1
  have h2 : mmFiber76StateAt 5 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 1) (mmFiber76StateAt 5) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep5
  change mmFiber76StateAt 5 ∈ closeChainFiber mmWord mmFiber76DirectStates (2 + 62) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 2 62 [mmFiber76StateAt 0] (mmFiber76StateAt 5) h2

theorem mmFiber76State6_in_close :
    mmFiber76StateAt 6 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 4 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 4) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep4
  have h2 : mmFiber76StateAt 6 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 4) (mmFiber76StateAt 6) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep6
  change mmFiber76StateAt 6 ∈ closeChainFiber mmWord mmFiber76DirectStates (2 + 62) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 2 62 [mmFiber76StateAt 0] (mmFiber76StateAt 6) h2

theorem mmFiber76State7_in_close :
    mmFiber76StateAt 7 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 3 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 3) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep3
  have h2 : mmFiber76StateAt 7 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 3) (mmFiber76StateAt 7) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep7
  change mmFiber76StateAt 7 ∈ closeChainFiber mmWord mmFiber76DirectStates (2 + 62) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 2 62 [mmFiber76StateAt 0] (mmFiber76StateAt 7) h2

theorem mmFiber76State8_in_close :
    mmFiber76StateAt 8 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 8 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 8) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep8
  change mmFiber76StateAt 8 ∈ closeChainFiber mmWord mmFiber76DirectStates (1 + 63) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 1 63 [mmFiber76StateAt 0] (mmFiber76StateAt 8) h1

theorem mmFiber76State9_in_close :
    mmFiber76StateAt 9 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 1 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 1) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep1
  have h2 : mmFiber76StateAt 9 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 1) (mmFiber76StateAt 9) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep9
  change mmFiber76StateAt 9 ∈ closeChainFiber mmWord mmFiber76DirectStates (2 + 62) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 2 62 [mmFiber76StateAt 0] (mmFiber76StateAt 9) h2

theorem mmFiber76State10_in_close :
    mmFiber76StateAt 10 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 1 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 1) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep1
  have h2 : mmFiber76StateAt 2 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 1) (mmFiber76StateAt 2) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep2
  have h3 : mmFiber76StateAt 10 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 2) (mmFiber76StateAt 10) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep10
  change mmFiber76StateAt 10 ∈ closeChainFiber mmWord mmFiber76DirectStates (3 + 61) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 3 61 [mmFiber76StateAt 0] (mmFiber76StateAt 10) h3

theorem mmFiber76State11_in_close :
    mmFiber76StateAt 11 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 3 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 3) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep3
  have h2 : mmFiber76StateAt 11 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 3) (mmFiber76StateAt 11) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep11
  change mmFiber76StateAt 11 ∈ closeChainFiber mmWord mmFiber76DirectStates (2 + 62) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 2 62 [mmFiber76StateAt 0] (mmFiber76StateAt 11) h2

theorem mmFiber76State12_in_close :
    mmFiber76StateAt 12 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 4 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 4) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep4
  have h2 : mmFiber76StateAt 12 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 4) (mmFiber76StateAt 12) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep12
  change mmFiber76StateAt 12 ∈ closeChainFiber mmWord mmFiber76DirectStates (2 + 62) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 2 62 [mmFiber76StateAt 0] (mmFiber76StateAt 12) h2

theorem mmFiber76State13_in_close :
    mmFiber76StateAt 13 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 1 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 1) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep1
  have h2 : mmFiber76StateAt 5 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 1) (mmFiber76StateAt 5) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep5
  have h3 : mmFiber76StateAt 13 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 5) (mmFiber76StateAt 13) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep13
  change mmFiber76StateAt 13 ∈ closeChainFiber mmWord mmFiber76DirectStates (3 + 61) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 3 61 [mmFiber76StateAt 0] (mmFiber76StateAt 13) h3

theorem mmFiber76State14_in_close :
    mmFiber76StateAt 14 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 4 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 4) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep4
  have h2 : mmFiber76StateAt 6 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 4) (mmFiber76StateAt 6) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep6
  have h3 : mmFiber76StateAt 14 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 6) (mmFiber76StateAt 14) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep14
  change mmFiber76StateAt 14 ∈ closeChainFiber mmWord mmFiber76DirectStates (3 + 61) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 3 61 [mmFiber76StateAt 0] (mmFiber76StateAt 14) h3

theorem mmFiber76State15_in_close :
    mmFiber76StateAt 15 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 3 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 3) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep3
  have h2 : mmFiber76StateAt 7 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 3) (mmFiber76StateAt 7) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep7
  have h3 : mmFiber76StateAt 15 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 7) (mmFiber76StateAt 15) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep15
  change mmFiber76StateAt 15 ∈ closeChainFiber mmWord mmFiber76DirectStates (3 + 61) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 3 61 [mmFiber76StateAt 0] (mmFiber76StateAt 15) h3

theorem mmFiber76State16_in_close :
    mmFiber76StateAt 16 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 8 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 8) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep8
  have h2 : mmFiber76StateAt 20 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 8) (mmFiber76StateAt 20) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep20
  have h3 : mmFiber76StateAt 16 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 20) (mmFiber76StateAt 16) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep16
  change mmFiber76StateAt 16 ∈ closeChainFiber mmWord mmFiber76DirectStates (3 + 61) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 3 61 [mmFiber76StateAt 0] (mmFiber76StateAt 16) h3

theorem mmFiber76State17_in_close :
    mmFiber76StateAt 17 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 1 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 1) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep1
  have h2 : mmFiber76StateAt 9 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 1) (mmFiber76StateAt 9) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep9
  have h3 : mmFiber76StateAt 21 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 9) (mmFiber76StateAt 21) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep21
  have h4 : mmFiber76StateAt 17 ∈ closeChainFiber mmWord mmFiber76DirectStates 4 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0]
      (mmFiber76StateAt 21) (mmFiber76StateAt 17) (by decide) h3 (by decide)
      mmFiber76ReverseSingleStep17
  change mmFiber76StateAt 17 ∈ closeChainFiber mmWord mmFiber76DirectStates (4 + 60) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 4 60 [mmFiber76StateAt 0] (mmFiber76StateAt 17) h4

theorem mmFiber76State18_in_close :
    mmFiber76StateAt 18 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 4 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 4) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep4
  have h2 : mmFiber76StateAt 12 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 4) (mmFiber76StateAt 12) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep12
  have h3 : mmFiber76StateAt 18 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 12) (mmFiber76StateAt 18) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep18
  change mmFiber76StateAt 18 ∈ closeChainFiber mmWord mmFiber76DirectStates (3 + 61) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 3 61 [mmFiber76StateAt 0] (mmFiber76StateAt 18) h3

theorem mmFiber76State19_in_close :
    mmFiber76StateAt 19 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 1 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 1) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep1
  have h2 : mmFiber76StateAt 5 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 1) (mmFiber76StateAt 5) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep5
  have h3 : mmFiber76StateAt 13 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 5) (mmFiber76StateAt 13) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep13
  have h4 : mmFiber76StateAt 19 ∈ closeChainFiber mmWord mmFiber76DirectStates 4 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0]
      (mmFiber76StateAt 13) (mmFiber76StateAt 19) (by decide) h3 (by decide)
      mmFiber76ReverseSingleStep19
  change mmFiber76StateAt 19 ∈ closeChainFiber mmWord mmFiber76DirectStates (4 + 60) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 4 60 [mmFiber76StateAt 0] (mmFiber76StateAt 19) h4

theorem mmFiber76State20_in_close :
    mmFiber76StateAt 20 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 8 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 8) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep8
  have h2 : mmFiber76StateAt 20 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 8) (mmFiber76StateAt 20) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep20
  change mmFiber76StateAt 20 ∈ closeChainFiber mmWord mmFiber76DirectStates (2 + 62) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 2 62 [mmFiber76StateAt 0] (mmFiber76StateAt 20) h2

theorem mmFiber76State21_in_close :
    mmFiber76StateAt 21 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 1 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 1) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep1
  have h2 : mmFiber76StateAt 9 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 1) (mmFiber76StateAt 9) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep9
  have h3 : mmFiber76StateAt 21 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 9) (mmFiber76StateAt 21) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep21
  change mmFiber76StateAt 21 ∈ closeChainFiber mmWord mmFiber76DirectStates (3 + 61) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 3 61 [mmFiber76StateAt 0] (mmFiber76StateAt 21) h3

theorem mmFiber76State22_in_close :
    mmFiber76StateAt 22 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 1 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 1) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep1
  have h2 : mmFiber76StateAt 2 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 1) (mmFiber76StateAt 2) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep2
  have h3 : mmFiber76StateAt 10 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 2) (mmFiber76StateAt 10) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep10
  have h4 : mmFiber76StateAt 22 ∈ closeChainFiber mmWord mmFiber76DirectStates 4 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0]
      (mmFiber76StateAt 10) (mmFiber76StateAt 22) (by decide) h3 (by decide)
      mmFiber76ReverseSingleStep22
  change mmFiber76StateAt 22 ∈ closeChainFiber mmWord mmFiber76DirectStates (4 + 60) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 4 60 [mmFiber76StateAt 0] (mmFiber76StateAt 22) h4

theorem mmFiber76State23_in_close :
    mmFiber76StateAt 23 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 3 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 3) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep3
  have h2 : mmFiber76StateAt 11 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 3) (mmFiber76StateAt 11) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep11
  have h3 : mmFiber76StateAt 23 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 11) (mmFiber76StateAt 23) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep23
  change mmFiber76StateAt 23 ∈ closeChainFiber mmWord mmFiber76DirectStates (3 + 61) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 3 61 [mmFiber76StateAt 0] (mmFiber76StateAt 23) h3

theorem mmFiber76State24_in_close :
    mmFiber76StateAt 24 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 28 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 28) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep28
  have h2 : mmFiber76StateAt 24 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 28) (mmFiber76StateAt 24) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep24
  change mmFiber76StateAt 24 ∈ closeChainFiber mmWord mmFiber76DirectStates (2 + 62) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 2 62 [mmFiber76StateAt 0] (mmFiber76StateAt 24) h2

theorem mmFiber76State25_in_close :
    mmFiber76StateAt 25 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 1 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 1) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep1
  have h2 : mmFiber76StateAt 29 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 1) (mmFiber76StateAt 29) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep29
  have h3 : mmFiber76StateAt 25 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 29) (mmFiber76StateAt 25) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep25
  change mmFiber76StateAt 25 ∈ closeChainFiber mmWord mmFiber76DirectStates (3 + 61) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 3 61 [mmFiber76StateAt 0] (mmFiber76StateAt 25) h3

theorem mmFiber76State26_in_close :
    mmFiber76StateAt 26 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 4 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 4) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep4
  have h2 : mmFiber76StateAt 26 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 4) (mmFiber76StateAt 26) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep26
  change mmFiber76StateAt 26 ∈ closeChainFiber mmWord mmFiber76DirectStates (2 + 62) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 2 62 [mmFiber76StateAt 0] (mmFiber76StateAt 26) h2

theorem mmFiber76State27_in_close :
    mmFiber76StateAt 27 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 1 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 1) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep1
  have h2 : mmFiber76StateAt 5 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 1) (mmFiber76StateAt 5) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep5
  have h3 : mmFiber76StateAt 27 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 5) (mmFiber76StateAt 27) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep27
  change mmFiber76StateAt 27 ∈ closeChainFiber mmWord mmFiber76DirectStates (3 + 61) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 3 61 [mmFiber76StateAt 0] (mmFiber76StateAt 27) h3

theorem mmFiber76State28_in_close :
    mmFiber76StateAt 28 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 28 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 28) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep28
  change mmFiber76StateAt 28 ∈ closeChainFiber mmWord mmFiber76DirectStates (1 + 63) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 1 63 [mmFiber76StateAt 0] (mmFiber76StateAt 28) h1

theorem mmFiber76State29_in_close :
    mmFiber76StateAt 29 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 1 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 1) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep1
  have h2 : mmFiber76StateAt 29 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 1) (mmFiber76StateAt 29) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep29
  change mmFiber76StateAt 29 ∈ closeChainFiber mmWord mmFiber76DirectStates (2 + 62) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 2 62 [mmFiber76StateAt 0] (mmFiber76StateAt 29) h2

theorem mmFiber76State30_in_close :
    mmFiber76StateAt 30 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 1 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 1) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep1
  have h2 : mmFiber76StateAt 2 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 1) (mmFiber76StateAt 2) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep2
  have h3 : mmFiber76StateAt 30 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 2) (mmFiber76StateAt 30) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep30
  change mmFiber76StateAt 30 ∈ closeChainFiber mmWord mmFiber76DirectStates (3 + 61) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 3 61 [mmFiber76StateAt 0] (mmFiber76StateAt 30) h3

theorem mmFiber76State31_in_close :
    mmFiber76StateAt 31 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 3 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 3) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep3
  have h2 : mmFiber76StateAt 31 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 3) (mmFiber76StateAt 31) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep31
  change mmFiber76StateAt 31 ∈ closeChainFiber mmWord mmFiber76DirectStates (2 + 62) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 2 62 [mmFiber76StateAt 0] (mmFiber76StateAt 31) h2

theorem mmFiber76State32_in_close :
    mmFiber76StateAt 32 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 32 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 32) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep32
  change mmFiber76StateAt 32 ∈ closeChainFiber mmWord mmFiber76DirectStates (1 + 63) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 1 63 [mmFiber76StateAt 0] (mmFiber76StateAt 32) h1

theorem mmFiber76State33_in_close :
    mmFiber76StateAt 33 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 1 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 1) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep1
  have h2 : mmFiber76StateAt 33 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 1) (mmFiber76StateAt 33) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep33
  change mmFiber76StateAt 33 ∈ closeChainFiber mmWord mmFiber76DirectStates (2 + 62) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 2 62 [mmFiber76StateAt 0] (mmFiber76StateAt 33) h2

theorem mmFiber76State34_in_close :
    mmFiber76StateAt 34 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 1 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 1) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep1
  have h2 : mmFiber76StateAt 2 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 1) (mmFiber76StateAt 2) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep2
  have h3 : mmFiber76StateAt 34 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 2) (mmFiber76StateAt 34) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep34
  change mmFiber76StateAt 34 ∈ closeChainFiber mmWord mmFiber76DirectStates (3 + 61) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 3 61 [mmFiber76StateAt 0] (mmFiber76StateAt 34) h3

theorem mmFiber76State35_in_close :
    mmFiber76StateAt 35 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 3 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 3) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep3
  have h2 : mmFiber76StateAt 35 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 3) (mmFiber76StateAt 35) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep35
  change mmFiber76StateAt 35 ∈ closeChainFiber mmWord mmFiber76DirectStates (2 + 62) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 2 62 [mmFiber76StateAt 0] (mmFiber76StateAt 35) h2

theorem mmFiber76State36_in_close :
    mmFiber76StateAt 36 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 4 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 4) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep4
  have h2 : mmFiber76StateAt 36 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 4) (mmFiber76StateAt 36) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep36
  change mmFiber76StateAt 36 ∈ closeChainFiber mmWord mmFiber76DirectStates (2 + 62) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 2 62 [mmFiber76StateAt 0] (mmFiber76StateAt 36) h2

theorem mmFiber76State37_in_close :
    mmFiber76StateAt 37 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 1 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 1) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep1
  have h2 : mmFiber76StateAt 5 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 1) (mmFiber76StateAt 5) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep5
  have h3 : mmFiber76StateAt 37 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 5) (mmFiber76StateAt 37) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep37
  change mmFiber76StateAt 37 ∈ closeChainFiber mmWord mmFiber76DirectStates (3 + 61) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 3 61 [mmFiber76StateAt 0] (mmFiber76StateAt 37) h3

theorem mmFiber76State38_in_close :
    mmFiber76StateAt 38 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 4 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 4) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep4
  have h2 : mmFiber76StateAt 6 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 4) (mmFiber76StateAt 6) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep6
  have h3 : mmFiber76StateAt 38 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 6) (mmFiber76StateAt 38) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep38
  change mmFiber76StateAt 38 ∈ closeChainFiber mmWord mmFiber76DirectStates (3 + 61) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 3 61 [mmFiber76StateAt 0] (mmFiber76StateAt 38) h3

theorem mmFiber76State39_in_close :
    mmFiber76StateAt 39 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 3 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 3) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep3
  have h2 : mmFiber76StateAt 7 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 3) (mmFiber76StateAt 7) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep7
  have h3 : mmFiber76StateAt 39 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 7) (mmFiber76StateAt 39) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep39
  change mmFiber76StateAt 39 ∈ closeChainFiber mmWord mmFiber76DirectStates (3 + 61) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 3 61 [mmFiber76StateAt 0] (mmFiber76StateAt 39) h3

theorem mmFiber76State40_in_close :
    mmFiber76StateAt 40 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 8 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 8) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep8
  have h2 : mmFiber76StateAt 40 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 8) (mmFiber76StateAt 40) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep40
  change mmFiber76StateAt 40 ∈ closeChainFiber mmWord mmFiber76DirectStates (2 + 62) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 2 62 [mmFiber76StateAt 0] (mmFiber76StateAt 40) h2

theorem mmFiber76State41_in_close :
    mmFiber76StateAt 41 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 1 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 1) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep1
  have h2 : mmFiber76StateAt 9 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 1) (mmFiber76StateAt 9) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep9
  have h3 : mmFiber76StateAt 41 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 9) (mmFiber76StateAt 41) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep41
  change mmFiber76StateAt 41 ∈ closeChainFiber mmWord mmFiber76DirectStates (3 + 61) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 3 61 [mmFiber76StateAt 0] (mmFiber76StateAt 41) h3

theorem mmFiber76State42_in_close :
    mmFiber76StateAt 42 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 1 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 1) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep1
  have h2 : mmFiber76StateAt 2 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 1) (mmFiber76StateAt 2) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep2
  have h3 : mmFiber76StateAt 10 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 2) (mmFiber76StateAt 10) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep10
  have h4 : mmFiber76StateAt 42 ∈ closeChainFiber mmWord mmFiber76DirectStates 4 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0]
      (mmFiber76StateAt 10) (mmFiber76StateAt 42) (by decide) h3 (by decide)
      mmFiber76ReverseSingleStep42
  change mmFiber76StateAt 42 ∈ closeChainFiber mmWord mmFiber76DirectStates (4 + 60) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 4 60 [mmFiber76StateAt 0] (mmFiber76StateAt 42) h4

theorem mmFiber76State43_in_close :
    mmFiber76StateAt 43 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 3 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 3) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep3
  have h2 : mmFiber76StateAt 11 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 3) (mmFiber76StateAt 11) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep11
  have h3 : mmFiber76StateAt 43 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 11) (mmFiber76StateAt 43) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep43
  change mmFiber76StateAt 43 ∈ closeChainFiber mmWord mmFiber76DirectStates (3 + 61) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 3 61 [mmFiber76StateAt 0] (mmFiber76StateAt 43) h3

theorem mmFiber76State44_in_close :
    mmFiber76StateAt 44 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 4 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 4) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep4
  have h2 : mmFiber76StateAt 12 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 4) (mmFiber76StateAt 12) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep12
  have h3 : mmFiber76StateAt 44 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 12) (mmFiber76StateAt 44) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep44
  change mmFiber76StateAt 44 ∈ closeChainFiber mmWord mmFiber76DirectStates (3 + 61) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 3 61 [mmFiber76StateAt 0] (mmFiber76StateAt 44) h3

theorem mmFiber76State45_in_close :
    mmFiber76StateAt 45 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 1 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 1) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep1
  have h2 : mmFiber76StateAt 5 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 1) (mmFiber76StateAt 5) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep5
  have h3 : mmFiber76StateAt 13 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 5) (mmFiber76StateAt 13) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep13
  have h4 : mmFiber76StateAt 45 ∈ closeChainFiber mmWord mmFiber76DirectStates 4 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0]
      (mmFiber76StateAt 13) (mmFiber76StateAt 45) (by decide) h3 (by decide)
      mmFiber76ReverseSingleStep45
  change mmFiber76StateAt 45 ∈ closeChainFiber mmWord mmFiber76DirectStates (4 + 60) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 4 60 [mmFiber76StateAt 0] (mmFiber76StateAt 45) h4

theorem mmFiber76State46_in_close :
    mmFiber76StateAt 46 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 4 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 4) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep4
  have h2 : mmFiber76StateAt 6 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 4) (mmFiber76StateAt 6) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep6
  have h3 : mmFiber76StateAt 14 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 6) (mmFiber76StateAt 14) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep14
  have h4 : mmFiber76StateAt 46 ∈ closeChainFiber mmWord mmFiber76DirectStates 4 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0]
      (mmFiber76StateAt 14) (mmFiber76StateAt 46) (by decide) h3 (by decide)
      mmFiber76ReverseSingleStep46
  change mmFiber76StateAt 46 ∈ closeChainFiber mmWord mmFiber76DirectStates (4 + 60) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 4 60 [mmFiber76StateAt 0] (mmFiber76StateAt 46) h4

theorem mmFiber76State47_in_close :
    mmFiber76StateAt 47 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 3 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 3) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep3
  have h2 : mmFiber76StateAt 7 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 3) (mmFiber76StateAt 7) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep7
  have h3 : mmFiber76StateAt 15 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 7) (mmFiber76StateAt 15) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep15
  have h4 : mmFiber76StateAt 47 ∈ closeChainFiber mmWord mmFiber76DirectStates 4 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0]
      (mmFiber76StateAt 15) (mmFiber76StateAt 47) (by decide) h3 (by decide)
      mmFiber76ReverseSingleStep47
  change mmFiber76StateAt 47 ∈ closeChainFiber mmWord mmFiber76DirectStates (4 + 60) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 4 60 [mmFiber76StateAt 0] (mmFiber76StateAt 47) h4

theorem mmFiber76State48_in_close :
    mmFiber76StateAt 48 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 32 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 32) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep32
  have h2 : mmFiber76StateAt 48 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 32) (mmFiber76StateAt 48) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep48
  change mmFiber76StateAt 48 ∈ closeChainFiber mmWord mmFiber76DirectStates (2 + 62) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 2 62 [mmFiber76StateAt 0] (mmFiber76StateAt 48) h2

theorem mmFiber76State49_in_close :
    mmFiber76StateAt 49 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 1 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 1) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep1
  have h2 : mmFiber76StateAt 33 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 1) (mmFiber76StateAt 33) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep33
  have h3 : mmFiber76StateAt 49 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 33) (mmFiber76StateAt 49) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep49
  change mmFiber76StateAt 49 ∈ closeChainFiber mmWord mmFiber76DirectStates (3 + 61) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 3 61 [mmFiber76StateAt 0] (mmFiber76StateAt 49) h3

theorem mmFiber76State50_in_close :
    mmFiber76StateAt 50 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 32 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 32) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep32
  have h2 : mmFiber76StateAt 48 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 32) (mmFiber76StateAt 48) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep48
  have h3 : mmFiber76StateAt 50 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 48) (mmFiber76StateAt 50) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep50
  change mmFiber76StateAt 50 ∈ closeChainFiber mmWord mmFiber76DirectStates (3 + 61) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 3 61 [mmFiber76StateAt 0] (mmFiber76StateAt 50) h3

theorem mmFiber76State51_in_close :
    mmFiber76StateAt 51 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 3 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 3) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep3
  have h2 : mmFiber76StateAt 35 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 3) (mmFiber76StateAt 35) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep35
  have h3 : mmFiber76StateAt 51 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 35) (mmFiber76StateAt 51) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep51
  change mmFiber76StateAt 51 ∈ closeChainFiber mmWord mmFiber76DirectStates (3 + 61) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 3 61 [mmFiber76StateAt 0] (mmFiber76StateAt 51) h3

theorem mmFiber76State52_in_close :
    mmFiber76StateAt 52 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 4 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 4) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep4
  have h2 : mmFiber76StateAt 36 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 4) (mmFiber76StateAt 36) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep36
  have h3 : mmFiber76StateAt 52 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 36) (mmFiber76StateAt 52) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep52
  change mmFiber76StateAt 52 ∈ closeChainFiber mmWord mmFiber76DirectStates (3 + 61) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 3 61 [mmFiber76StateAt 0] (mmFiber76StateAt 52) h3

theorem mmFiber76State53_in_close :
    mmFiber76StateAt 53 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 1 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 1) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep1
  have h2 : mmFiber76StateAt 5 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 1) (mmFiber76StateAt 5) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep5
  have h3 : mmFiber76StateAt 37 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 5) (mmFiber76StateAt 37) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep37
  have h4 : mmFiber76StateAt 53 ∈ closeChainFiber mmWord mmFiber76DirectStates 4 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0]
      (mmFiber76StateAt 37) (mmFiber76StateAt 53) (by decide) h3 (by decide)
      mmFiber76ReverseSingleStep53
  change mmFiber76StateAt 53 ∈ closeChainFiber mmWord mmFiber76DirectStates (4 + 60) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 4 60 [mmFiber76StateAt 0] (mmFiber76StateAt 53) h4

theorem mmFiber76State54_in_close :
    mmFiber76StateAt 54 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 1 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 1) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep1
  have h2 : mmFiber76StateAt 33 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 1) (mmFiber76StateAt 33) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep33
  have h3 : mmFiber76StateAt 49 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 33) (mmFiber76StateAt 49) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep49
  have h4 : mmFiber76StateAt 54 ∈ closeChainFiber mmWord mmFiber76DirectStates 4 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0]
      (mmFiber76StateAt 49) (mmFiber76StateAt 54) (by decide) h3 (by decide)
      mmFiber76ReverseSingleStep54
  change mmFiber76StateAt 54 ∈ closeChainFiber mmWord mmFiber76DirectStates (4 + 60) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 4 60 [mmFiber76StateAt 0] (mmFiber76StateAt 54) h4

theorem mmFiber76State55_in_close :
    mmFiber76StateAt 55 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 32 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 32) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep32
  have h2 : mmFiber76StateAt 48 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 32) (mmFiber76StateAt 48) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep48
  have h3 : mmFiber76StateAt 55 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 48) (mmFiber76StateAt 55) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep55
  change mmFiber76StateAt 55 ∈ closeChainFiber mmWord mmFiber76DirectStates (3 + 61) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 3 61 [mmFiber76StateAt 0] (mmFiber76StateAt 55) h3

theorem mmFiber76State56_in_close :
    mmFiber76StateAt 56 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 8 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 8) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep8
  have h2 : mmFiber76StateAt 40 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 8) (mmFiber76StateAt 40) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep40
  have h3 : mmFiber76StateAt 56 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 40) (mmFiber76StateAt 56) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep56
  change mmFiber76StateAt 56 ∈ closeChainFiber mmWord mmFiber76DirectStates (3 + 61) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 3 61 [mmFiber76StateAt 0] (mmFiber76StateAt 56) h3

theorem mmFiber76State57_in_close :
    mmFiber76StateAt 57 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 1 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 1) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep1
  have h2 : mmFiber76StateAt 9 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 1) (mmFiber76StateAt 9) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep9
  have h3 : mmFiber76StateAt 41 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 9) (mmFiber76StateAt 41) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep41
  have h4 : mmFiber76StateAt 57 ∈ closeChainFiber mmWord mmFiber76DirectStates 4 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0]
      (mmFiber76StateAt 41) (mmFiber76StateAt 57) (by decide) h3 (by decide)
      mmFiber76ReverseSingleStep57
  change mmFiber76StateAt 57 ∈ closeChainFiber mmWord mmFiber76DirectStates (4 + 60) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 4 60 [mmFiber76StateAt 0] (mmFiber76StateAt 57) h4

theorem mmFiber76State58_in_close :
    mmFiber76StateAt 58 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 4 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 4) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep4
  have h2 : mmFiber76StateAt 26 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 4) (mmFiber76StateAt 26) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep26
  have h3 : mmFiber76StateAt 58 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 26) (mmFiber76StateAt 58) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep58
  change mmFiber76StateAt 58 ∈ closeChainFiber mmWord mmFiber76DirectStates (3 + 61) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 3 61 [mmFiber76StateAt 0] (mmFiber76StateAt 58) h3

theorem mmFiber76State59_in_close :
    mmFiber76StateAt 59 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 1 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 1) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep1
  have h2 : mmFiber76StateAt 5 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 1) (mmFiber76StateAt 5) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep5
  have h3 : mmFiber76StateAt 27 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 5) (mmFiber76StateAt 27) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep27
  have h4 : mmFiber76StateAt 59 ∈ closeChainFiber mmWord mmFiber76DirectStates 4 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0]
      (mmFiber76StateAt 27) (mmFiber76StateAt 59) (by decide) h3 (by decide)
      mmFiber76ReverseSingleStep59
  change mmFiber76StateAt 59 ∈ closeChainFiber mmWord mmFiber76DirectStates (4 + 60) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 4 60 [mmFiber76StateAt 0] (mmFiber76StateAt 59) h4

theorem mmFiber76State60_in_close :
    mmFiber76StateAt 60 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 28 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 28) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep28
  have h2 : mmFiber76StateAt 60 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 28) (mmFiber76StateAt 60) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep60
  change mmFiber76StateAt 60 ∈ closeChainFiber mmWord mmFiber76DirectStates (2 + 62) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 2 62 [mmFiber76StateAt 0] (mmFiber76StateAt 60) h2

theorem mmFiber76State61_in_close :
    mmFiber76StateAt 61 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 1 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 1) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep1
  have h2 : mmFiber76StateAt 29 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 1) (mmFiber76StateAt 29) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep29
  have h3 : mmFiber76StateAt 61 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 29) (mmFiber76StateAt 61) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep61
  change mmFiber76StateAt 61 ∈ closeChainFiber mmWord mmFiber76DirectStates (3 + 61) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 3 61 [mmFiber76StateAt 0] (mmFiber76StateAt 61) h3

theorem mmFiber76State62_in_close :
    mmFiber76StateAt 62 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 28 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 28) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep28
  have h2 : mmFiber76StateAt 60 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 28) (mmFiber76StateAt 60) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep60
  have h3 : mmFiber76StateAt 62 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 60) (mmFiber76StateAt 62) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep62
  change mmFiber76StateAt 62 ∈ closeChainFiber mmWord mmFiber76DirectStates (3 + 61) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 3 61 [mmFiber76StateAt 0] (mmFiber76StateAt 62) h3

theorem mmFiber76State63_in_close :
    mmFiber76StateAt 63 ∈ closeChainFiber mmWord mmFiber76DirectStates mmFiber76DirectStates.length [mmFiber76StateAt 0] := by
  have h0 : mmFiber76StateAt 0 ∈ closeChainFiber mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber76StateAt 3 ∈ closeChainFiber mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 0 [mmFiber76StateAt 0]
      (mmFiber76StateAt 0) (mmFiber76StateAt 3) (by decide) h0 (by decide)
      mmFiber76ReverseSingleStep3
  have h2 : mmFiber76StateAt 31 ∈ closeChainFiber mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 1 [mmFiber76StateAt 0]
      (mmFiber76StateAt 3) (mmFiber76StateAt 31) (by decide) h1 (by decide)
      mmFiber76ReverseSingleStep31
  have h3 : mmFiber76StateAt 63 ∈ closeChainFiber mmWord mmFiber76DirectStates 3 [mmFiber76StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber76DirectStates 2 [mmFiber76StateAt 0]
      (mmFiber76StateAt 31) (mmFiber76StateAt 63) (by decide) h2 (by decide)
      mmFiber76ReverseSingleStep63
  change mmFiber76StateAt 63 ∈ closeChainFiber mmWord mmFiber76DirectStates (3 + 61) [mmFiber76StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber76DirectStates 3 61 [mmFiber76StateAt 0] (mmFiber76StateAt 63) h3

theorem mmFiber76DirectConnected :
    chainFiberConnected mmWord mmFiber76DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber76DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber76State0_in_close
  · subst state
    exact mmFiber76State1_in_close
  · subst state
    exact mmFiber76State2_in_close
  · subst state
    exact mmFiber76State3_in_close
  · subst state
    exact mmFiber76State4_in_close
  · subst state
    exact mmFiber76State5_in_close
  · subst state
    exact mmFiber76State6_in_close
  · subst state
    exact mmFiber76State7_in_close
  · subst state
    exact mmFiber76State8_in_close
  · subst state
    exact mmFiber76State9_in_close
  · subst state
    exact mmFiber76State10_in_close
  · subst state
    exact mmFiber76State11_in_close
  · subst state
    exact mmFiber76State12_in_close
  · subst state
    exact mmFiber76State13_in_close
  · subst state
    exact mmFiber76State14_in_close
  · subst state
    exact mmFiber76State15_in_close
  · subst state
    exact mmFiber76State16_in_close
  · subst state
    exact mmFiber76State17_in_close
  · subst state
    exact mmFiber76State18_in_close
  · subst state
    exact mmFiber76State19_in_close
  · subst state
    exact mmFiber76State20_in_close
  · subst state
    exact mmFiber76State21_in_close
  · subst state
    exact mmFiber76State22_in_close
  · subst state
    exact mmFiber76State23_in_close
  · subst state
    exact mmFiber76State24_in_close
  · subst state
    exact mmFiber76State25_in_close
  · subst state
    exact mmFiber76State26_in_close
  · subst state
    exact mmFiber76State27_in_close
  · subst state
    exact mmFiber76State28_in_close
  · subst state
    exact mmFiber76State29_in_close
  · subst state
    exact mmFiber76State30_in_close
  · subst state
    exact mmFiber76State31_in_close
  · subst state
    exact mmFiber76State32_in_close
  · subst state
    exact mmFiber76State33_in_close
  · subst state
    exact mmFiber76State34_in_close
  · subst state
    exact mmFiber76State35_in_close
  · subst state
    exact mmFiber76State36_in_close
  · subst state
    exact mmFiber76State37_in_close
  · subst state
    exact mmFiber76State38_in_close
  · subst state
    exact mmFiber76State39_in_close
  · subst state
    exact mmFiber76State40_in_close
  · subst state
    exact mmFiber76State41_in_close
  · subst state
    exact mmFiber76State42_in_close
  · subst state
    exact mmFiber76State43_in_close
  · subst state
    exact mmFiber76State44_in_close
  · subst state
    exact mmFiber76State45_in_close
  · subst state
    exact mmFiber76State46_in_close
  · subst state
    exact mmFiber76State47_in_close
  · subst state
    exact mmFiber76State48_in_close
  · subst state
    exact mmFiber76State49_in_close
  · subst state
    exact mmFiber76State50_in_close
  · subst state
    exact mmFiber76State51_in_close
  · subst state
    exact mmFiber76State52_in_close
  · subst state
    exact mmFiber76State53_in_close
  · subst state
    exact mmFiber76State54_in_close
  · subst state
    exact mmFiber76State55_in_close
  · subst state
    exact mmFiber76State56_in_close
  · subst state
    exact mmFiber76State57_in_close
  · subst state
    exact mmFiber76State58_in_close
  · subst state
    exact mmFiber76State59_in_close
  · subst state
    exact mmFiber76State60_in_close
  · subst state
    exact mmFiber76State61_in_close
  · subst state
    exact mmFiber76State62_in_close
  · subst state
    exact mmFiber76State63_in_close
  · cases h
end GoertzelLemma818LengthTwoMMBridge

end Mettapedia.GraphTheory.FourColor
