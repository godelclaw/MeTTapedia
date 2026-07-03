import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for `mirror,mirror` size-64 fiber 44

This module proves direct connectedness for one generated size-64 fiber from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMMBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorMirrorCertificate
open GoertzelLemma818MirrorMirrorReverseAudit

def mmFiber44StateAt (i : Nat) : List TauState :=
  directStates (mmFiber44RowAt i).sourceLeft (mmFiber44RowAt i).sourceRight

def mmFiber44DirectStates : List (List TauState) :=
  [mmFiber44StateAt 0, mmFiber44StateAt 1, mmFiber44StateAt 2, mmFiber44StateAt 3, mmFiber44StateAt 4, mmFiber44StateAt 5, mmFiber44StateAt 6, mmFiber44StateAt 7, mmFiber44StateAt 8, mmFiber44StateAt 9, mmFiber44StateAt 10, mmFiber44StateAt 11, mmFiber44StateAt 12, mmFiber44StateAt 13, mmFiber44StateAt 14, mmFiber44StateAt 15, mmFiber44StateAt 16, mmFiber44StateAt 17, mmFiber44StateAt 18, mmFiber44StateAt 19, mmFiber44StateAt 20, mmFiber44StateAt 21, mmFiber44StateAt 22, mmFiber44StateAt 23, mmFiber44StateAt 24, mmFiber44StateAt 25, mmFiber44StateAt 26, mmFiber44StateAt 27, mmFiber44StateAt 28, mmFiber44StateAt 29, mmFiber44StateAt 30, mmFiber44StateAt 31, mmFiber44StateAt 32, mmFiber44StateAt 33, mmFiber44StateAt 34, mmFiber44StateAt 35, mmFiber44StateAt 36, mmFiber44StateAt 37, mmFiber44StateAt 38, mmFiber44StateAt 39, mmFiber44StateAt 40, mmFiber44StateAt 41, mmFiber44StateAt 42, mmFiber44StateAt 43, mmFiber44StateAt 44, mmFiber44StateAt 45, mmFiber44StateAt 46, mmFiber44StateAt 47, mmFiber44StateAt 48, mmFiber44StateAt 49, mmFiber44StateAt 50, mmFiber44StateAt 51, mmFiber44StateAt 52, mmFiber44StateAt 53, mmFiber44StateAt 54, mmFiber44StateAt 55, mmFiber44StateAt 56, mmFiber44StateAt 57, mmFiber44StateAt 58, mmFiber44StateAt 59, mmFiber44StateAt 60, mmFiber44StateAt 61, mmFiber44StateAt 62, mmFiber44StateAt 63]

theorem mmFiber44ReverseRow_1_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk0_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 0) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 0) (mmFiber44StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 0) (mmFiber44StateAt 1)
    (mmFiber44RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 1) (by decide) mmFiber44ReverseRow_1_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_2_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk1_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 2) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber44ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 0) (mmFiber44StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 0) (mmFiber44StateAt 2)
    (mmFiber44RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 2) (by decide) mmFiber44ReverseRow_2_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_3_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk1_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 2) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 1) (mmFiber44StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 1) (mmFiber44StateAt 3)
    (mmFiber44RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 3) (by decide) mmFiber44ReverseRow_3_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_4_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk2_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 4) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber44ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 2) (mmFiber44StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 2) (mmFiber44StateAt 4)
    (mmFiber44RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 4) (by decide) mmFiber44ReverseRow_4_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_5_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk2_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 4) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 7) (mmFiber44StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 7) (mmFiber44StateAt 5)
    (mmFiber44RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 5) (by decide) mmFiber44ReverseRow_5_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_6_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk3_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 6) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber44ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 1) (mmFiber44StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 1) (mmFiber44StateAt 6)
    (mmFiber44RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 6) (by decide) mmFiber44ReverseRow_6_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_7_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk3_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 6) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 0) (mmFiber44StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 0) (mmFiber44StateAt 7)
    (mmFiber44RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 7) (by decide) mmFiber44ReverseRow_7_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_8_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 8) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk4_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 8) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber44ReverseSingleStep8 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 0) (mmFiber44StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 0) (mmFiber44StateAt 8)
    (mmFiber44RowAt 8).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 8) (by decide) mmFiber44ReverseRow_8_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_9_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 9) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk4_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 8) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep9 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 1) (mmFiber44StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 1) (mmFiber44StateAt 9)
    (mmFiber44RowAt 9).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 9) (by decide) mmFiber44ReverseRow_9_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_10_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 10) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk5_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 10) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber44ReverseSingleStep10 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 2) (mmFiber44StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 2) (mmFiber44StateAt 10)
    (mmFiber44RowAt 10).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 10) (by decide) mmFiber44ReverseRow_10_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_11_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 11) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk5_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 10) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep11 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 3) (mmFiber44StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 3) (mmFiber44StateAt 11)
    (mmFiber44RowAt 11).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 11) (by decide) mmFiber44ReverseRow_11_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_12_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 12) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk6_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 12) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber44ReverseSingleStep12 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 4) (mmFiber44StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 4) (mmFiber44StateAt 12)
    (mmFiber44RowAt 12).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 12) (by decide) mmFiber44ReverseRow_12_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_13_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 13) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk6_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 12) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep13 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 5) (mmFiber44StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 5) (mmFiber44StateAt 13)
    (mmFiber44RowAt 13).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 13) (by decide) mmFiber44ReverseRow_13_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_14_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 14) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk7_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 14) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber44ReverseSingleStep14 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 6) (mmFiber44StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 6) (mmFiber44StateAt 14)
    (mmFiber44RowAt 14).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 14) (by decide) mmFiber44ReverseRow_14_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_15_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 15) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk7_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 14) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep15 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 7) (mmFiber44StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 7) (mmFiber44StateAt 15)
    (mmFiber44RowAt 15).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 15) (by decide) mmFiber44ReverseRow_15_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_16_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 16) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk8_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 16) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber44ReverseSingleStep16 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 0) (mmFiber44StateAt 16) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 0) (mmFiber44StateAt 16)
    (mmFiber44RowAt 16).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 16) (by decide) mmFiber44ReverseRow_16_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_17_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 17) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk8_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 16) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep17 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 1) (mmFiber44StateAt 17) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 1) (mmFiber44StateAt 17)
    (mmFiber44RowAt 17).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 17) (by decide) mmFiber44ReverseRow_17_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_18_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 18) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk9_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 18) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber44ReverseSingleStep18 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 2) (mmFiber44StateAt 18) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 2) (mmFiber44StateAt 18)
    (mmFiber44RowAt 18).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 18) (by decide) mmFiber44ReverseRow_18_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_19_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 19) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk9_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 18) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep19 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 3) (mmFiber44StateAt 19) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 3) (mmFiber44StateAt 19)
    (mmFiber44RowAt 19).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 19) (by decide) mmFiber44ReverseRow_19_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_20_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 20) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk10_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 20) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber44ReverseSingleStep20 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 16) (mmFiber44StateAt 20) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 16) (mmFiber44StateAt 20)
    (mmFiber44RowAt 20).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 20) (by decide) mmFiber44ReverseRow_20_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_21_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 21) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk10_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 20) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep21 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 17) (mmFiber44StateAt 21) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 17) (mmFiber44StateAt 21)
    (mmFiber44RowAt 21).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 21) (by decide) mmFiber44ReverseRow_21_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_22_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 22) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk11_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 22) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber44ReverseSingleStep22 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 6) (mmFiber44StateAt 22) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 6) (mmFiber44StateAt 22)
    (mmFiber44RowAt 22).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 22) (by decide) mmFiber44ReverseRow_22_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_23_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 23) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk11_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 22) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep23 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 7) (mmFiber44StateAt 23) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 7) (mmFiber44StateAt 23)
    (mmFiber44RowAt 23).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 23) (by decide) mmFiber44ReverseRow_23_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_24_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 24) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk12_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 24) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber44ReverseSingleStep24 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 8) (mmFiber44StateAt 24) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 8) (mmFiber44StateAt 24)
    (mmFiber44RowAt 24).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 24) (by decide) mmFiber44ReverseRow_24_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_25_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 25) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk12_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 24) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep25 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 9) (mmFiber44StateAt 25) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 9) (mmFiber44StateAt 25)
    (mmFiber44RowAt 25).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 25) (by decide) mmFiber44ReverseRow_25_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_26_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 26) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk13_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 26) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber44ReverseSingleStep26 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 10) (mmFiber44StateAt 26) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 10) (mmFiber44StateAt 26)
    (mmFiber44RowAt 26).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 26) (by decide) mmFiber44ReverseRow_26_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_27_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 27) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk13_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 26) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep27 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 11) (mmFiber44StateAt 27) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 11) (mmFiber44StateAt 27)
    (mmFiber44RowAt 27).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 27) (by decide) mmFiber44ReverseRow_27_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_28_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 28) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk14_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 28) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber44ReverseSingleStep28 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 24) (mmFiber44StateAt 28) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 24) (mmFiber44StateAt 28)
    (mmFiber44RowAt 28).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 28) (by decide) mmFiber44ReverseRow_28_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_29_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 29) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk14_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 28) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep29 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 25) (mmFiber44StateAt 29) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 25) (mmFiber44StateAt 29)
    (mmFiber44RowAt 29).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 29) (by decide) mmFiber44ReverseRow_29_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_30_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 30) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk15_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 30) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber44ReverseSingleStep30 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 14) (mmFiber44StateAt 30) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 14) (mmFiber44StateAt 30)
    (mmFiber44RowAt 30).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 30) (by decide) mmFiber44ReverseRow_30_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_31_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 31) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk15_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 30) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep31 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 15) (mmFiber44StateAt 31) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 15) (mmFiber44StateAt 31)
    (mmFiber44RowAt 31).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 31) (by decide) mmFiber44ReverseRow_31_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_32_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 32) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk16_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 32) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber44ReverseSingleStep32 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 48) (mmFiber44StateAt 32) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 48) (mmFiber44StateAt 32)
    (mmFiber44RowAt 32).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 32) (by decide) mmFiber44ReverseRow_32_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_33_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 33) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk16_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 32) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep33 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 49) (mmFiber44StateAt 33) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 49) (mmFiber44StateAt 33)
    (mmFiber44RowAt 33).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 33) (by decide) mmFiber44ReverseRow_33_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_34_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 34) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk17_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 34) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber44ReverseSingleStep34 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 22) (mmFiber44StateAt 34) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 22) (mmFiber44StateAt 34)
    (mmFiber44RowAt 34).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 34) (by decide) mmFiber44ReverseRow_34_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_35_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 35) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk17_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 34) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep35 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 23) (mmFiber44StateAt 35) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 23) (mmFiber44StateAt 35)
    (mmFiber44RowAt 35).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 35) (by decide) mmFiber44ReverseRow_35_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_36_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 36) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk18_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 36) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber44ReverseSingleStep36 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 18) (mmFiber44StateAt 36) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 18) (mmFiber44StateAt 36)
    (mmFiber44RowAt 36).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 36) (by decide) mmFiber44ReverseRow_36_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_37_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 37) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk18_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 36) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep37 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 39) (mmFiber44StateAt 37) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 39) (mmFiber44StateAt 37)
    (mmFiber44RowAt 37).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 37) (by decide) mmFiber44ReverseRow_37_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_38_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 38) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk19_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 38) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber44ReverseSingleStep38 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 17) (mmFiber44StateAt 38) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 17) (mmFiber44StateAt 38)
    (mmFiber44RowAt 38).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 38) (by decide) mmFiber44ReverseRow_38_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_39_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 39) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk19_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 38) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep39 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 16) (mmFiber44StateAt 39) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 16) (mmFiber44StateAt 39)
    (mmFiber44RowAt 39).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 39) (by decide) mmFiber44ReverseRow_39_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_40_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 40) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk20_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 40) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber44ReverseSingleStep40 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 56) (mmFiber44StateAt 40) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 56) (mmFiber44StateAt 40)
    (mmFiber44RowAt 40).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 40) (by decide) mmFiber44ReverseRow_40_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_41_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 41) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk20_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 40) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep41 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 57) (mmFiber44StateAt 41) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 57) (mmFiber44StateAt 41)
    (mmFiber44RowAt 41).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 41) (by decide) mmFiber44ReverseRow_41_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_42_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 42) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk21_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 42) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber44ReverseSingleStep42 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 58) (mmFiber44StateAt 42) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 58) (mmFiber44StateAt 42)
    (mmFiber44RowAt 42).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 42) (by decide) mmFiber44ReverseRow_42_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_43_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 43) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk21_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 42) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep43 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 40) (mmFiber44StateAt 43) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 40) (mmFiber44StateAt 43)
    (mmFiber44RowAt 43).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 43) (by decide) mmFiber44ReverseRow_43_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_44_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 44) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk22_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 44) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber44ReverseSingleStep44 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 40) (mmFiber44StateAt 44) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 40) (mmFiber44StateAt 44)
    (mmFiber44RowAt 44).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 44) (by decide) mmFiber44ReverseRow_44_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_45_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 45) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk22_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 44) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep45 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 41) (mmFiber44StateAt 45) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 41) (mmFiber44StateAt 45)
    (mmFiber44RowAt 45).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 45) (by decide) mmFiber44ReverseRow_45_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_46_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 46) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk23_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 46) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber44ReverseSingleStep46 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 62) (mmFiber44StateAt 46) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 62) (mmFiber44StateAt 46)
    (mmFiber44RowAt 46).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 46) (by decide) mmFiber44ReverseRow_46_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_47_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 47) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk23_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 46) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep47 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 63) (mmFiber44StateAt 47) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 63) (mmFiber44StateAt 47)
    (mmFiber44RowAt 47).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 47) (by decide) mmFiber44ReverseRow_47_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_48_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 48) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk24_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 48) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber44ReverseSingleStep48 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 8) (mmFiber44StateAt 48) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 8) (mmFiber44StateAt 48)
    (mmFiber44RowAt 48).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 48) (by decide) mmFiber44ReverseRow_48_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_49_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 49) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk24_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 48) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep49 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 9) (mmFiber44StateAt 49) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 9) (mmFiber44StateAt 49)
    (mmFiber44RowAt 49).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 49) (by decide) mmFiber44ReverseRow_49_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_50_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 50) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk25_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 50) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber44ReverseSingleStep50 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 10) (mmFiber44StateAt 50) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 10) (mmFiber44StateAt 50)
    (mmFiber44RowAt 50).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 50) (by decide) mmFiber44ReverseRow_50_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_51_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 51) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk25_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 50) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep51 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 11) (mmFiber44StateAt 51) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 11) (mmFiber44StateAt 51)
    (mmFiber44RowAt 51).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 51) (by decide) mmFiber44ReverseRow_51_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_52_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 52) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk26_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 52) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber44ReverseSingleStep52 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 12) (mmFiber44StateAt 52) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 12) (mmFiber44StateAt 52)
    (mmFiber44RowAt 52).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 52) (by decide) mmFiber44ReverseRow_52_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_53_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 53) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk26_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 52) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep53 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 13) (mmFiber44StateAt 53) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 13) (mmFiber44StateAt 53)
    (mmFiber44RowAt 53).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 53) (by decide) mmFiber44ReverseRow_53_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_54_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 54) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk27_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 54) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber44ReverseSingleStep54 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 14) (mmFiber44StateAt 54) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 14) (mmFiber44StateAt 54)
    (mmFiber44RowAt 54).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 54) (by decide) mmFiber44ReverseRow_54_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_55_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 55) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk27_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 54) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep55 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 15) (mmFiber44StateAt 55) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 15) (mmFiber44StateAt 55)
    (mmFiber44RowAt 55).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 55) (by decide) mmFiber44ReverseRow_55_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_56_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 56) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk28_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 56) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber44ReverseSingleStep56 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 0) (mmFiber44StateAt 56) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 0) (mmFiber44StateAt 56)
    (mmFiber44RowAt 56).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 56) (by decide) mmFiber44ReverseRow_56_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_57_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 57) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk28_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 56) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep57 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 1) (mmFiber44StateAt 57) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 1) (mmFiber44StateAt 57)
    (mmFiber44RowAt 57).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 57) (by decide) mmFiber44ReverseRow_57_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_58_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 58) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk29_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 58) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber44ReverseSingleStep58 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 2) (mmFiber44StateAt 58) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 2) (mmFiber44StateAt 58)
    (mmFiber44RowAt 58).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 58) (by decide) mmFiber44ReverseRow_58_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_59_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 59) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk29_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 58) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep59 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 3) (mmFiber44StateAt 59) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 3) (mmFiber44StateAt 59)
    (mmFiber44RowAt 59).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 59) (by decide) mmFiber44ReverseRow_59_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_60_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 60) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk30_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 60) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber44ReverseSingleStep60 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 4) (mmFiber44StateAt 60) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 4) (mmFiber44StateAt 60)
    (mmFiber44RowAt 60).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 60) (by decide) mmFiber44ReverseRow_60_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_61_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 61) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk30_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 60) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep61 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 5) (mmFiber44StateAt 61) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 5) (mmFiber44StateAt 61)
    (mmFiber44RowAt 61).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 61) (by decide) mmFiber44ReverseRow_61_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_62_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 62) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk31_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 62) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber44ReverseSingleStep62 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 6) (mmFiber44StateAt 62) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 6) (mmFiber44StateAt 62)
    (mmFiber44RowAt 62).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 62) (by decide) mmFiber44ReverseRow_62_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44ReverseRow_63_ok :
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 63) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber44Chunk31_ok
  change (mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 62) &&
    mmRowReverseValid mmFiber44Key mmFiber44Expected (mmFiber44RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber44ReverseSingleStep63 :
    chainSingleKempeStep mmWord (mmFiber44StateAt 7) (mmFiber44StateAt 63) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber44StateAt 7) (mmFiber44StateAt 63)
    (mmFiber44RowAt 63).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber44Key mmFiber44Expected
        (mmFiber44RowAt 63) (by decide) mmFiber44ReverseRow_63_ok
      simpa [mmFiber44StateAt, mmFiber44RowAt, mmFiber44Rows, listGetD, directRow] using h)

theorem mmFiber44State0_in_close :
    mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  change mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 64 [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 0 64 [mmFiber44StateAt 0] (mmFiber44StateAt 0) (by simp [closeChainFiber])

theorem mmFiber44State1_in_close :
    mmFiber44StateAt 1 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 1 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 1) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep1
  change mmFiber44StateAt 1 ∈ closeChainFiber mmWord mmFiber44DirectStates (1 + 63) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 1 63 [mmFiber44StateAt 0] (mmFiber44StateAt 1) h1

theorem mmFiber44State2_in_close :
    mmFiber44StateAt 2 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 2 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 2) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep2
  change mmFiber44StateAt 2 ∈ closeChainFiber mmWord mmFiber44DirectStates (1 + 63) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 1 63 [mmFiber44StateAt 0] (mmFiber44StateAt 2) h1

theorem mmFiber44State3_in_close :
    mmFiber44StateAt 3 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 1 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 1) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep1
  have h2 : mmFiber44StateAt 3 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 1) (mmFiber44StateAt 3) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep3
  change mmFiber44StateAt 3 ∈ closeChainFiber mmWord mmFiber44DirectStates (2 + 62) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 2 62 [mmFiber44StateAt 0] (mmFiber44StateAt 3) h2

theorem mmFiber44State4_in_close :
    mmFiber44StateAt 4 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 2 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 2) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep2
  have h2 : mmFiber44StateAt 4 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 2) (mmFiber44StateAt 4) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep4
  change mmFiber44StateAt 4 ∈ closeChainFiber mmWord mmFiber44DirectStates (2 + 62) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 2 62 [mmFiber44StateAt 0] (mmFiber44StateAt 4) h2

theorem mmFiber44State5_in_close :
    mmFiber44StateAt 5 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 7 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 7) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep7
  have h2 : mmFiber44StateAt 5 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 7) (mmFiber44StateAt 5) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep5
  change mmFiber44StateAt 5 ∈ closeChainFiber mmWord mmFiber44DirectStates (2 + 62) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 2 62 [mmFiber44StateAt 0] (mmFiber44StateAt 5) h2

theorem mmFiber44State6_in_close :
    mmFiber44StateAt 6 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 1 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 1) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep1
  have h2 : mmFiber44StateAt 6 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 1) (mmFiber44StateAt 6) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep6
  change mmFiber44StateAt 6 ∈ closeChainFiber mmWord mmFiber44DirectStates (2 + 62) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 2 62 [mmFiber44StateAt 0] (mmFiber44StateAt 6) h2

theorem mmFiber44State7_in_close :
    mmFiber44StateAt 7 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 7 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 7) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep7
  change mmFiber44StateAt 7 ∈ closeChainFiber mmWord mmFiber44DirectStates (1 + 63) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 1 63 [mmFiber44StateAt 0] (mmFiber44StateAt 7) h1

theorem mmFiber44State8_in_close :
    mmFiber44StateAt 8 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 8 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 8) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep8
  change mmFiber44StateAt 8 ∈ closeChainFiber mmWord mmFiber44DirectStates (1 + 63) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 1 63 [mmFiber44StateAt 0] (mmFiber44StateAt 8) h1

theorem mmFiber44State9_in_close :
    mmFiber44StateAt 9 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 1 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 1) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep1
  have h2 : mmFiber44StateAt 9 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 1) (mmFiber44StateAt 9) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep9
  change mmFiber44StateAt 9 ∈ closeChainFiber mmWord mmFiber44DirectStates (2 + 62) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 2 62 [mmFiber44StateAt 0] (mmFiber44StateAt 9) h2

theorem mmFiber44State10_in_close :
    mmFiber44StateAt 10 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 2 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 2) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep2
  have h2 : mmFiber44StateAt 10 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 2) (mmFiber44StateAt 10) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep10
  change mmFiber44StateAt 10 ∈ closeChainFiber mmWord mmFiber44DirectStates (2 + 62) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 2 62 [mmFiber44StateAt 0] (mmFiber44StateAt 10) h2

theorem mmFiber44State11_in_close :
    mmFiber44StateAt 11 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 1 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 1) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep1
  have h2 : mmFiber44StateAt 3 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 1) (mmFiber44StateAt 3) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep3
  have h3 : mmFiber44StateAt 11 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 3) (mmFiber44StateAt 11) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep11
  change mmFiber44StateAt 11 ∈ closeChainFiber mmWord mmFiber44DirectStates (3 + 61) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 3 61 [mmFiber44StateAt 0] (mmFiber44StateAt 11) h3

theorem mmFiber44State12_in_close :
    mmFiber44StateAt 12 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 2 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 2) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep2
  have h2 : mmFiber44StateAt 4 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 2) (mmFiber44StateAt 4) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep4
  have h3 : mmFiber44StateAt 12 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 4) (mmFiber44StateAt 12) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep12
  change mmFiber44StateAt 12 ∈ closeChainFiber mmWord mmFiber44DirectStates (3 + 61) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 3 61 [mmFiber44StateAt 0] (mmFiber44StateAt 12) h3

theorem mmFiber44State13_in_close :
    mmFiber44StateAt 13 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 7 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 7) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep7
  have h2 : mmFiber44StateAt 5 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 7) (mmFiber44StateAt 5) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep5
  have h3 : mmFiber44StateAt 13 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 5) (mmFiber44StateAt 13) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep13
  change mmFiber44StateAt 13 ∈ closeChainFiber mmWord mmFiber44DirectStates (3 + 61) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 3 61 [mmFiber44StateAt 0] (mmFiber44StateAt 13) h3

theorem mmFiber44State14_in_close :
    mmFiber44StateAt 14 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 1 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 1) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep1
  have h2 : mmFiber44StateAt 6 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 1) (mmFiber44StateAt 6) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep6
  have h3 : mmFiber44StateAt 14 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 6) (mmFiber44StateAt 14) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep14
  change mmFiber44StateAt 14 ∈ closeChainFiber mmWord mmFiber44DirectStates (3 + 61) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 3 61 [mmFiber44StateAt 0] (mmFiber44StateAt 14) h3

theorem mmFiber44State15_in_close :
    mmFiber44StateAt 15 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 7 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 7) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep7
  have h2 : mmFiber44StateAt 15 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 7) (mmFiber44StateAt 15) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep15
  change mmFiber44StateAt 15 ∈ closeChainFiber mmWord mmFiber44DirectStates (2 + 62) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 2 62 [mmFiber44StateAt 0] (mmFiber44StateAt 15) h2

theorem mmFiber44State16_in_close :
    mmFiber44StateAt 16 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 16 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 16) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep16
  change mmFiber44StateAt 16 ∈ closeChainFiber mmWord mmFiber44DirectStates (1 + 63) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 1 63 [mmFiber44StateAt 0] (mmFiber44StateAt 16) h1

theorem mmFiber44State17_in_close :
    mmFiber44StateAt 17 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 1 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 1) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep1
  have h2 : mmFiber44StateAt 17 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 1) (mmFiber44StateAt 17) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep17
  change mmFiber44StateAt 17 ∈ closeChainFiber mmWord mmFiber44DirectStates (2 + 62) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 2 62 [mmFiber44StateAt 0] (mmFiber44StateAt 17) h2

theorem mmFiber44State18_in_close :
    mmFiber44StateAt 18 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 2 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 2) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep2
  have h2 : mmFiber44StateAt 18 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 2) (mmFiber44StateAt 18) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep18
  change mmFiber44StateAt 18 ∈ closeChainFiber mmWord mmFiber44DirectStates (2 + 62) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 2 62 [mmFiber44StateAt 0] (mmFiber44StateAt 18) h2

theorem mmFiber44State19_in_close :
    mmFiber44StateAt 19 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 1 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 1) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep1
  have h2 : mmFiber44StateAt 3 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 1) (mmFiber44StateAt 3) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep3
  have h3 : mmFiber44StateAt 19 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 3) (mmFiber44StateAt 19) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep19
  change mmFiber44StateAt 19 ∈ closeChainFiber mmWord mmFiber44DirectStates (3 + 61) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 3 61 [mmFiber44StateAt 0] (mmFiber44StateAt 19) h3

theorem mmFiber44State20_in_close :
    mmFiber44StateAt 20 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 16 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 16) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep16
  have h2 : mmFiber44StateAt 20 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 16) (mmFiber44StateAt 20) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep20
  change mmFiber44StateAt 20 ∈ closeChainFiber mmWord mmFiber44DirectStates (2 + 62) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 2 62 [mmFiber44StateAt 0] (mmFiber44StateAt 20) h2

theorem mmFiber44State21_in_close :
    mmFiber44StateAt 21 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 1 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 1) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep1
  have h2 : mmFiber44StateAt 17 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 1) (mmFiber44StateAt 17) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep17
  have h3 : mmFiber44StateAt 21 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 17) (mmFiber44StateAt 21) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep21
  change mmFiber44StateAt 21 ∈ closeChainFiber mmWord mmFiber44DirectStates (3 + 61) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 3 61 [mmFiber44StateAt 0] (mmFiber44StateAt 21) h3

theorem mmFiber44State22_in_close :
    mmFiber44StateAt 22 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 1 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 1) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep1
  have h2 : mmFiber44StateAt 6 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 1) (mmFiber44StateAt 6) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep6
  have h3 : mmFiber44StateAt 22 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 6) (mmFiber44StateAt 22) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep22
  change mmFiber44StateAt 22 ∈ closeChainFiber mmWord mmFiber44DirectStates (3 + 61) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 3 61 [mmFiber44StateAt 0] (mmFiber44StateAt 22) h3

theorem mmFiber44State23_in_close :
    mmFiber44StateAt 23 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 7 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 7) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep7
  have h2 : mmFiber44StateAt 23 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 7) (mmFiber44StateAt 23) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep23
  change mmFiber44StateAt 23 ∈ closeChainFiber mmWord mmFiber44DirectStates (2 + 62) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 2 62 [mmFiber44StateAt 0] (mmFiber44StateAt 23) h2

theorem mmFiber44State24_in_close :
    mmFiber44StateAt 24 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 8 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 8) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep8
  have h2 : mmFiber44StateAt 24 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 8) (mmFiber44StateAt 24) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep24
  change mmFiber44StateAt 24 ∈ closeChainFiber mmWord mmFiber44DirectStates (2 + 62) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 2 62 [mmFiber44StateAt 0] (mmFiber44StateAt 24) h2

theorem mmFiber44State25_in_close :
    mmFiber44StateAt 25 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 1 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 1) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep1
  have h2 : mmFiber44StateAt 9 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 1) (mmFiber44StateAt 9) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep9
  have h3 : mmFiber44StateAt 25 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 9) (mmFiber44StateAt 25) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep25
  change mmFiber44StateAt 25 ∈ closeChainFiber mmWord mmFiber44DirectStates (3 + 61) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 3 61 [mmFiber44StateAt 0] (mmFiber44StateAt 25) h3

theorem mmFiber44State26_in_close :
    mmFiber44StateAt 26 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 2 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 2) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep2
  have h2 : mmFiber44StateAt 10 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 2) (mmFiber44StateAt 10) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep10
  have h3 : mmFiber44StateAt 26 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 10) (mmFiber44StateAt 26) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep26
  change mmFiber44StateAt 26 ∈ closeChainFiber mmWord mmFiber44DirectStates (3 + 61) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 3 61 [mmFiber44StateAt 0] (mmFiber44StateAt 26) h3

theorem mmFiber44State27_in_close :
    mmFiber44StateAt 27 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 1 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 1) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep1
  have h2 : mmFiber44StateAt 3 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 1) (mmFiber44StateAt 3) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep3
  have h3 : mmFiber44StateAt 11 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 3) (mmFiber44StateAt 11) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep11
  have h4 : mmFiber44StateAt 27 ∈ closeChainFiber mmWord mmFiber44DirectStates 4 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0]
      (mmFiber44StateAt 11) (mmFiber44StateAt 27) (by decide) h3 (by decide)
      mmFiber44ReverseSingleStep27
  change mmFiber44StateAt 27 ∈ closeChainFiber mmWord mmFiber44DirectStates (4 + 60) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 4 60 [mmFiber44StateAt 0] (mmFiber44StateAt 27) h4

theorem mmFiber44State28_in_close :
    mmFiber44StateAt 28 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 8 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 8) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep8
  have h2 : mmFiber44StateAt 24 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 8) (mmFiber44StateAt 24) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep24
  have h3 : mmFiber44StateAt 28 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 24) (mmFiber44StateAt 28) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep28
  change mmFiber44StateAt 28 ∈ closeChainFiber mmWord mmFiber44DirectStates (3 + 61) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 3 61 [mmFiber44StateAt 0] (mmFiber44StateAt 28) h3

theorem mmFiber44State29_in_close :
    mmFiber44StateAt 29 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 1 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 1) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep1
  have h2 : mmFiber44StateAt 9 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 1) (mmFiber44StateAt 9) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep9
  have h3 : mmFiber44StateAt 25 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 9) (mmFiber44StateAt 25) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep25
  have h4 : mmFiber44StateAt 29 ∈ closeChainFiber mmWord mmFiber44DirectStates 4 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0]
      (mmFiber44StateAt 25) (mmFiber44StateAt 29) (by decide) h3 (by decide)
      mmFiber44ReverseSingleStep29
  change mmFiber44StateAt 29 ∈ closeChainFiber mmWord mmFiber44DirectStates (4 + 60) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 4 60 [mmFiber44StateAt 0] (mmFiber44StateAt 29) h4

theorem mmFiber44State30_in_close :
    mmFiber44StateAt 30 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 1 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 1) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep1
  have h2 : mmFiber44StateAt 6 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 1) (mmFiber44StateAt 6) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep6
  have h3 : mmFiber44StateAt 14 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 6) (mmFiber44StateAt 14) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep14
  have h4 : mmFiber44StateAt 30 ∈ closeChainFiber mmWord mmFiber44DirectStates 4 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0]
      (mmFiber44StateAt 14) (mmFiber44StateAt 30) (by decide) h3 (by decide)
      mmFiber44ReverseSingleStep30
  change mmFiber44StateAt 30 ∈ closeChainFiber mmWord mmFiber44DirectStates (4 + 60) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 4 60 [mmFiber44StateAt 0] (mmFiber44StateAt 30) h4

theorem mmFiber44State31_in_close :
    mmFiber44StateAt 31 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 7 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 7) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep7
  have h2 : mmFiber44StateAt 15 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 7) (mmFiber44StateAt 15) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep15
  have h3 : mmFiber44StateAt 31 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 15) (mmFiber44StateAt 31) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep31
  change mmFiber44StateAt 31 ∈ closeChainFiber mmWord mmFiber44DirectStates (3 + 61) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 3 61 [mmFiber44StateAt 0] (mmFiber44StateAt 31) h3

theorem mmFiber44State32_in_close :
    mmFiber44StateAt 32 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 8 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 8) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep8
  have h2 : mmFiber44StateAt 48 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 8) (mmFiber44StateAt 48) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep48
  have h3 : mmFiber44StateAt 32 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 48) (mmFiber44StateAt 32) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep32
  change mmFiber44StateAt 32 ∈ closeChainFiber mmWord mmFiber44DirectStates (3 + 61) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 3 61 [mmFiber44StateAt 0] (mmFiber44StateAt 32) h3

theorem mmFiber44State33_in_close :
    mmFiber44StateAt 33 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 1 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 1) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep1
  have h2 : mmFiber44StateAt 9 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 1) (mmFiber44StateAt 9) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep9
  have h3 : mmFiber44StateAt 49 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 9) (mmFiber44StateAt 49) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep49
  have h4 : mmFiber44StateAt 33 ∈ closeChainFiber mmWord mmFiber44DirectStates 4 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0]
      (mmFiber44StateAt 49) (mmFiber44StateAt 33) (by decide) h3 (by decide)
      mmFiber44ReverseSingleStep33
  change mmFiber44StateAt 33 ∈ closeChainFiber mmWord mmFiber44DirectStates (4 + 60) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 4 60 [mmFiber44StateAt 0] (mmFiber44StateAt 33) h4

theorem mmFiber44State34_in_close :
    mmFiber44StateAt 34 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 1 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 1) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep1
  have h2 : mmFiber44StateAt 6 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 1) (mmFiber44StateAt 6) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep6
  have h3 : mmFiber44StateAt 22 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 6) (mmFiber44StateAt 22) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep22
  have h4 : mmFiber44StateAt 34 ∈ closeChainFiber mmWord mmFiber44DirectStates 4 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0]
      (mmFiber44StateAt 22) (mmFiber44StateAt 34) (by decide) h3 (by decide)
      mmFiber44ReverseSingleStep34
  change mmFiber44StateAt 34 ∈ closeChainFiber mmWord mmFiber44DirectStates (4 + 60) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 4 60 [mmFiber44StateAt 0] (mmFiber44StateAt 34) h4

theorem mmFiber44State35_in_close :
    mmFiber44StateAt 35 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 7 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 7) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep7
  have h2 : mmFiber44StateAt 23 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 7) (mmFiber44StateAt 23) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep23
  have h3 : mmFiber44StateAt 35 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 23) (mmFiber44StateAt 35) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep35
  change mmFiber44StateAt 35 ∈ closeChainFiber mmWord mmFiber44DirectStates (3 + 61) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 3 61 [mmFiber44StateAt 0] (mmFiber44StateAt 35) h3

theorem mmFiber44State36_in_close :
    mmFiber44StateAt 36 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 2 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 2) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep2
  have h2 : mmFiber44StateAt 18 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 2) (mmFiber44StateAt 18) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep18
  have h3 : mmFiber44StateAt 36 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 18) (mmFiber44StateAt 36) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep36
  change mmFiber44StateAt 36 ∈ closeChainFiber mmWord mmFiber44DirectStates (3 + 61) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 3 61 [mmFiber44StateAt 0] (mmFiber44StateAt 36) h3

theorem mmFiber44State37_in_close :
    mmFiber44StateAt 37 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 16 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 16) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep16
  have h2 : mmFiber44StateAt 39 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 16) (mmFiber44StateAt 39) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep39
  have h3 : mmFiber44StateAt 37 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 39) (mmFiber44StateAt 37) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep37
  change mmFiber44StateAt 37 ∈ closeChainFiber mmWord mmFiber44DirectStates (3 + 61) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 3 61 [mmFiber44StateAt 0] (mmFiber44StateAt 37) h3

theorem mmFiber44State38_in_close :
    mmFiber44StateAt 38 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 1 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 1) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep1
  have h2 : mmFiber44StateAt 17 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 1) (mmFiber44StateAt 17) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep17
  have h3 : mmFiber44StateAt 38 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 17) (mmFiber44StateAt 38) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep38
  change mmFiber44StateAt 38 ∈ closeChainFiber mmWord mmFiber44DirectStates (3 + 61) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 3 61 [mmFiber44StateAt 0] (mmFiber44StateAt 38) h3

theorem mmFiber44State39_in_close :
    mmFiber44StateAt 39 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 16 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 16) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep16
  have h2 : mmFiber44StateAt 39 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 16) (mmFiber44StateAt 39) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep39
  change mmFiber44StateAt 39 ∈ closeChainFiber mmWord mmFiber44DirectStates (2 + 62) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 2 62 [mmFiber44StateAt 0] (mmFiber44StateAt 39) h2

theorem mmFiber44State40_in_close :
    mmFiber44StateAt 40 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 56 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 56) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep56
  have h2 : mmFiber44StateAt 40 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 56) (mmFiber44StateAt 40) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep40
  change mmFiber44StateAt 40 ∈ closeChainFiber mmWord mmFiber44DirectStates (2 + 62) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 2 62 [mmFiber44StateAt 0] (mmFiber44StateAt 40) h2

theorem mmFiber44State41_in_close :
    mmFiber44StateAt 41 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 1 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 1) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep1
  have h2 : mmFiber44StateAt 57 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 1) (mmFiber44StateAt 57) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep57
  have h3 : mmFiber44StateAt 41 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 57) (mmFiber44StateAt 41) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep41
  change mmFiber44StateAt 41 ∈ closeChainFiber mmWord mmFiber44DirectStates (3 + 61) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 3 61 [mmFiber44StateAt 0] (mmFiber44StateAt 41) h3

theorem mmFiber44State42_in_close :
    mmFiber44StateAt 42 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 2 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 2) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep2
  have h2 : mmFiber44StateAt 58 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 2) (mmFiber44StateAt 58) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep58
  have h3 : mmFiber44StateAt 42 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 58) (mmFiber44StateAt 42) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep42
  change mmFiber44StateAt 42 ∈ closeChainFiber mmWord mmFiber44DirectStates (3 + 61) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 3 61 [mmFiber44StateAt 0] (mmFiber44StateAt 42) h3

theorem mmFiber44State43_in_close :
    mmFiber44StateAt 43 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 56 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 56) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep56
  have h2 : mmFiber44StateAt 40 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 56) (mmFiber44StateAt 40) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep40
  have h3 : mmFiber44StateAt 43 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 40) (mmFiber44StateAt 43) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep43
  change mmFiber44StateAt 43 ∈ closeChainFiber mmWord mmFiber44DirectStates (3 + 61) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 3 61 [mmFiber44StateAt 0] (mmFiber44StateAt 43) h3

theorem mmFiber44State44_in_close :
    mmFiber44StateAt 44 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 56 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 56) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep56
  have h2 : mmFiber44StateAt 40 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 56) (mmFiber44StateAt 40) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep40
  have h3 : mmFiber44StateAt 44 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 40) (mmFiber44StateAt 44) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep44
  change mmFiber44StateAt 44 ∈ closeChainFiber mmWord mmFiber44DirectStates (3 + 61) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 3 61 [mmFiber44StateAt 0] (mmFiber44StateAt 44) h3

theorem mmFiber44State45_in_close :
    mmFiber44StateAt 45 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 1 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 1) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep1
  have h2 : mmFiber44StateAt 57 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 1) (mmFiber44StateAt 57) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep57
  have h3 : mmFiber44StateAt 41 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 57) (mmFiber44StateAt 41) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep41
  have h4 : mmFiber44StateAt 45 ∈ closeChainFiber mmWord mmFiber44DirectStates 4 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0]
      (mmFiber44StateAt 41) (mmFiber44StateAt 45) (by decide) h3 (by decide)
      mmFiber44ReverseSingleStep45
  change mmFiber44StateAt 45 ∈ closeChainFiber mmWord mmFiber44DirectStates (4 + 60) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 4 60 [mmFiber44StateAt 0] (mmFiber44StateAt 45) h4

theorem mmFiber44State46_in_close :
    mmFiber44StateAt 46 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 1 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 1) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep1
  have h2 : mmFiber44StateAt 6 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 1) (mmFiber44StateAt 6) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep6
  have h3 : mmFiber44StateAt 62 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 6) (mmFiber44StateAt 62) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep62
  have h4 : mmFiber44StateAt 46 ∈ closeChainFiber mmWord mmFiber44DirectStates 4 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0]
      (mmFiber44StateAt 62) (mmFiber44StateAt 46) (by decide) h3 (by decide)
      mmFiber44ReverseSingleStep46
  change mmFiber44StateAt 46 ∈ closeChainFiber mmWord mmFiber44DirectStates (4 + 60) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 4 60 [mmFiber44StateAt 0] (mmFiber44StateAt 46) h4

theorem mmFiber44State47_in_close :
    mmFiber44StateAt 47 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 7 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 7) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep7
  have h2 : mmFiber44StateAt 63 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 7) (mmFiber44StateAt 63) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep63
  have h3 : mmFiber44StateAt 47 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 63) (mmFiber44StateAt 47) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep47
  change mmFiber44StateAt 47 ∈ closeChainFiber mmWord mmFiber44DirectStates (3 + 61) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 3 61 [mmFiber44StateAt 0] (mmFiber44StateAt 47) h3

theorem mmFiber44State48_in_close :
    mmFiber44StateAt 48 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 8 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 8) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep8
  have h2 : mmFiber44StateAt 48 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 8) (mmFiber44StateAt 48) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep48
  change mmFiber44StateAt 48 ∈ closeChainFiber mmWord mmFiber44DirectStates (2 + 62) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 2 62 [mmFiber44StateAt 0] (mmFiber44StateAt 48) h2

theorem mmFiber44State49_in_close :
    mmFiber44StateAt 49 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 1 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 1) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep1
  have h2 : mmFiber44StateAt 9 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 1) (mmFiber44StateAt 9) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep9
  have h3 : mmFiber44StateAt 49 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 9) (mmFiber44StateAt 49) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep49
  change mmFiber44StateAt 49 ∈ closeChainFiber mmWord mmFiber44DirectStates (3 + 61) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 3 61 [mmFiber44StateAt 0] (mmFiber44StateAt 49) h3

theorem mmFiber44State50_in_close :
    mmFiber44StateAt 50 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 2 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 2) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep2
  have h2 : mmFiber44StateAt 10 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 2) (mmFiber44StateAt 10) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep10
  have h3 : mmFiber44StateAt 50 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 10) (mmFiber44StateAt 50) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep50
  change mmFiber44StateAt 50 ∈ closeChainFiber mmWord mmFiber44DirectStates (3 + 61) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 3 61 [mmFiber44StateAt 0] (mmFiber44StateAt 50) h3

theorem mmFiber44State51_in_close :
    mmFiber44StateAt 51 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 1 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 1) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep1
  have h2 : mmFiber44StateAt 3 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 1) (mmFiber44StateAt 3) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep3
  have h3 : mmFiber44StateAt 11 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 3) (mmFiber44StateAt 11) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep11
  have h4 : mmFiber44StateAt 51 ∈ closeChainFiber mmWord mmFiber44DirectStates 4 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0]
      (mmFiber44StateAt 11) (mmFiber44StateAt 51) (by decide) h3 (by decide)
      mmFiber44ReverseSingleStep51
  change mmFiber44StateAt 51 ∈ closeChainFiber mmWord mmFiber44DirectStates (4 + 60) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 4 60 [mmFiber44StateAt 0] (mmFiber44StateAt 51) h4

theorem mmFiber44State52_in_close :
    mmFiber44StateAt 52 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 2 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 2) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep2
  have h2 : mmFiber44StateAt 4 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 2) (mmFiber44StateAt 4) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep4
  have h3 : mmFiber44StateAt 12 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 4) (mmFiber44StateAt 12) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep12
  have h4 : mmFiber44StateAt 52 ∈ closeChainFiber mmWord mmFiber44DirectStates 4 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0]
      (mmFiber44StateAt 12) (mmFiber44StateAt 52) (by decide) h3 (by decide)
      mmFiber44ReverseSingleStep52
  change mmFiber44StateAt 52 ∈ closeChainFiber mmWord mmFiber44DirectStates (4 + 60) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 4 60 [mmFiber44StateAt 0] (mmFiber44StateAt 52) h4

theorem mmFiber44State53_in_close :
    mmFiber44StateAt 53 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 7 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 7) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep7
  have h2 : mmFiber44StateAt 5 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 7) (mmFiber44StateAt 5) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep5
  have h3 : mmFiber44StateAt 13 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 5) (mmFiber44StateAt 13) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep13
  have h4 : mmFiber44StateAt 53 ∈ closeChainFiber mmWord mmFiber44DirectStates 4 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0]
      (mmFiber44StateAt 13) (mmFiber44StateAt 53) (by decide) h3 (by decide)
      mmFiber44ReverseSingleStep53
  change mmFiber44StateAt 53 ∈ closeChainFiber mmWord mmFiber44DirectStates (4 + 60) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 4 60 [mmFiber44StateAt 0] (mmFiber44StateAt 53) h4

theorem mmFiber44State54_in_close :
    mmFiber44StateAt 54 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 1 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 1) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep1
  have h2 : mmFiber44StateAt 6 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 1) (mmFiber44StateAt 6) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep6
  have h3 : mmFiber44StateAt 14 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 6) (mmFiber44StateAt 14) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep14
  have h4 : mmFiber44StateAt 54 ∈ closeChainFiber mmWord mmFiber44DirectStates 4 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0]
      (mmFiber44StateAt 14) (mmFiber44StateAt 54) (by decide) h3 (by decide)
      mmFiber44ReverseSingleStep54
  change mmFiber44StateAt 54 ∈ closeChainFiber mmWord mmFiber44DirectStates (4 + 60) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 4 60 [mmFiber44StateAt 0] (mmFiber44StateAt 54) h4

theorem mmFiber44State55_in_close :
    mmFiber44StateAt 55 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 7 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 7) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep7
  have h2 : mmFiber44StateAt 15 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 7) (mmFiber44StateAt 15) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep15
  have h3 : mmFiber44StateAt 55 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 15) (mmFiber44StateAt 55) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep55
  change mmFiber44StateAt 55 ∈ closeChainFiber mmWord mmFiber44DirectStates (3 + 61) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 3 61 [mmFiber44StateAt 0] (mmFiber44StateAt 55) h3

theorem mmFiber44State56_in_close :
    mmFiber44StateAt 56 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 56 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 56) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep56
  change mmFiber44StateAt 56 ∈ closeChainFiber mmWord mmFiber44DirectStates (1 + 63) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 1 63 [mmFiber44StateAt 0] (mmFiber44StateAt 56) h1

theorem mmFiber44State57_in_close :
    mmFiber44StateAt 57 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 1 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 1) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep1
  have h2 : mmFiber44StateAt 57 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 1) (mmFiber44StateAt 57) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep57
  change mmFiber44StateAt 57 ∈ closeChainFiber mmWord mmFiber44DirectStates (2 + 62) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 2 62 [mmFiber44StateAt 0] (mmFiber44StateAt 57) h2

theorem mmFiber44State58_in_close :
    mmFiber44StateAt 58 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 2 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 2) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep2
  have h2 : mmFiber44StateAt 58 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 2) (mmFiber44StateAt 58) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep58
  change mmFiber44StateAt 58 ∈ closeChainFiber mmWord mmFiber44DirectStates (2 + 62) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 2 62 [mmFiber44StateAt 0] (mmFiber44StateAt 58) h2

theorem mmFiber44State59_in_close :
    mmFiber44StateAt 59 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 1 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 1) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep1
  have h2 : mmFiber44StateAt 3 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 1) (mmFiber44StateAt 3) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep3
  have h3 : mmFiber44StateAt 59 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 3) (mmFiber44StateAt 59) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep59
  change mmFiber44StateAt 59 ∈ closeChainFiber mmWord mmFiber44DirectStates (3 + 61) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 3 61 [mmFiber44StateAt 0] (mmFiber44StateAt 59) h3

theorem mmFiber44State60_in_close :
    mmFiber44StateAt 60 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 2 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 2) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep2
  have h2 : mmFiber44StateAt 4 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 2) (mmFiber44StateAt 4) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep4
  have h3 : mmFiber44StateAt 60 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 4) (mmFiber44StateAt 60) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep60
  change mmFiber44StateAt 60 ∈ closeChainFiber mmWord mmFiber44DirectStates (3 + 61) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 3 61 [mmFiber44StateAt 0] (mmFiber44StateAt 60) h3

theorem mmFiber44State61_in_close :
    mmFiber44StateAt 61 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 7 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 7) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep7
  have h2 : mmFiber44StateAt 5 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 7) (mmFiber44StateAt 5) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep5
  have h3 : mmFiber44StateAt 61 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 5) (mmFiber44StateAt 61) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep61
  change mmFiber44StateAt 61 ∈ closeChainFiber mmWord mmFiber44DirectStates (3 + 61) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 3 61 [mmFiber44StateAt 0] (mmFiber44StateAt 61) h3

theorem mmFiber44State62_in_close :
    mmFiber44StateAt 62 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 1 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 1) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep1
  have h2 : mmFiber44StateAt 6 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 1) (mmFiber44StateAt 6) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep6
  have h3 : mmFiber44StateAt 62 ∈ closeChainFiber mmWord mmFiber44DirectStates 3 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0]
      (mmFiber44StateAt 6) (mmFiber44StateAt 62) (by decide) h2 (by decide)
      mmFiber44ReverseSingleStep62
  change mmFiber44StateAt 62 ∈ closeChainFiber mmWord mmFiber44DirectStates (3 + 61) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 3 61 [mmFiber44StateAt 0] (mmFiber44StateAt 62) h3

theorem mmFiber44State63_in_close :
    mmFiber44StateAt 63 ∈ closeChainFiber mmWord mmFiber44DirectStates mmFiber44DirectStates.length [mmFiber44StateAt 0] := by
  have h0 : mmFiber44StateAt 0 ∈ closeChainFiber mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber44StateAt 7 ∈ closeChainFiber mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 0 [mmFiber44StateAt 0]
      (mmFiber44StateAt 0) (mmFiber44StateAt 7) (by decide) h0 (by decide)
      mmFiber44ReverseSingleStep7
  have h2 : mmFiber44StateAt 63 ∈ closeChainFiber mmWord mmFiber44DirectStates 2 [mmFiber44StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber44DirectStates 1 [mmFiber44StateAt 0]
      (mmFiber44StateAt 7) (mmFiber44StateAt 63) (by decide) h1 (by decide)
      mmFiber44ReverseSingleStep63
  change mmFiber44StateAt 63 ∈ closeChainFiber mmWord mmFiber44DirectStates (2 + 62) [mmFiber44StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber44DirectStates 2 62 [mmFiber44StateAt 0] (mmFiber44StateAt 63) h2

theorem mmFiber44DirectConnected :
    chainFiberConnected mmWord mmFiber44DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber44DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber44State0_in_close
  · subst state
    exact mmFiber44State1_in_close
  · subst state
    exact mmFiber44State2_in_close
  · subst state
    exact mmFiber44State3_in_close
  · subst state
    exact mmFiber44State4_in_close
  · subst state
    exact mmFiber44State5_in_close
  · subst state
    exact mmFiber44State6_in_close
  · subst state
    exact mmFiber44State7_in_close
  · subst state
    exact mmFiber44State8_in_close
  · subst state
    exact mmFiber44State9_in_close
  · subst state
    exact mmFiber44State10_in_close
  · subst state
    exact mmFiber44State11_in_close
  · subst state
    exact mmFiber44State12_in_close
  · subst state
    exact mmFiber44State13_in_close
  · subst state
    exact mmFiber44State14_in_close
  · subst state
    exact mmFiber44State15_in_close
  · subst state
    exact mmFiber44State16_in_close
  · subst state
    exact mmFiber44State17_in_close
  · subst state
    exact mmFiber44State18_in_close
  · subst state
    exact mmFiber44State19_in_close
  · subst state
    exact mmFiber44State20_in_close
  · subst state
    exact mmFiber44State21_in_close
  · subst state
    exact mmFiber44State22_in_close
  · subst state
    exact mmFiber44State23_in_close
  · subst state
    exact mmFiber44State24_in_close
  · subst state
    exact mmFiber44State25_in_close
  · subst state
    exact mmFiber44State26_in_close
  · subst state
    exact mmFiber44State27_in_close
  · subst state
    exact mmFiber44State28_in_close
  · subst state
    exact mmFiber44State29_in_close
  · subst state
    exact mmFiber44State30_in_close
  · subst state
    exact mmFiber44State31_in_close
  · subst state
    exact mmFiber44State32_in_close
  · subst state
    exact mmFiber44State33_in_close
  · subst state
    exact mmFiber44State34_in_close
  · subst state
    exact mmFiber44State35_in_close
  · subst state
    exact mmFiber44State36_in_close
  · subst state
    exact mmFiber44State37_in_close
  · subst state
    exact mmFiber44State38_in_close
  · subst state
    exact mmFiber44State39_in_close
  · subst state
    exact mmFiber44State40_in_close
  · subst state
    exact mmFiber44State41_in_close
  · subst state
    exact mmFiber44State42_in_close
  · subst state
    exact mmFiber44State43_in_close
  · subst state
    exact mmFiber44State44_in_close
  · subst state
    exact mmFiber44State45_in_close
  · subst state
    exact mmFiber44State46_in_close
  · subst state
    exact mmFiber44State47_in_close
  · subst state
    exact mmFiber44State48_in_close
  · subst state
    exact mmFiber44State49_in_close
  · subst state
    exact mmFiber44State50_in_close
  · subst state
    exact mmFiber44State51_in_close
  · subst state
    exact mmFiber44State52_in_close
  · subst state
    exact mmFiber44State53_in_close
  · subst state
    exact mmFiber44State54_in_close
  · subst state
    exact mmFiber44State55_in_close
  · subst state
    exact mmFiber44State56_in_close
  · subst state
    exact mmFiber44State57_in_close
  · subst state
    exact mmFiber44State58_in_close
  · subst state
    exact mmFiber44State59_in_close
  · subst state
    exact mmFiber44State60_in_close
  · subst state
    exact mmFiber44State61_in_close
  · subst state
    exact mmFiber44State62_in_close
  · subst state
    exact mmFiber44State63_in_close
  · cases h
end GoertzelLemma818LengthTwoMMBridge

end Mettapedia.GraphTheory.FourColor
