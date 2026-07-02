import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for `mirror,mirror` size-64 fiber 50

This module proves direct connectedness for one generated size-64 fiber from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMMBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorMirrorCertificate
open GoertzelLemma818MirrorMirrorReverseAudit

def mmFiber50StateAt (i : Nat) : List TauState :=
  directStates (mmFiber50RowAt i).sourceLeft (mmFiber50RowAt i).sourceRight

def mmFiber50DirectStates : List (List TauState) :=
  [mmFiber50StateAt 0, mmFiber50StateAt 1, mmFiber50StateAt 2, mmFiber50StateAt 3, mmFiber50StateAt 4, mmFiber50StateAt 5, mmFiber50StateAt 6, mmFiber50StateAt 7, mmFiber50StateAt 8, mmFiber50StateAt 9, mmFiber50StateAt 10, mmFiber50StateAt 11, mmFiber50StateAt 12, mmFiber50StateAt 13, mmFiber50StateAt 14, mmFiber50StateAt 15, mmFiber50StateAt 16, mmFiber50StateAt 17, mmFiber50StateAt 18, mmFiber50StateAt 19, mmFiber50StateAt 20, mmFiber50StateAt 21, mmFiber50StateAt 22, mmFiber50StateAt 23, mmFiber50StateAt 24, mmFiber50StateAt 25, mmFiber50StateAt 26, mmFiber50StateAt 27, mmFiber50StateAt 28, mmFiber50StateAt 29, mmFiber50StateAt 30, mmFiber50StateAt 31, mmFiber50StateAt 32, mmFiber50StateAt 33, mmFiber50StateAt 34, mmFiber50StateAt 35, mmFiber50StateAt 36, mmFiber50StateAt 37, mmFiber50StateAt 38, mmFiber50StateAt 39, mmFiber50StateAt 40, mmFiber50StateAt 41, mmFiber50StateAt 42, mmFiber50StateAt 43, mmFiber50StateAt 44, mmFiber50StateAt 45, mmFiber50StateAt 46, mmFiber50StateAt 47, mmFiber50StateAt 48, mmFiber50StateAt 49, mmFiber50StateAt 50, mmFiber50StateAt 51, mmFiber50StateAt 52, mmFiber50StateAt 53, mmFiber50StateAt 54, mmFiber50StateAt 55, mmFiber50StateAt 56, mmFiber50StateAt 57, mmFiber50StateAt 58, mmFiber50StateAt 59, mmFiber50StateAt 60, mmFiber50StateAt 61, mmFiber50StateAt 62, mmFiber50StateAt 63]

theorem mmFiber50ReverseRow_1_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk0_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 0) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 0) (mmFiber50StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 0) (mmFiber50StateAt 1)
    (mmFiber50RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 1) (by decide) mmFiber50ReverseRow_1_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_2_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk1_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 2) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber50ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 0) (mmFiber50StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 0) (mmFiber50StateAt 2)
    (mmFiber50RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 2) (by decide) mmFiber50ReverseRow_2_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_3_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk1_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 2) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 1) (mmFiber50StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 1) (mmFiber50StateAt 3)
    (mmFiber50RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 3) (by decide) mmFiber50ReverseRow_3_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_4_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk2_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 4) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber50ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 2) (mmFiber50StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 2) (mmFiber50StateAt 4)
    (mmFiber50RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 4) (by decide) mmFiber50ReverseRow_4_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_5_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk2_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 4) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 7) (mmFiber50StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 7) (mmFiber50StateAt 5)
    (mmFiber50RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 5) (by decide) mmFiber50ReverseRow_5_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_6_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk3_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 6) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber50ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 1) (mmFiber50StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 1) (mmFiber50StateAt 6)
    (mmFiber50RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 6) (by decide) mmFiber50ReverseRow_6_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_7_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk3_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 6) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 0) (mmFiber50StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 0) (mmFiber50StateAt 7)
    (mmFiber50RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 7) (by decide) mmFiber50ReverseRow_7_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_8_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 8) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk4_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 8) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber50ReverseSingleStep8 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 0) (mmFiber50StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 0) (mmFiber50StateAt 8)
    (mmFiber50RowAt 8).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 8) (by decide) mmFiber50ReverseRow_8_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_9_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 9) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk4_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 8) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep9 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 1) (mmFiber50StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 1) (mmFiber50StateAt 9)
    (mmFiber50RowAt 9).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 9) (by decide) mmFiber50ReverseRow_9_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_10_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 10) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk5_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 10) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber50ReverseSingleStep10 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 2) (mmFiber50StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 2) (mmFiber50StateAt 10)
    (mmFiber50RowAt 10).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 10) (by decide) mmFiber50ReverseRow_10_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_11_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 11) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk5_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 10) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep11 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 3) (mmFiber50StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 3) (mmFiber50StateAt 11)
    (mmFiber50RowAt 11).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 11) (by decide) mmFiber50ReverseRow_11_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_12_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 12) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk6_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 12) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber50ReverseSingleStep12 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 4) (mmFiber50StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 4) (mmFiber50StateAt 12)
    (mmFiber50RowAt 12).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 12) (by decide) mmFiber50ReverseRow_12_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_13_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 13) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk6_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 12) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep13 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 5) (mmFiber50StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 5) (mmFiber50StateAt 13)
    (mmFiber50RowAt 13).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 13) (by decide) mmFiber50ReverseRow_13_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_14_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 14) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk7_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 14) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber50ReverseSingleStep14 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 6) (mmFiber50StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 6) (mmFiber50StateAt 14)
    (mmFiber50RowAt 14).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 14) (by decide) mmFiber50ReverseRow_14_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_15_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 15) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk7_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 14) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep15 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 7) (mmFiber50StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 7) (mmFiber50StateAt 15)
    (mmFiber50RowAt 15).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 15) (by decide) mmFiber50ReverseRow_15_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_16_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 16) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk8_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 16) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber50ReverseSingleStep16 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 0) (mmFiber50StateAt 16) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 0) (mmFiber50StateAt 16)
    (mmFiber50RowAt 16).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 16) (by decide) mmFiber50ReverseRow_16_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_17_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 17) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk8_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 16) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep17 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 1) (mmFiber50StateAt 17) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 1) (mmFiber50StateAt 17)
    (mmFiber50RowAt 17).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 17) (by decide) mmFiber50ReverseRow_17_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_18_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 18) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk9_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 18) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber50ReverseSingleStep18 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 2) (mmFiber50StateAt 18) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 2) (mmFiber50StateAt 18)
    (mmFiber50RowAt 18).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 18) (by decide) mmFiber50ReverseRow_18_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_19_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 19) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk9_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 18) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep19 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 3) (mmFiber50StateAt 19) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 3) (mmFiber50StateAt 19)
    (mmFiber50RowAt 19).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 19) (by decide) mmFiber50ReverseRow_19_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_20_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 20) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk10_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 20) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber50ReverseSingleStep20 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 16) (mmFiber50StateAt 20) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 16) (mmFiber50StateAt 20)
    (mmFiber50RowAt 20).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 20) (by decide) mmFiber50ReverseRow_20_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_21_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 21) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk10_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 20) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep21 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 17) (mmFiber50StateAt 21) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 17) (mmFiber50StateAt 21)
    (mmFiber50RowAt 21).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 21) (by decide) mmFiber50ReverseRow_21_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_22_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 22) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk11_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 22) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber50ReverseSingleStep22 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 6) (mmFiber50StateAt 22) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 6) (mmFiber50StateAt 22)
    (mmFiber50RowAt 22).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 22) (by decide) mmFiber50ReverseRow_22_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_23_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 23) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk11_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 22) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep23 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 7) (mmFiber50StateAt 23) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 7) (mmFiber50StateAt 23)
    (mmFiber50RowAt 23).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 23) (by decide) mmFiber50ReverseRow_23_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_24_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 24) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk12_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 24) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber50ReverseSingleStep24 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 8) (mmFiber50StateAt 24) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 8) (mmFiber50StateAt 24)
    (mmFiber50RowAt 24).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 24) (by decide) mmFiber50ReverseRow_24_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_25_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 25) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk12_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 24) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep25 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 9) (mmFiber50StateAt 25) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 9) (mmFiber50StateAt 25)
    (mmFiber50RowAt 25).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 25) (by decide) mmFiber50ReverseRow_25_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_26_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 26) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk13_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 26) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber50ReverseSingleStep26 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 10) (mmFiber50StateAt 26) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 10) (mmFiber50StateAt 26)
    (mmFiber50RowAt 26).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 26) (by decide) mmFiber50ReverseRow_26_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_27_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 27) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk13_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 26) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep27 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 11) (mmFiber50StateAt 27) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 11) (mmFiber50StateAt 27)
    (mmFiber50RowAt 27).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 27) (by decide) mmFiber50ReverseRow_27_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_28_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 28) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk14_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 28) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber50ReverseSingleStep28 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 24) (mmFiber50StateAt 28) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 24) (mmFiber50StateAt 28)
    (mmFiber50RowAt 28).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 28) (by decide) mmFiber50ReverseRow_28_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_29_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 29) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk14_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 28) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep29 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 25) (mmFiber50StateAt 29) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 25) (mmFiber50StateAt 29)
    (mmFiber50RowAt 29).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 29) (by decide) mmFiber50ReverseRow_29_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_30_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 30) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk15_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 30) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber50ReverseSingleStep30 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 14) (mmFiber50StateAt 30) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 14) (mmFiber50StateAt 30)
    (mmFiber50RowAt 30).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 30) (by decide) mmFiber50ReverseRow_30_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_31_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 31) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk15_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 30) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep31 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 15) (mmFiber50StateAt 31) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 15) (mmFiber50StateAt 31)
    (mmFiber50RowAt 31).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 31) (by decide) mmFiber50ReverseRow_31_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_32_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 32) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk16_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 32) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber50ReverseSingleStep32 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 48) (mmFiber50StateAt 32) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 48) (mmFiber50StateAt 32)
    (mmFiber50RowAt 32).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 32) (by decide) mmFiber50ReverseRow_32_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_33_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 33) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk16_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 32) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep33 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 49) (mmFiber50StateAt 33) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 49) (mmFiber50StateAt 33)
    (mmFiber50RowAt 33).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 33) (by decide) mmFiber50ReverseRow_33_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_34_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 34) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk17_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 34) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber50ReverseSingleStep34 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 22) (mmFiber50StateAt 34) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 22) (mmFiber50StateAt 34)
    (mmFiber50RowAt 34).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 34) (by decide) mmFiber50ReverseRow_34_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_35_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 35) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk17_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 34) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep35 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 23) (mmFiber50StateAt 35) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 23) (mmFiber50StateAt 35)
    (mmFiber50RowAt 35).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 35) (by decide) mmFiber50ReverseRow_35_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_36_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 36) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk18_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 36) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber50ReverseSingleStep36 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 18) (mmFiber50StateAt 36) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 18) (mmFiber50StateAt 36)
    (mmFiber50RowAt 36).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 36) (by decide) mmFiber50ReverseRow_36_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_37_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 37) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk18_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 36) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep37 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 39) (mmFiber50StateAt 37) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 39) (mmFiber50StateAt 37)
    (mmFiber50RowAt 37).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 37) (by decide) mmFiber50ReverseRow_37_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_38_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 38) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk19_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 38) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber50ReverseSingleStep38 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 17) (mmFiber50StateAt 38) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 17) (mmFiber50StateAt 38)
    (mmFiber50RowAt 38).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 38) (by decide) mmFiber50ReverseRow_38_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_39_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 39) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk19_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 38) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep39 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 16) (mmFiber50StateAt 39) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 16) (mmFiber50StateAt 39)
    (mmFiber50RowAt 39).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 39) (by decide) mmFiber50ReverseRow_39_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_40_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 40) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk20_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 40) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber50ReverseSingleStep40 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 56) (mmFiber50StateAt 40) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 56) (mmFiber50StateAt 40)
    (mmFiber50RowAt 40).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 40) (by decide) mmFiber50ReverseRow_40_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_41_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 41) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk20_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 40) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep41 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 57) (mmFiber50StateAt 41) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 57) (mmFiber50StateAt 41)
    (mmFiber50RowAt 41).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 41) (by decide) mmFiber50ReverseRow_41_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_42_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 42) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk21_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 42) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber50ReverseSingleStep42 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 58) (mmFiber50StateAt 42) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 58) (mmFiber50StateAt 42)
    (mmFiber50RowAt 42).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 42) (by decide) mmFiber50ReverseRow_42_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_43_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 43) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk21_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 42) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep43 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 40) (mmFiber50StateAt 43) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 40) (mmFiber50StateAt 43)
    (mmFiber50RowAt 43).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 43) (by decide) mmFiber50ReverseRow_43_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_44_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 44) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk22_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 44) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber50ReverseSingleStep44 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 40) (mmFiber50StateAt 44) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 40) (mmFiber50StateAt 44)
    (mmFiber50RowAt 44).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 44) (by decide) mmFiber50ReverseRow_44_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_45_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 45) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk22_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 44) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep45 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 41) (mmFiber50StateAt 45) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 41) (mmFiber50StateAt 45)
    (mmFiber50RowAt 45).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 45) (by decide) mmFiber50ReverseRow_45_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_46_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 46) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk23_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 46) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber50ReverseSingleStep46 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 62) (mmFiber50StateAt 46) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 62) (mmFiber50StateAt 46)
    (mmFiber50RowAt 46).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 46) (by decide) mmFiber50ReverseRow_46_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_47_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 47) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk23_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 46) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep47 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 63) (mmFiber50StateAt 47) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 63) (mmFiber50StateAt 47)
    (mmFiber50RowAt 47).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 47) (by decide) mmFiber50ReverseRow_47_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_48_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 48) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk24_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 48) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber50ReverseSingleStep48 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 8) (mmFiber50StateAt 48) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 8) (mmFiber50StateAt 48)
    (mmFiber50RowAt 48).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 48) (by decide) mmFiber50ReverseRow_48_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_49_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 49) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk24_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 48) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep49 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 9) (mmFiber50StateAt 49) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 9) (mmFiber50StateAt 49)
    (mmFiber50RowAt 49).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 49) (by decide) mmFiber50ReverseRow_49_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_50_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 50) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk25_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 50) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber50ReverseSingleStep50 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 10) (mmFiber50StateAt 50) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 10) (mmFiber50StateAt 50)
    (mmFiber50RowAt 50).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 50) (by decide) mmFiber50ReverseRow_50_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_51_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 51) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk25_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 50) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep51 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 11) (mmFiber50StateAt 51) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 11) (mmFiber50StateAt 51)
    (mmFiber50RowAt 51).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 51) (by decide) mmFiber50ReverseRow_51_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_52_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 52) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk26_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 52) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber50ReverseSingleStep52 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 12) (mmFiber50StateAt 52) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 12) (mmFiber50StateAt 52)
    (mmFiber50RowAt 52).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 52) (by decide) mmFiber50ReverseRow_52_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_53_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 53) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk26_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 52) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep53 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 13) (mmFiber50StateAt 53) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 13) (mmFiber50StateAt 53)
    (mmFiber50RowAt 53).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 53) (by decide) mmFiber50ReverseRow_53_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_54_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 54) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk27_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 54) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber50ReverseSingleStep54 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 14) (mmFiber50StateAt 54) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 14) (mmFiber50StateAt 54)
    (mmFiber50RowAt 54).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 54) (by decide) mmFiber50ReverseRow_54_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_55_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 55) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk27_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 54) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep55 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 15) (mmFiber50StateAt 55) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 15) (mmFiber50StateAt 55)
    (mmFiber50RowAt 55).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 55) (by decide) mmFiber50ReverseRow_55_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_56_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 56) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk28_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 56) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber50ReverseSingleStep56 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 0) (mmFiber50StateAt 56) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 0) (mmFiber50StateAt 56)
    (mmFiber50RowAt 56).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 56) (by decide) mmFiber50ReverseRow_56_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_57_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 57) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk28_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 56) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep57 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 1) (mmFiber50StateAt 57) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 1) (mmFiber50StateAt 57)
    (mmFiber50RowAt 57).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 57) (by decide) mmFiber50ReverseRow_57_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_58_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 58) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk29_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 58) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber50ReverseSingleStep58 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 2) (mmFiber50StateAt 58) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 2) (mmFiber50StateAt 58)
    (mmFiber50RowAt 58).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 58) (by decide) mmFiber50ReverseRow_58_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_59_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 59) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk29_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 58) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep59 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 3) (mmFiber50StateAt 59) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 3) (mmFiber50StateAt 59)
    (mmFiber50RowAt 59).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 59) (by decide) mmFiber50ReverseRow_59_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_60_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 60) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk30_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 60) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber50ReverseSingleStep60 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 4) (mmFiber50StateAt 60) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 4) (mmFiber50StateAt 60)
    (mmFiber50RowAt 60).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 60) (by decide) mmFiber50ReverseRow_60_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_61_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 61) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk30_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 60) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep61 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 5) (mmFiber50StateAt 61) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 5) (mmFiber50StateAt 61)
    (mmFiber50RowAt 61).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 61) (by decide) mmFiber50ReverseRow_61_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_62_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 62) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk31_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 62) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber50ReverseSingleStep62 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 6) (mmFiber50StateAt 62) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 6) (mmFiber50StateAt 62)
    (mmFiber50RowAt 62).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 62) (by decide) mmFiber50ReverseRow_62_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50ReverseRow_63_ok :
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 63) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber50Chunk31_ok
  change (mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 62) &&
    mmRowReverseValid mmFiber50Key mmFiber50Expected (mmFiber50RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber50ReverseSingleStep63 :
    chainSingleKempeStep mmWord (mmFiber50StateAt 7) (mmFiber50StateAt 63) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber50StateAt 7) (mmFiber50StateAt 63)
    (mmFiber50RowAt 63).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber50Key mmFiber50Expected
        (mmFiber50RowAt 63) (by decide) mmFiber50ReverseRow_63_ok
      simpa [mmFiber50StateAt, mmFiber50RowAt, mmFiber50Rows, listGetD, directRow] using h)

theorem mmFiber50State0_in_close :
    mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  change mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 64 [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 0 64 [mmFiber50StateAt 0] (mmFiber50StateAt 0) (by simp [closeChainFiber])

theorem mmFiber50State1_in_close :
    mmFiber50StateAt 1 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 1 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 1) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep1
  change mmFiber50StateAt 1 ∈ closeChainFiber mmWord mmFiber50DirectStates (1 + 63) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 1 63 [mmFiber50StateAt 0] (mmFiber50StateAt 1) h1

theorem mmFiber50State2_in_close :
    mmFiber50StateAt 2 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 2 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 2) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep2
  change mmFiber50StateAt 2 ∈ closeChainFiber mmWord mmFiber50DirectStates (1 + 63) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 1 63 [mmFiber50StateAt 0] (mmFiber50StateAt 2) h1

theorem mmFiber50State3_in_close :
    mmFiber50StateAt 3 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 1 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 1) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep1
  have h2 : mmFiber50StateAt 3 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 1) (mmFiber50StateAt 3) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep3
  change mmFiber50StateAt 3 ∈ closeChainFiber mmWord mmFiber50DirectStates (2 + 62) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 2 62 [mmFiber50StateAt 0] (mmFiber50StateAt 3) h2

theorem mmFiber50State4_in_close :
    mmFiber50StateAt 4 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 2 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 2) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep2
  have h2 : mmFiber50StateAt 4 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 2) (mmFiber50StateAt 4) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep4
  change mmFiber50StateAt 4 ∈ closeChainFiber mmWord mmFiber50DirectStates (2 + 62) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 2 62 [mmFiber50StateAt 0] (mmFiber50StateAt 4) h2

theorem mmFiber50State5_in_close :
    mmFiber50StateAt 5 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 7 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 7) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep7
  have h2 : mmFiber50StateAt 5 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 7) (mmFiber50StateAt 5) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep5
  change mmFiber50StateAt 5 ∈ closeChainFiber mmWord mmFiber50DirectStates (2 + 62) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 2 62 [mmFiber50StateAt 0] (mmFiber50StateAt 5) h2

theorem mmFiber50State6_in_close :
    mmFiber50StateAt 6 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 1 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 1) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep1
  have h2 : mmFiber50StateAt 6 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 1) (mmFiber50StateAt 6) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep6
  change mmFiber50StateAt 6 ∈ closeChainFiber mmWord mmFiber50DirectStates (2 + 62) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 2 62 [mmFiber50StateAt 0] (mmFiber50StateAt 6) h2

theorem mmFiber50State7_in_close :
    mmFiber50StateAt 7 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 7 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 7) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep7
  change mmFiber50StateAt 7 ∈ closeChainFiber mmWord mmFiber50DirectStates (1 + 63) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 1 63 [mmFiber50StateAt 0] (mmFiber50StateAt 7) h1

theorem mmFiber50State8_in_close :
    mmFiber50StateAt 8 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 8 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 8) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep8
  change mmFiber50StateAt 8 ∈ closeChainFiber mmWord mmFiber50DirectStates (1 + 63) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 1 63 [mmFiber50StateAt 0] (mmFiber50StateAt 8) h1

theorem mmFiber50State9_in_close :
    mmFiber50StateAt 9 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 1 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 1) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep1
  have h2 : mmFiber50StateAt 9 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 1) (mmFiber50StateAt 9) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep9
  change mmFiber50StateAt 9 ∈ closeChainFiber mmWord mmFiber50DirectStates (2 + 62) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 2 62 [mmFiber50StateAt 0] (mmFiber50StateAt 9) h2

theorem mmFiber50State10_in_close :
    mmFiber50StateAt 10 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 2 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 2) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep2
  have h2 : mmFiber50StateAt 10 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 2) (mmFiber50StateAt 10) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep10
  change mmFiber50StateAt 10 ∈ closeChainFiber mmWord mmFiber50DirectStates (2 + 62) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 2 62 [mmFiber50StateAt 0] (mmFiber50StateAt 10) h2

theorem mmFiber50State11_in_close :
    mmFiber50StateAt 11 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 1 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 1) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep1
  have h2 : mmFiber50StateAt 3 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 1) (mmFiber50StateAt 3) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep3
  have h3 : mmFiber50StateAt 11 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 3) (mmFiber50StateAt 11) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep11
  change mmFiber50StateAt 11 ∈ closeChainFiber mmWord mmFiber50DirectStates (3 + 61) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 3 61 [mmFiber50StateAt 0] (mmFiber50StateAt 11) h3

theorem mmFiber50State12_in_close :
    mmFiber50StateAt 12 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 2 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 2) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep2
  have h2 : mmFiber50StateAt 4 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 2) (mmFiber50StateAt 4) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep4
  have h3 : mmFiber50StateAt 12 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 4) (mmFiber50StateAt 12) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep12
  change mmFiber50StateAt 12 ∈ closeChainFiber mmWord mmFiber50DirectStates (3 + 61) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 3 61 [mmFiber50StateAt 0] (mmFiber50StateAt 12) h3

theorem mmFiber50State13_in_close :
    mmFiber50StateAt 13 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 7 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 7) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep7
  have h2 : mmFiber50StateAt 5 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 7) (mmFiber50StateAt 5) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep5
  have h3 : mmFiber50StateAt 13 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 5) (mmFiber50StateAt 13) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep13
  change mmFiber50StateAt 13 ∈ closeChainFiber mmWord mmFiber50DirectStates (3 + 61) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 3 61 [mmFiber50StateAt 0] (mmFiber50StateAt 13) h3

theorem mmFiber50State14_in_close :
    mmFiber50StateAt 14 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 1 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 1) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep1
  have h2 : mmFiber50StateAt 6 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 1) (mmFiber50StateAt 6) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep6
  have h3 : mmFiber50StateAt 14 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 6) (mmFiber50StateAt 14) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep14
  change mmFiber50StateAt 14 ∈ closeChainFiber mmWord mmFiber50DirectStates (3 + 61) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 3 61 [mmFiber50StateAt 0] (mmFiber50StateAt 14) h3

theorem mmFiber50State15_in_close :
    mmFiber50StateAt 15 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 7 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 7) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep7
  have h2 : mmFiber50StateAt 15 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 7) (mmFiber50StateAt 15) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep15
  change mmFiber50StateAt 15 ∈ closeChainFiber mmWord mmFiber50DirectStates (2 + 62) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 2 62 [mmFiber50StateAt 0] (mmFiber50StateAt 15) h2

theorem mmFiber50State16_in_close :
    mmFiber50StateAt 16 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 16 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 16) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep16
  change mmFiber50StateAt 16 ∈ closeChainFiber mmWord mmFiber50DirectStates (1 + 63) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 1 63 [mmFiber50StateAt 0] (mmFiber50StateAt 16) h1

theorem mmFiber50State17_in_close :
    mmFiber50StateAt 17 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 1 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 1) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep1
  have h2 : mmFiber50StateAt 17 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 1) (mmFiber50StateAt 17) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep17
  change mmFiber50StateAt 17 ∈ closeChainFiber mmWord mmFiber50DirectStates (2 + 62) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 2 62 [mmFiber50StateAt 0] (mmFiber50StateAt 17) h2

theorem mmFiber50State18_in_close :
    mmFiber50StateAt 18 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 2 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 2) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep2
  have h2 : mmFiber50StateAt 18 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 2) (mmFiber50StateAt 18) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep18
  change mmFiber50StateAt 18 ∈ closeChainFiber mmWord mmFiber50DirectStates (2 + 62) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 2 62 [mmFiber50StateAt 0] (mmFiber50StateAt 18) h2

theorem mmFiber50State19_in_close :
    mmFiber50StateAt 19 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 1 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 1) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep1
  have h2 : mmFiber50StateAt 3 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 1) (mmFiber50StateAt 3) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep3
  have h3 : mmFiber50StateAt 19 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 3) (mmFiber50StateAt 19) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep19
  change mmFiber50StateAt 19 ∈ closeChainFiber mmWord mmFiber50DirectStates (3 + 61) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 3 61 [mmFiber50StateAt 0] (mmFiber50StateAt 19) h3

theorem mmFiber50State20_in_close :
    mmFiber50StateAt 20 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 16 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 16) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep16
  have h2 : mmFiber50StateAt 20 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 16) (mmFiber50StateAt 20) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep20
  change mmFiber50StateAt 20 ∈ closeChainFiber mmWord mmFiber50DirectStates (2 + 62) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 2 62 [mmFiber50StateAt 0] (mmFiber50StateAt 20) h2

theorem mmFiber50State21_in_close :
    mmFiber50StateAt 21 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 1 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 1) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep1
  have h2 : mmFiber50StateAt 17 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 1) (mmFiber50StateAt 17) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep17
  have h3 : mmFiber50StateAt 21 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 17) (mmFiber50StateAt 21) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep21
  change mmFiber50StateAt 21 ∈ closeChainFiber mmWord mmFiber50DirectStates (3 + 61) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 3 61 [mmFiber50StateAt 0] (mmFiber50StateAt 21) h3

theorem mmFiber50State22_in_close :
    mmFiber50StateAt 22 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 1 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 1) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep1
  have h2 : mmFiber50StateAt 6 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 1) (mmFiber50StateAt 6) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep6
  have h3 : mmFiber50StateAt 22 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 6) (mmFiber50StateAt 22) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep22
  change mmFiber50StateAt 22 ∈ closeChainFiber mmWord mmFiber50DirectStates (3 + 61) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 3 61 [mmFiber50StateAt 0] (mmFiber50StateAt 22) h3

theorem mmFiber50State23_in_close :
    mmFiber50StateAt 23 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 7 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 7) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep7
  have h2 : mmFiber50StateAt 23 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 7) (mmFiber50StateAt 23) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep23
  change mmFiber50StateAt 23 ∈ closeChainFiber mmWord mmFiber50DirectStates (2 + 62) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 2 62 [mmFiber50StateAt 0] (mmFiber50StateAt 23) h2

theorem mmFiber50State24_in_close :
    mmFiber50StateAt 24 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 8 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 8) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep8
  have h2 : mmFiber50StateAt 24 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 8) (mmFiber50StateAt 24) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep24
  change mmFiber50StateAt 24 ∈ closeChainFiber mmWord mmFiber50DirectStates (2 + 62) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 2 62 [mmFiber50StateAt 0] (mmFiber50StateAt 24) h2

theorem mmFiber50State25_in_close :
    mmFiber50StateAt 25 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 1 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 1) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep1
  have h2 : mmFiber50StateAt 9 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 1) (mmFiber50StateAt 9) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep9
  have h3 : mmFiber50StateAt 25 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 9) (mmFiber50StateAt 25) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep25
  change mmFiber50StateAt 25 ∈ closeChainFiber mmWord mmFiber50DirectStates (3 + 61) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 3 61 [mmFiber50StateAt 0] (mmFiber50StateAt 25) h3

theorem mmFiber50State26_in_close :
    mmFiber50StateAt 26 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 2 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 2) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep2
  have h2 : mmFiber50StateAt 10 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 2) (mmFiber50StateAt 10) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep10
  have h3 : mmFiber50StateAt 26 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 10) (mmFiber50StateAt 26) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep26
  change mmFiber50StateAt 26 ∈ closeChainFiber mmWord mmFiber50DirectStates (3 + 61) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 3 61 [mmFiber50StateAt 0] (mmFiber50StateAt 26) h3

theorem mmFiber50State27_in_close :
    mmFiber50StateAt 27 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 1 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 1) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep1
  have h2 : mmFiber50StateAt 3 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 1) (mmFiber50StateAt 3) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep3
  have h3 : mmFiber50StateAt 11 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 3) (mmFiber50StateAt 11) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep11
  have h4 : mmFiber50StateAt 27 ∈ closeChainFiber mmWord mmFiber50DirectStates 4 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0]
      (mmFiber50StateAt 11) (mmFiber50StateAt 27) (by decide) h3 (by decide)
      mmFiber50ReverseSingleStep27
  change mmFiber50StateAt 27 ∈ closeChainFiber mmWord mmFiber50DirectStates (4 + 60) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 4 60 [mmFiber50StateAt 0] (mmFiber50StateAt 27) h4

theorem mmFiber50State28_in_close :
    mmFiber50StateAt 28 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 8 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 8) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep8
  have h2 : mmFiber50StateAt 24 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 8) (mmFiber50StateAt 24) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep24
  have h3 : mmFiber50StateAt 28 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 24) (mmFiber50StateAt 28) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep28
  change mmFiber50StateAt 28 ∈ closeChainFiber mmWord mmFiber50DirectStates (3 + 61) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 3 61 [mmFiber50StateAt 0] (mmFiber50StateAt 28) h3

theorem mmFiber50State29_in_close :
    mmFiber50StateAt 29 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 1 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 1) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep1
  have h2 : mmFiber50StateAt 9 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 1) (mmFiber50StateAt 9) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep9
  have h3 : mmFiber50StateAt 25 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 9) (mmFiber50StateAt 25) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep25
  have h4 : mmFiber50StateAt 29 ∈ closeChainFiber mmWord mmFiber50DirectStates 4 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0]
      (mmFiber50StateAt 25) (mmFiber50StateAt 29) (by decide) h3 (by decide)
      mmFiber50ReverseSingleStep29
  change mmFiber50StateAt 29 ∈ closeChainFiber mmWord mmFiber50DirectStates (4 + 60) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 4 60 [mmFiber50StateAt 0] (mmFiber50StateAt 29) h4

theorem mmFiber50State30_in_close :
    mmFiber50StateAt 30 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 1 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 1) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep1
  have h2 : mmFiber50StateAt 6 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 1) (mmFiber50StateAt 6) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep6
  have h3 : mmFiber50StateAt 14 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 6) (mmFiber50StateAt 14) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep14
  have h4 : mmFiber50StateAt 30 ∈ closeChainFiber mmWord mmFiber50DirectStates 4 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0]
      (mmFiber50StateAt 14) (mmFiber50StateAt 30) (by decide) h3 (by decide)
      mmFiber50ReverseSingleStep30
  change mmFiber50StateAt 30 ∈ closeChainFiber mmWord mmFiber50DirectStates (4 + 60) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 4 60 [mmFiber50StateAt 0] (mmFiber50StateAt 30) h4

theorem mmFiber50State31_in_close :
    mmFiber50StateAt 31 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 7 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 7) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep7
  have h2 : mmFiber50StateAt 15 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 7) (mmFiber50StateAt 15) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep15
  have h3 : mmFiber50StateAt 31 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 15) (mmFiber50StateAt 31) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep31
  change mmFiber50StateAt 31 ∈ closeChainFiber mmWord mmFiber50DirectStates (3 + 61) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 3 61 [mmFiber50StateAt 0] (mmFiber50StateAt 31) h3

theorem mmFiber50State32_in_close :
    mmFiber50StateAt 32 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 8 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 8) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep8
  have h2 : mmFiber50StateAt 48 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 8) (mmFiber50StateAt 48) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep48
  have h3 : mmFiber50StateAt 32 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 48) (mmFiber50StateAt 32) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep32
  change mmFiber50StateAt 32 ∈ closeChainFiber mmWord mmFiber50DirectStates (3 + 61) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 3 61 [mmFiber50StateAt 0] (mmFiber50StateAt 32) h3

theorem mmFiber50State33_in_close :
    mmFiber50StateAt 33 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 1 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 1) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep1
  have h2 : mmFiber50StateAt 9 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 1) (mmFiber50StateAt 9) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep9
  have h3 : mmFiber50StateAt 49 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 9) (mmFiber50StateAt 49) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep49
  have h4 : mmFiber50StateAt 33 ∈ closeChainFiber mmWord mmFiber50DirectStates 4 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0]
      (mmFiber50StateAt 49) (mmFiber50StateAt 33) (by decide) h3 (by decide)
      mmFiber50ReverseSingleStep33
  change mmFiber50StateAt 33 ∈ closeChainFiber mmWord mmFiber50DirectStates (4 + 60) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 4 60 [mmFiber50StateAt 0] (mmFiber50StateAt 33) h4

theorem mmFiber50State34_in_close :
    mmFiber50StateAt 34 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 1 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 1) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep1
  have h2 : mmFiber50StateAt 6 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 1) (mmFiber50StateAt 6) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep6
  have h3 : mmFiber50StateAt 22 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 6) (mmFiber50StateAt 22) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep22
  have h4 : mmFiber50StateAt 34 ∈ closeChainFiber mmWord mmFiber50DirectStates 4 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0]
      (mmFiber50StateAt 22) (mmFiber50StateAt 34) (by decide) h3 (by decide)
      mmFiber50ReverseSingleStep34
  change mmFiber50StateAt 34 ∈ closeChainFiber mmWord mmFiber50DirectStates (4 + 60) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 4 60 [mmFiber50StateAt 0] (mmFiber50StateAt 34) h4

theorem mmFiber50State35_in_close :
    mmFiber50StateAt 35 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 7 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 7) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep7
  have h2 : mmFiber50StateAt 23 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 7) (mmFiber50StateAt 23) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep23
  have h3 : mmFiber50StateAt 35 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 23) (mmFiber50StateAt 35) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep35
  change mmFiber50StateAt 35 ∈ closeChainFiber mmWord mmFiber50DirectStates (3 + 61) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 3 61 [mmFiber50StateAt 0] (mmFiber50StateAt 35) h3

theorem mmFiber50State36_in_close :
    mmFiber50StateAt 36 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 2 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 2) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep2
  have h2 : mmFiber50StateAt 18 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 2) (mmFiber50StateAt 18) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep18
  have h3 : mmFiber50StateAt 36 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 18) (mmFiber50StateAt 36) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep36
  change mmFiber50StateAt 36 ∈ closeChainFiber mmWord mmFiber50DirectStates (3 + 61) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 3 61 [mmFiber50StateAt 0] (mmFiber50StateAt 36) h3

theorem mmFiber50State37_in_close :
    mmFiber50StateAt 37 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 16 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 16) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep16
  have h2 : mmFiber50StateAt 39 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 16) (mmFiber50StateAt 39) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep39
  have h3 : mmFiber50StateAt 37 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 39) (mmFiber50StateAt 37) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep37
  change mmFiber50StateAt 37 ∈ closeChainFiber mmWord mmFiber50DirectStates (3 + 61) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 3 61 [mmFiber50StateAt 0] (mmFiber50StateAt 37) h3

theorem mmFiber50State38_in_close :
    mmFiber50StateAt 38 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 1 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 1) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep1
  have h2 : mmFiber50StateAt 17 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 1) (mmFiber50StateAt 17) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep17
  have h3 : mmFiber50StateAt 38 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 17) (mmFiber50StateAt 38) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep38
  change mmFiber50StateAt 38 ∈ closeChainFiber mmWord mmFiber50DirectStates (3 + 61) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 3 61 [mmFiber50StateAt 0] (mmFiber50StateAt 38) h3

theorem mmFiber50State39_in_close :
    mmFiber50StateAt 39 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 16 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 16) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep16
  have h2 : mmFiber50StateAt 39 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 16) (mmFiber50StateAt 39) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep39
  change mmFiber50StateAt 39 ∈ closeChainFiber mmWord mmFiber50DirectStates (2 + 62) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 2 62 [mmFiber50StateAt 0] (mmFiber50StateAt 39) h2

theorem mmFiber50State40_in_close :
    mmFiber50StateAt 40 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 56 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 56) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep56
  have h2 : mmFiber50StateAt 40 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 56) (mmFiber50StateAt 40) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep40
  change mmFiber50StateAt 40 ∈ closeChainFiber mmWord mmFiber50DirectStates (2 + 62) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 2 62 [mmFiber50StateAt 0] (mmFiber50StateAt 40) h2

theorem mmFiber50State41_in_close :
    mmFiber50StateAt 41 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 1 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 1) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep1
  have h2 : mmFiber50StateAt 57 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 1) (mmFiber50StateAt 57) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep57
  have h3 : mmFiber50StateAt 41 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 57) (mmFiber50StateAt 41) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep41
  change mmFiber50StateAt 41 ∈ closeChainFiber mmWord mmFiber50DirectStates (3 + 61) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 3 61 [mmFiber50StateAt 0] (mmFiber50StateAt 41) h3

theorem mmFiber50State42_in_close :
    mmFiber50StateAt 42 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 2 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 2) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep2
  have h2 : mmFiber50StateAt 58 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 2) (mmFiber50StateAt 58) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep58
  have h3 : mmFiber50StateAt 42 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 58) (mmFiber50StateAt 42) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep42
  change mmFiber50StateAt 42 ∈ closeChainFiber mmWord mmFiber50DirectStates (3 + 61) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 3 61 [mmFiber50StateAt 0] (mmFiber50StateAt 42) h3

theorem mmFiber50State43_in_close :
    mmFiber50StateAt 43 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 56 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 56) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep56
  have h2 : mmFiber50StateAt 40 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 56) (mmFiber50StateAt 40) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep40
  have h3 : mmFiber50StateAt 43 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 40) (mmFiber50StateAt 43) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep43
  change mmFiber50StateAt 43 ∈ closeChainFiber mmWord mmFiber50DirectStates (3 + 61) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 3 61 [mmFiber50StateAt 0] (mmFiber50StateAt 43) h3

theorem mmFiber50State44_in_close :
    mmFiber50StateAt 44 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 56 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 56) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep56
  have h2 : mmFiber50StateAt 40 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 56) (mmFiber50StateAt 40) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep40
  have h3 : mmFiber50StateAt 44 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 40) (mmFiber50StateAt 44) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep44
  change mmFiber50StateAt 44 ∈ closeChainFiber mmWord mmFiber50DirectStates (3 + 61) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 3 61 [mmFiber50StateAt 0] (mmFiber50StateAt 44) h3

theorem mmFiber50State45_in_close :
    mmFiber50StateAt 45 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 1 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 1) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep1
  have h2 : mmFiber50StateAt 57 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 1) (mmFiber50StateAt 57) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep57
  have h3 : mmFiber50StateAt 41 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 57) (mmFiber50StateAt 41) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep41
  have h4 : mmFiber50StateAt 45 ∈ closeChainFiber mmWord mmFiber50DirectStates 4 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0]
      (mmFiber50StateAt 41) (mmFiber50StateAt 45) (by decide) h3 (by decide)
      mmFiber50ReverseSingleStep45
  change mmFiber50StateAt 45 ∈ closeChainFiber mmWord mmFiber50DirectStates (4 + 60) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 4 60 [mmFiber50StateAt 0] (mmFiber50StateAt 45) h4

theorem mmFiber50State46_in_close :
    mmFiber50StateAt 46 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 1 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 1) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep1
  have h2 : mmFiber50StateAt 6 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 1) (mmFiber50StateAt 6) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep6
  have h3 : mmFiber50StateAt 62 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 6) (mmFiber50StateAt 62) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep62
  have h4 : mmFiber50StateAt 46 ∈ closeChainFiber mmWord mmFiber50DirectStates 4 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0]
      (mmFiber50StateAt 62) (mmFiber50StateAt 46) (by decide) h3 (by decide)
      mmFiber50ReverseSingleStep46
  change mmFiber50StateAt 46 ∈ closeChainFiber mmWord mmFiber50DirectStates (4 + 60) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 4 60 [mmFiber50StateAt 0] (mmFiber50StateAt 46) h4

theorem mmFiber50State47_in_close :
    mmFiber50StateAt 47 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 7 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 7) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep7
  have h2 : mmFiber50StateAt 63 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 7) (mmFiber50StateAt 63) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep63
  have h3 : mmFiber50StateAt 47 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 63) (mmFiber50StateAt 47) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep47
  change mmFiber50StateAt 47 ∈ closeChainFiber mmWord mmFiber50DirectStates (3 + 61) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 3 61 [mmFiber50StateAt 0] (mmFiber50StateAt 47) h3

theorem mmFiber50State48_in_close :
    mmFiber50StateAt 48 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 8 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 8) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep8
  have h2 : mmFiber50StateAt 48 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 8) (mmFiber50StateAt 48) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep48
  change mmFiber50StateAt 48 ∈ closeChainFiber mmWord mmFiber50DirectStates (2 + 62) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 2 62 [mmFiber50StateAt 0] (mmFiber50StateAt 48) h2

theorem mmFiber50State49_in_close :
    mmFiber50StateAt 49 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 1 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 1) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep1
  have h2 : mmFiber50StateAt 9 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 1) (mmFiber50StateAt 9) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep9
  have h3 : mmFiber50StateAt 49 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 9) (mmFiber50StateAt 49) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep49
  change mmFiber50StateAt 49 ∈ closeChainFiber mmWord mmFiber50DirectStates (3 + 61) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 3 61 [mmFiber50StateAt 0] (mmFiber50StateAt 49) h3

theorem mmFiber50State50_in_close :
    mmFiber50StateAt 50 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 2 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 2) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep2
  have h2 : mmFiber50StateAt 10 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 2) (mmFiber50StateAt 10) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep10
  have h3 : mmFiber50StateAt 50 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 10) (mmFiber50StateAt 50) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep50
  change mmFiber50StateAt 50 ∈ closeChainFiber mmWord mmFiber50DirectStates (3 + 61) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 3 61 [mmFiber50StateAt 0] (mmFiber50StateAt 50) h3

theorem mmFiber50State51_in_close :
    mmFiber50StateAt 51 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 1 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 1) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep1
  have h2 : mmFiber50StateAt 3 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 1) (mmFiber50StateAt 3) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep3
  have h3 : mmFiber50StateAt 11 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 3) (mmFiber50StateAt 11) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep11
  have h4 : mmFiber50StateAt 51 ∈ closeChainFiber mmWord mmFiber50DirectStates 4 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0]
      (mmFiber50StateAt 11) (mmFiber50StateAt 51) (by decide) h3 (by decide)
      mmFiber50ReverseSingleStep51
  change mmFiber50StateAt 51 ∈ closeChainFiber mmWord mmFiber50DirectStates (4 + 60) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 4 60 [mmFiber50StateAt 0] (mmFiber50StateAt 51) h4

theorem mmFiber50State52_in_close :
    mmFiber50StateAt 52 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 2 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 2) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep2
  have h2 : mmFiber50StateAt 4 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 2) (mmFiber50StateAt 4) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep4
  have h3 : mmFiber50StateAt 12 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 4) (mmFiber50StateAt 12) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep12
  have h4 : mmFiber50StateAt 52 ∈ closeChainFiber mmWord mmFiber50DirectStates 4 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0]
      (mmFiber50StateAt 12) (mmFiber50StateAt 52) (by decide) h3 (by decide)
      mmFiber50ReverseSingleStep52
  change mmFiber50StateAt 52 ∈ closeChainFiber mmWord mmFiber50DirectStates (4 + 60) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 4 60 [mmFiber50StateAt 0] (mmFiber50StateAt 52) h4

theorem mmFiber50State53_in_close :
    mmFiber50StateAt 53 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 7 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 7) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep7
  have h2 : mmFiber50StateAt 5 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 7) (mmFiber50StateAt 5) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep5
  have h3 : mmFiber50StateAt 13 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 5) (mmFiber50StateAt 13) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep13
  have h4 : mmFiber50StateAt 53 ∈ closeChainFiber mmWord mmFiber50DirectStates 4 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0]
      (mmFiber50StateAt 13) (mmFiber50StateAt 53) (by decide) h3 (by decide)
      mmFiber50ReverseSingleStep53
  change mmFiber50StateAt 53 ∈ closeChainFiber mmWord mmFiber50DirectStates (4 + 60) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 4 60 [mmFiber50StateAt 0] (mmFiber50StateAt 53) h4

theorem mmFiber50State54_in_close :
    mmFiber50StateAt 54 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 1 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 1) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep1
  have h2 : mmFiber50StateAt 6 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 1) (mmFiber50StateAt 6) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep6
  have h3 : mmFiber50StateAt 14 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 6) (mmFiber50StateAt 14) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep14
  have h4 : mmFiber50StateAt 54 ∈ closeChainFiber mmWord mmFiber50DirectStates 4 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0]
      (mmFiber50StateAt 14) (mmFiber50StateAt 54) (by decide) h3 (by decide)
      mmFiber50ReverseSingleStep54
  change mmFiber50StateAt 54 ∈ closeChainFiber mmWord mmFiber50DirectStates (4 + 60) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 4 60 [mmFiber50StateAt 0] (mmFiber50StateAt 54) h4

theorem mmFiber50State55_in_close :
    mmFiber50StateAt 55 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 7 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 7) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep7
  have h2 : mmFiber50StateAt 15 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 7) (mmFiber50StateAt 15) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep15
  have h3 : mmFiber50StateAt 55 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 15) (mmFiber50StateAt 55) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep55
  change mmFiber50StateAt 55 ∈ closeChainFiber mmWord mmFiber50DirectStates (3 + 61) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 3 61 [mmFiber50StateAt 0] (mmFiber50StateAt 55) h3

theorem mmFiber50State56_in_close :
    mmFiber50StateAt 56 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 56 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 56) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep56
  change mmFiber50StateAt 56 ∈ closeChainFiber mmWord mmFiber50DirectStates (1 + 63) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 1 63 [mmFiber50StateAt 0] (mmFiber50StateAt 56) h1

theorem mmFiber50State57_in_close :
    mmFiber50StateAt 57 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 1 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 1) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep1
  have h2 : mmFiber50StateAt 57 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 1) (mmFiber50StateAt 57) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep57
  change mmFiber50StateAt 57 ∈ closeChainFiber mmWord mmFiber50DirectStates (2 + 62) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 2 62 [mmFiber50StateAt 0] (mmFiber50StateAt 57) h2

theorem mmFiber50State58_in_close :
    mmFiber50StateAt 58 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 2 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 2) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep2
  have h2 : mmFiber50StateAt 58 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 2) (mmFiber50StateAt 58) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep58
  change mmFiber50StateAt 58 ∈ closeChainFiber mmWord mmFiber50DirectStates (2 + 62) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 2 62 [mmFiber50StateAt 0] (mmFiber50StateAt 58) h2

theorem mmFiber50State59_in_close :
    mmFiber50StateAt 59 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 1 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 1) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep1
  have h2 : mmFiber50StateAt 3 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 1) (mmFiber50StateAt 3) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep3
  have h3 : mmFiber50StateAt 59 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 3) (mmFiber50StateAt 59) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep59
  change mmFiber50StateAt 59 ∈ closeChainFiber mmWord mmFiber50DirectStates (3 + 61) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 3 61 [mmFiber50StateAt 0] (mmFiber50StateAt 59) h3

theorem mmFiber50State60_in_close :
    mmFiber50StateAt 60 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 2 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 2) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep2
  have h2 : mmFiber50StateAt 4 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 2) (mmFiber50StateAt 4) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep4
  have h3 : mmFiber50StateAt 60 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 4) (mmFiber50StateAt 60) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep60
  change mmFiber50StateAt 60 ∈ closeChainFiber mmWord mmFiber50DirectStates (3 + 61) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 3 61 [mmFiber50StateAt 0] (mmFiber50StateAt 60) h3

theorem mmFiber50State61_in_close :
    mmFiber50StateAt 61 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 7 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 7) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep7
  have h2 : mmFiber50StateAt 5 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 7) (mmFiber50StateAt 5) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep5
  have h3 : mmFiber50StateAt 61 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 5) (mmFiber50StateAt 61) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep61
  change mmFiber50StateAt 61 ∈ closeChainFiber mmWord mmFiber50DirectStates (3 + 61) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 3 61 [mmFiber50StateAt 0] (mmFiber50StateAt 61) h3

theorem mmFiber50State62_in_close :
    mmFiber50StateAt 62 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 1 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 1) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep1
  have h2 : mmFiber50StateAt 6 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 1) (mmFiber50StateAt 6) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep6
  have h3 : mmFiber50StateAt 62 ∈ closeChainFiber mmWord mmFiber50DirectStates 3 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0]
      (mmFiber50StateAt 6) (mmFiber50StateAt 62) (by decide) h2 (by decide)
      mmFiber50ReverseSingleStep62
  change mmFiber50StateAt 62 ∈ closeChainFiber mmWord mmFiber50DirectStates (3 + 61) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 3 61 [mmFiber50StateAt 0] (mmFiber50StateAt 62) h3

theorem mmFiber50State63_in_close :
    mmFiber50StateAt 63 ∈ closeChainFiber mmWord mmFiber50DirectStates mmFiber50DirectStates.length [mmFiber50StateAt 0] := by
  have h0 : mmFiber50StateAt 0 ∈ closeChainFiber mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber50StateAt 7 ∈ closeChainFiber mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 0 [mmFiber50StateAt 0]
      (mmFiber50StateAt 0) (mmFiber50StateAt 7) (by decide) h0 (by decide)
      mmFiber50ReverseSingleStep7
  have h2 : mmFiber50StateAt 63 ∈ closeChainFiber mmWord mmFiber50DirectStates 2 [mmFiber50StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber50DirectStates 1 [mmFiber50StateAt 0]
      (mmFiber50StateAt 7) (mmFiber50StateAt 63) (by decide) h1 (by decide)
      mmFiber50ReverseSingleStep63
  change mmFiber50StateAt 63 ∈ closeChainFiber mmWord mmFiber50DirectStates (2 + 62) [mmFiber50StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber50DirectStates 2 62 [mmFiber50StateAt 0] (mmFiber50StateAt 63) h2

theorem mmFiber50DirectConnected :
    chainFiberConnected mmWord mmFiber50DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber50DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber50State0_in_close
  · subst state
    exact mmFiber50State1_in_close
  · subst state
    exact mmFiber50State2_in_close
  · subst state
    exact mmFiber50State3_in_close
  · subst state
    exact mmFiber50State4_in_close
  · subst state
    exact mmFiber50State5_in_close
  · subst state
    exact mmFiber50State6_in_close
  · subst state
    exact mmFiber50State7_in_close
  · subst state
    exact mmFiber50State8_in_close
  · subst state
    exact mmFiber50State9_in_close
  · subst state
    exact mmFiber50State10_in_close
  · subst state
    exact mmFiber50State11_in_close
  · subst state
    exact mmFiber50State12_in_close
  · subst state
    exact mmFiber50State13_in_close
  · subst state
    exact mmFiber50State14_in_close
  · subst state
    exact mmFiber50State15_in_close
  · subst state
    exact mmFiber50State16_in_close
  · subst state
    exact mmFiber50State17_in_close
  · subst state
    exact mmFiber50State18_in_close
  · subst state
    exact mmFiber50State19_in_close
  · subst state
    exact mmFiber50State20_in_close
  · subst state
    exact mmFiber50State21_in_close
  · subst state
    exact mmFiber50State22_in_close
  · subst state
    exact mmFiber50State23_in_close
  · subst state
    exact mmFiber50State24_in_close
  · subst state
    exact mmFiber50State25_in_close
  · subst state
    exact mmFiber50State26_in_close
  · subst state
    exact mmFiber50State27_in_close
  · subst state
    exact mmFiber50State28_in_close
  · subst state
    exact mmFiber50State29_in_close
  · subst state
    exact mmFiber50State30_in_close
  · subst state
    exact mmFiber50State31_in_close
  · subst state
    exact mmFiber50State32_in_close
  · subst state
    exact mmFiber50State33_in_close
  · subst state
    exact mmFiber50State34_in_close
  · subst state
    exact mmFiber50State35_in_close
  · subst state
    exact mmFiber50State36_in_close
  · subst state
    exact mmFiber50State37_in_close
  · subst state
    exact mmFiber50State38_in_close
  · subst state
    exact mmFiber50State39_in_close
  · subst state
    exact mmFiber50State40_in_close
  · subst state
    exact mmFiber50State41_in_close
  · subst state
    exact mmFiber50State42_in_close
  · subst state
    exact mmFiber50State43_in_close
  · subst state
    exact mmFiber50State44_in_close
  · subst state
    exact mmFiber50State45_in_close
  · subst state
    exact mmFiber50State46_in_close
  · subst state
    exact mmFiber50State47_in_close
  · subst state
    exact mmFiber50State48_in_close
  · subst state
    exact mmFiber50State49_in_close
  · subst state
    exact mmFiber50State50_in_close
  · subst state
    exact mmFiber50State51_in_close
  · subst state
    exact mmFiber50State52_in_close
  · subst state
    exact mmFiber50State53_in_close
  · subst state
    exact mmFiber50State54_in_close
  · subst state
    exact mmFiber50State55_in_close
  · subst state
    exact mmFiber50State56_in_close
  · subst state
    exact mmFiber50State57_in_close
  · subst state
    exact mmFiber50State58_in_close
  · subst state
    exact mmFiber50State59_in_close
  · subst state
    exact mmFiber50State60_in_close
  · subst state
    exact mmFiber50State61_in_close
  · subst state
    exact mmFiber50State62_in_close
  · subst state
    exact mmFiber50State63_in_close
  · cases h
end GoertzelLemma818LengthTwoMMBridge

end Mettapedia.GraphTheory.FourColor
