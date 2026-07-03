import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for `mirror,mirror` size-64 fiber 10

This module proves direct connectedness for one generated size-64 fiber from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMMBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorMirrorCertificate
open GoertzelLemma818MirrorMirrorReverseAudit

def mmFiber10StateAt (i : Nat) : List TauState :=
  directStates (mmFiber10RowAt i).sourceLeft (mmFiber10RowAt i).sourceRight

def mmFiber10DirectStates : List (List TauState) :=
  [mmFiber10StateAt 0, mmFiber10StateAt 1, mmFiber10StateAt 2, mmFiber10StateAt 3, mmFiber10StateAt 4, mmFiber10StateAt 5, mmFiber10StateAt 6, mmFiber10StateAt 7, mmFiber10StateAt 8, mmFiber10StateAt 9, mmFiber10StateAt 10, mmFiber10StateAt 11, mmFiber10StateAt 12, mmFiber10StateAt 13, mmFiber10StateAt 14, mmFiber10StateAt 15, mmFiber10StateAt 16, mmFiber10StateAt 17, mmFiber10StateAt 18, mmFiber10StateAt 19, mmFiber10StateAt 20, mmFiber10StateAt 21, mmFiber10StateAt 22, mmFiber10StateAt 23, mmFiber10StateAt 24, mmFiber10StateAt 25, mmFiber10StateAt 26, mmFiber10StateAt 27, mmFiber10StateAt 28, mmFiber10StateAt 29, mmFiber10StateAt 30, mmFiber10StateAt 31, mmFiber10StateAt 32, mmFiber10StateAt 33, mmFiber10StateAt 34, mmFiber10StateAt 35, mmFiber10StateAt 36, mmFiber10StateAt 37, mmFiber10StateAt 38, mmFiber10StateAt 39, mmFiber10StateAt 40, mmFiber10StateAt 41, mmFiber10StateAt 42, mmFiber10StateAt 43, mmFiber10StateAt 44, mmFiber10StateAt 45, mmFiber10StateAt 46, mmFiber10StateAt 47, mmFiber10StateAt 48, mmFiber10StateAt 49, mmFiber10StateAt 50, mmFiber10StateAt 51, mmFiber10StateAt 52, mmFiber10StateAt 53, mmFiber10StateAt 54, mmFiber10StateAt 55, mmFiber10StateAt 56, mmFiber10StateAt 57, mmFiber10StateAt 58, mmFiber10StateAt 59, mmFiber10StateAt 60, mmFiber10StateAt 61, mmFiber10StateAt 62, mmFiber10StateAt 63]

theorem mmFiber10ReverseRow_1_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk0_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 0) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 0) (mmFiber10StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 0) (mmFiber10StateAt 1)
    (mmFiber10RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 1) (by decide) mmFiber10ReverseRow_1_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_2_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk1_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 2) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber10ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 0) (mmFiber10StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 0) (mmFiber10StateAt 2)
    (mmFiber10RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 2) (by decide) mmFiber10ReverseRow_2_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_3_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk1_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 2) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 1) (mmFiber10StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 1) (mmFiber10StateAt 3)
    (mmFiber10RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 3) (by decide) mmFiber10ReverseRow_3_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_4_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk2_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 4) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber10ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 2) (mmFiber10StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 2) (mmFiber10StateAt 4)
    (mmFiber10RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 4) (by decide) mmFiber10ReverseRow_4_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_5_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk2_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 4) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 7) (mmFiber10StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 7) (mmFiber10StateAt 5)
    (mmFiber10RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 5) (by decide) mmFiber10ReverseRow_5_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_6_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk3_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 6) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber10ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 1) (mmFiber10StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 1) (mmFiber10StateAt 6)
    (mmFiber10RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 6) (by decide) mmFiber10ReverseRow_6_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_7_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk3_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 6) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 0) (mmFiber10StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 0) (mmFiber10StateAt 7)
    (mmFiber10RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 7) (by decide) mmFiber10ReverseRow_7_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_8_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 8) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk4_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 8) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber10ReverseSingleStep8 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 0) (mmFiber10StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 0) (mmFiber10StateAt 8)
    (mmFiber10RowAt 8).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 8) (by decide) mmFiber10ReverseRow_8_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_9_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 9) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk4_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 8) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep9 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 1) (mmFiber10StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 1) (mmFiber10StateAt 9)
    (mmFiber10RowAt 9).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 9) (by decide) mmFiber10ReverseRow_9_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_10_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 10) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk5_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 10) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber10ReverseSingleStep10 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 2) (mmFiber10StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 2) (mmFiber10StateAt 10)
    (mmFiber10RowAt 10).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 10) (by decide) mmFiber10ReverseRow_10_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_11_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 11) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk5_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 10) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep11 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 3) (mmFiber10StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 3) (mmFiber10StateAt 11)
    (mmFiber10RowAt 11).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 11) (by decide) mmFiber10ReverseRow_11_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_12_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 12) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk6_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 12) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber10ReverseSingleStep12 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 4) (mmFiber10StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 4) (mmFiber10StateAt 12)
    (mmFiber10RowAt 12).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 12) (by decide) mmFiber10ReverseRow_12_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_13_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 13) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk6_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 12) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep13 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 5) (mmFiber10StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 5) (mmFiber10StateAt 13)
    (mmFiber10RowAt 13).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 13) (by decide) mmFiber10ReverseRow_13_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_14_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 14) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk7_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 14) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber10ReverseSingleStep14 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 6) (mmFiber10StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 6) (mmFiber10StateAt 14)
    (mmFiber10RowAt 14).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 14) (by decide) mmFiber10ReverseRow_14_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_15_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 15) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk7_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 14) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep15 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 7) (mmFiber10StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 7) (mmFiber10StateAt 15)
    (mmFiber10RowAt 15).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 15) (by decide) mmFiber10ReverseRow_15_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_16_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 16) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk8_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 16) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber10ReverseSingleStep16 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 0) (mmFiber10StateAt 16) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 0) (mmFiber10StateAt 16)
    (mmFiber10RowAt 16).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 16) (by decide) mmFiber10ReverseRow_16_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_17_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 17) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk8_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 16) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep17 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 1) (mmFiber10StateAt 17) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 1) (mmFiber10StateAt 17)
    (mmFiber10RowAt 17).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 17) (by decide) mmFiber10ReverseRow_17_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_18_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 18) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk9_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 18) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber10ReverseSingleStep18 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 2) (mmFiber10StateAt 18) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 2) (mmFiber10StateAt 18)
    (mmFiber10RowAt 18).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 18) (by decide) mmFiber10ReverseRow_18_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_19_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 19) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk9_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 18) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep19 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 3) (mmFiber10StateAt 19) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 3) (mmFiber10StateAt 19)
    (mmFiber10RowAt 19).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 19) (by decide) mmFiber10ReverseRow_19_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_20_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 20) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk10_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 20) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber10ReverseSingleStep20 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 16) (mmFiber10StateAt 20) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 16) (mmFiber10StateAt 20)
    (mmFiber10RowAt 20).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 20) (by decide) mmFiber10ReverseRow_20_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_21_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 21) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk10_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 20) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep21 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 17) (mmFiber10StateAt 21) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 17) (mmFiber10StateAt 21)
    (mmFiber10RowAt 21).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 21) (by decide) mmFiber10ReverseRow_21_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_22_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 22) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk11_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 22) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber10ReverseSingleStep22 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 6) (mmFiber10StateAt 22) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 6) (mmFiber10StateAt 22)
    (mmFiber10RowAt 22).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 22) (by decide) mmFiber10ReverseRow_22_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_23_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 23) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk11_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 22) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep23 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 7) (mmFiber10StateAt 23) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 7) (mmFiber10StateAt 23)
    (mmFiber10RowAt 23).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 23) (by decide) mmFiber10ReverseRow_23_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_24_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 24) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk12_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 24) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber10ReverseSingleStep24 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 8) (mmFiber10StateAt 24) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 8) (mmFiber10StateAt 24)
    (mmFiber10RowAt 24).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 24) (by decide) mmFiber10ReverseRow_24_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_25_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 25) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk12_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 24) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep25 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 9) (mmFiber10StateAt 25) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 9) (mmFiber10StateAt 25)
    (mmFiber10RowAt 25).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 25) (by decide) mmFiber10ReverseRow_25_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_26_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 26) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk13_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 26) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber10ReverseSingleStep26 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 10) (mmFiber10StateAt 26) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 10) (mmFiber10StateAt 26)
    (mmFiber10RowAt 26).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 26) (by decide) mmFiber10ReverseRow_26_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_27_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 27) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk13_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 26) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep27 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 11) (mmFiber10StateAt 27) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 11) (mmFiber10StateAt 27)
    (mmFiber10RowAt 27).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 27) (by decide) mmFiber10ReverseRow_27_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_28_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 28) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk14_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 28) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber10ReverseSingleStep28 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 24) (mmFiber10StateAt 28) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 24) (mmFiber10StateAt 28)
    (mmFiber10RowAt 28).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 28) (by decide) mmFiber10ReverseRow_28_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_29_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 29) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk14_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 28) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep29 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 25) (mmFiber10StateAt 29) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 25) (mmFiber10StateAt 29)
    (mmFiber10RowAt 29).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 29) (by decide) mmFiber10ReverseRow_29_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_30_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 30) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk15_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 30) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber10ReverseSingleStep30 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 14) (mmFiber10StateAt 30) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 14) (mmFiber10StateAt 30)
    (mmFiber10RowAt 30).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 30) (by decide) mmFiber10ReverseRow_30_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_31_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 31) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk15_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 30) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep31 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 15) (mmFiber10StateAt 31) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 15) (mmFiber10StateAt 31)
    (mmFiber10RowAt 31).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 31) (by decide) mmFiber10ReverseRow_31_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_32_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 32) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk16_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 32) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber10ReverseSingleStep32 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 0) (mmFiber10StateAt 32) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 0) (mmFiber10StateAt 32)
    (mmFiber10RowAt 32).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 32) (by decide) mmFiber10ReverseRow_32_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_33_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 33) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk16_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 32) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep33 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 1) (mmFiber10StateAt 33) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 1) (mmFiber10StateAt 33)
    (mmFiber10RowAt 33).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 33) (by decide) mmFiber10ReverseRow_33_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_34_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 34) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk17_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 34) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber10ReverseSingleStep34 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 2) (mmFiber10StateAt 34) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 2) (mmFiber10StateAt 34)
    (mmFiber10RowAt 34).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 34) (by decide) mmFiber10ReverseRow_34_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_35_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 35) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk17_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 34) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep35 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 32) (mmFiber10StateAt 35) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 32) (mmFiber10StateAt 35)
    (mmFiber10RowAt 35).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 35) (by decide) mmFiber10ReverseRow_35_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_36_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 36) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk18_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 36) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber10ReverseSingleStep36 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 32) (mmFiber10StateAt 36) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 32) (mmFiber10StateAt 36)
    (mmFiber10RowAt 36).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 36) (by decide) mmFiber10ReverseRow_36_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_37_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 37) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk18_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 36) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep37 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 33) (mmFiber10StateAt 37) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 33) (mmFiber10StateAt 37)
    (mmFiber10RowAt 37).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 37) (by decide) mmFiber10ReverseRow_37_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_38_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 38) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk19_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 38) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber10ReverseSingleStep38 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 6) (mmFiber10StateAt 38) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 6) (mmFiber10StateAt 38)
    (mmFiber10RowAt 38).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 38) (by decide) mmFiber10ReverseRow_38_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_39_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 39) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk19_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 38) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep39 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 7) (mmFiber10StateAt 39) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 7) (mmFiber10StateAt 39)
    (mmFiber10RowAt 39).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 39) (by decide) mmFiber10ReverseRow_39_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_40_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 40) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk20_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 40) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber10ReverseSingleStep40 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 8) (mmFiber10StateAt 40) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 8) (mmFiber10StateAt 40)
    (mmFiber10RowAt 40).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 40) (by decide) mmFiber10ReverseRow_40_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_41_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 41) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk20_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 40) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep41 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 9) (mmFiber10StateAt 41) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 9) (mmFiber10StateAt 41)
    (mmFiber10RowAt 41).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 41) (by decide) mmFiber10ReverseRow_41_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_42_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 42) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk21_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 42) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber10ReverseSingleStep42 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 10) (mmFiber10StateAt 42) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 10) (mmFiber10StateAt 42)
    (mmFiber10RowAt 42).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 42) (by decide) mmFiber10ReverseRow_42_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_43_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 43) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk21_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 42) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep43 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 40) (mmFiber10StateAt 43) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 40) (mmFiber10StateAt 43)
    (mmFiber10RowAt 43).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 43) (by decide) mmFiber10ReverseRow_43_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_44_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 44) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk22_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 44) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber10ReverseSingleStep44 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 40) (mmFiber10StateAt 44) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 40) (mmFiber10StateAt 44)
    (mmFiber10RowAt 44).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 44) (by decide) mmFiber10ReverseRow_44_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_45_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 45) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk22_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 44) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep45 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 41) (mmFiber10StateAt 45) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 41) (mmFiber10StateAt 45)
    (mmFiber10RowAt 45).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 45) (by decide) mmFiber10ReverseRow_45_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_46_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 46) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk23_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 46) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber10ReverseSingleStep46 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 14) (mmFiber10StateAt 46) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 14) (mmFiber10StateAt 46)
    (mmFiber10RowAt 46).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 46) (by decide) mmFiber10ReverseRow_46_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_47_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 47) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk23_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 46) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep47 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 15) (mmFiber10StateAt 47) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 15) (mmFiber10StateAt 47)
    (mmFiber10RowAt 47).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 47) (by decide) mmFiber10ReverseRow_47_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_48_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 48) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk24_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 48) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber10ReverseSingleStep48 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 16) (mmFiber10StateAt 48) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 16) (mmFiber10StateAt 48)
    (mmFiber10RowAt 48).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 48) (by decide) mmFiber10ReverseRow_48_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_49_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 49) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk24_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 48) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep49 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 17) (mmFiber10StateAt 49) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 17) (mmFiber10StateAt 49)
    (mmFiber10RowAt 49).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 49) (by decide) mmFiber10ReverseRow_49_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_50_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 50) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk25_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 50) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber10ReverseSingleStep50 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 18) (mmFiber10StateAt 50) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 18) (mmFiber10StateAt 50)
    (mmFiber10RowAt 50).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 50) (by decide) mmFiber10ReverseRow_50_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_51_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 51) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk25_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 50) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep51 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 19) (mmFiber10StateAt 51) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 19) (mmFiber10StateAt 51)
    (mmFiber10RowAt 51).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 51) (by decide) mmFiber10ReverseRow_51_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_52_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 52) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk26_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 52) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber10ReverseSingleStep52 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 40) (mmFiber10StateAt 52) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 40) (mmFiber10StateAt 52)
    (mmFiber10RowAt 52).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 52) (by decide) mmFiber10ReverseRow_52_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_53_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 53) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk26_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 52) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep53 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 41) (mmFiber10StateAt 53) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 41) (mmFiber10StateAt 53)
    (mmFiber10RowAt 53).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 53) (by decide) mmFiber10ReverseRow_53_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_54_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 54) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk27_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 54) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber10ReverseSingleStep54 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 22) (mmFiber10StateAt 54) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 22) (mmFiber10StateAt 54)
    (mmFiber10RowAt 54).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 54) (by decide) mmFiber10ReverseRow_54_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_55_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 55) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk27_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 54) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep55 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 23) (mmFiber10StateAt 55) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 23) (mmFiber10StateAt 55)
    (mmFiber10RowAt 55).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 55) (by decide) mmFiber10ReverseRow_55_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_56_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 56) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk28_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 56) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber10ReverseSingleStep56 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 39) (mmFiber10StateAt 56) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 39) (mmFiber10StateAt 56)
    (mmFiber10RowAt 56).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 56) (by decide) mmFiber10ReverseRow_56_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_57_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 57) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk28_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 56) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep57 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 38) (mmFiber10StateAt 57) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 38) (mmFiber10StateAt 57)
    (mmFiber10RowAt 57).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 57) (by decide) mmFiber10ReverseRow_57_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_58_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 58) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk29_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 58) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber10ReverseSingleStep58 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 36) (mmFiber10StateAt 58) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 36) (mmFiber10StateAt 58)
    (mmFiber10RowAt 58).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 58) (by decide) mmFiber10ReverseRow_58_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_59_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 59) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk29_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 58) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep59 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 37) (mmFiber10StateAt 59) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 37) (mmFiber10StateAt 59)
    (mmFiber10RowAt 59).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 59) (by decide) mmFiber10ReverseRow_59_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_60_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 60) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk30_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 60) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber10ReverseSingleStep60 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 32) (mmFiber10StateAt 60) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 32) (mmFiber10StateAt 60)
    (mmFiber10RowAt 60).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 60) (by decide) mmFiber10ReverseRow_60_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_61_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 61) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk30_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 60) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep61 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 33) (mmFiber10StateAt 61) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 33) (mmFiber10StateAt 61)
    (mmFiber10RowAt 61).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 61) (by decide) mmFiber10ReverseRow_61_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_62_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 62) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk31_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 62) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber10ReverseSingleStep62 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 34) (mmFiber10StateAt 62) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 34) (mmFiber10StateAt 62)
    (mmFiber10RowAt 62).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 62) (by decide) mmFiber10ReverseRow_62_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10ReverseRow_63_ok :
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 63) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber10Chunk31_ok
  change (mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 62) &&
    mmRowReverseValid mmFiber10Key mmFiber10Expected (mmFiber10RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber10ReverseSingleStep63 :
    chainSingleKempeStep mmWord (mmFiber10StateAt 35) (mmFiber10StateAt 63) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber10StateAt 35) (mmFiber10StateAt 63)
    (mmFiber10RowAt 63).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber10Key mmFiber10Expected
        (mmFiber10RowAt 63) (by decide) mmFiber10ReverseRow_63_ok
      simpa [mmFiber10StateAt, mmFiber10RowAt, mmFiber10Rows, listGetD, directRow] using h)

theorem mmFiber10State0_in_close :
    mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  change mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 64 [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 0 64 [mmFiber10StateAt 0] (mmFiber10StateAt 0) (by simp [closeChainFiber])

theorem mmFiber10State1_in_close :
    mmFiber10StateAt 1 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 1 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 1) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep1
  change mmFiber10StateAt 1 ∈ closeChainFiber mmWord mmFiber10DirectStates (1 + 63) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 1 63 [mmFiber10StateAt 0] (mmFiber10StateAt 1) h1

theorem mmFiber10State2_in_close :
    mmFiber10StateAt 2 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 2 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 2) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep2
  change mmFiber10StateAt 2 ∈ closeChainFiber mmWord mmFiber10DirectStates (1 + 63) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 1 63 [mmFiber10StateAt 0] (mmFiber10StateAt 2) h1

theorem mmFiber10State3_in_close :
    mmFiber10StateAt 3 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 1 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 1) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep1
  have h2 : mmFiber10StateAt 3 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 1) (mmFiber10StateAt 3) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep3
  change mmFiber10StateAt 3 ∈ closeChainFiber mmWord mmFiber10DirectStates (2 + 62) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 2 62 [mmFiber10StateAt 0] (mmFiber10StateAt 3) h2

theorem mmFiber10State4_in_close :
    mmFiber10StateAt 4 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 2 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 2) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep2
  have h2 : mmFiber10StateAt 4 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 2) (mmFiber10StateAt 4) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep4
  change mmFiber10StateAt 4 ∈ closeChainFiber mmWord mmFiber10DirectStates (2 + 62) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 2 62 [mmFiber10StateAt 0] (mmFiber10StateAt 4) h2

theorem mmFiber10State5_in_close :
    mmFiber10StateAt 5 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 7 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 7) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep7
  have h2 : mmFiber10StateAt 5 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 7) (mmFiber10StateAt 5) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep5
  change mmFiber10StateAt 5 ∈ closeChainFiber mmWord mmFiber10DirectStates (2 + 62) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 2 62 [mmFiber10StateAt 0] (mmFiber10StateAt 5) h2

theorem mmFiber10State6_in_close :
    mmFiber10StateAt 6 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 1 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 1) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep1
  have h2 : mmFiber10StateAt 6 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 1) (mmFiber10StateAt 6) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep6
  change mmFiber10StateAt 6 ∈ closeChainFiber mmWord mmFiber10DirectStates (2 + 62) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 2 62 [mmFiber10StateAt 0] (mmFiber10StateAt 6) h2

theorem mmFiber10State7_in_close :
    mmFiber10StateAt 7 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 7 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 7) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep7
  change mmFiber10StateAt 7 ∈ closeChainFiber mmWord mmFiber10DirectStates (1 + 63) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 1 63 [mmFiber10StateAt 0] (mmFiber10StateAt 7) h1

theorem mmFiber10State8_in_close :
    mmFiber10StateAt 8 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 8 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 8) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep8
  change mmFiber10StateAt 8 ∈ closeChainFiber mmWord mmFiber10DirectStates (1 + 63) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 1 63 [mmFiber10StateAt 0] (mmFiber10StateAt 8) h1

theorem mmFiber10State9_in_close :
    mmFiber10StateAt 9 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 1 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 1) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep1
  have h2 : mmFiber10StateAt 9 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 1) (mmFiber10StateAt 9) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep9
  change mmFiber10StateAt 9 ∈ closeChainFiber mmWord mmFiber10DirectStates (2 + 62) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 2 62 [mmFiber10StateAt 0] (mmFiber10StateAt 9) h2

theorem mmFiber10State10_in_close :
    mmFiber10StateAt 10 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 2 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 2) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep2
  have h2 : mmFiber10StateAt 10 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 2) (mmFiber10StateAt 10) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep10
  change mmFiber10StateAt 10 ∈ closeChainFiber mmWord mmFiber10DirectStates (2 + 62) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 2 62 [mmFiber10StateAt 0] (mmFiber10StateAt 10) h2

theorem mmFiber10State11_in_close :
    mmFiber10StateAt 11 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 1 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 1) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep1
  have h2 : mmFiber10StateAt 3 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 1) (mmFiber10StateAt 3) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep3
  have h3 : mmFiber10StateAt 11 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 3) (mmFiber10StateAt 11) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep11
  change mmFiber10StateAt 11 ∈ closeChainFiber mmWord mmFiber10DirectStates (3 + 61) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 3 61 [mmFiber10StateAt 0] (mmFiber10StateAt 11) h3

theorem mmFiber10State12_in_close :
    mmFiber10StateAt 12 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 2 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 2) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep2
  have h2 : mmFiber10StateAt 4 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 2) (mmFiber10StateAt 4) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep4
  have h3 : mmFiber10StateAt 12 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 4) (mmFiber10StateAt 12) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep12
  change mmFiber10StateAt 12 ∈ closeChainFiber mmWord mmFiber10DirectStates (3 + 61) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 3 61 [mmFiber10StateAt 0] (mmFiber10StateAt 12) h3

theorem mmFiber10State13_in_close :
    mmFiber10StateAt 13 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 7 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 7) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep7
  have h2 : mmFiber10StateAt 5 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 7) (mmFiber10StateAt 5) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep5
  have h3 : mmFiber10StateAt 13 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 5) (mmFiber10StateAt 13) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep13
  change mmFiber10StateAt 13 ∈ closeChainFiber mmWord mmFiber10DirectStates (3 + 61) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 3 61 [mmFiber10StateAt 0] (mmFiber10StateAt 13) h3

theorem mmFiber10State14_in_close :
    mmFiber10StateAt 14 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 1 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 1) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep1
  have h2 : mmFiber10StateAt 6 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 1) (mmFiber10StateAt 6) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep6
  have h3 : mmFiber10StateAt 14 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 6) (mmFiber10StateAt 14) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep14
  change mmFiber10StateAt 14 ∈ closeChainFiber mmWord mmFiber10DirectStates (3 + 61) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 3 61 [mmFiber10StateAt 0] (mmFiber10StateAt 14) h3

theorem mmFiber10State15_in_close :
    mmFiber10StateAt 15 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 7 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 7) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep7
  have h2 : mmFiber10StateAt 15 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 7) (mmFiber10StateAt 15) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep15
  change mmFiber10StateAt 15 ∈ closeChainFiber mmWord mmFiber10DirectStates (2 + 62) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 2 62 [mmFiber10StateAt 0] (mmFiber10StateAt 15) h2

theorem mmFiber10State16_in_close :
    mmFiber10StateAt 16 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 16 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 16) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep16
  change mmFiber10StateAt 16 ∈ closeChainFiber mmWord mmFiber10DirectStates (1 + 63) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 1 63 [mmFiber10StateAt 0] (mmFiber10StateAt 16) h1

theorem mmFiber10State17_in_close :
    mmFiber10StateAt 17 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 1 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 1) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep1
  have h2 : mmFiber10StateAt 17 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 1) (mmFiber10StateAt 17) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep17
  change mmFiber10StateAt 17 ∈ closeChainFiber mmWord mmFiber10DirectStates (2 + 62) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 2 62 [mmFiber10StateAt 0] (mmFiber10StateAt 17) h2

theorem mmFiber10State18_in_close :
    mmFiber10StateAt 18 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 2 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 2) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep2
  have h2 : mmFiber10StateAt 18 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 2) (mmFiber10StateAt 18) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep18
  change mmFiber10StateAt 18 ∈ closeChainFiber mmWord mmFiber10DirectStates (2 + 62) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 2 62 [mmFiber10StateAt 0] (mmFiber10StateAt 18) h2

theorem mmFiber10State19_in_close :
    mmFiber10StateAt 19 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 1 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 1) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep1
  have h2 : mmFiber10StateAt 3 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 1) (mmFiber10StateAt 3) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep3
  have h3 : mmFiber10StateAt 19 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 3) (mmFiber10StateAt 19) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep19
  change mmFiber10StateAt 19 ∈ closeChainFiber mmWord mmFiber10DirectStates (3 + 61) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 3 61 [mmFiber10StateAt 0] (mmFiber10StateAt 19) h3

theorem mmFiber10State20_in_close :
    mmFiber10StateAt 20 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 16 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 16) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep16
  have h2 : mmFiber10StateAt 20 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 16) (mmFiber10StateAt 20) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep20
  change mmFiber10StateAt 20 ∈ closeChainFiber mmWord mmFiber10DirectStates (2 + 62) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 2 62 [mmFiber10StateAt 0] (mmFiber10StateAt 20) h2

theorem mmFiber10State21_in_close :
    mmFiber10StateAt 21 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 1 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 1) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep1
  have h2 : mmFiber10StateAt 17 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 1) (mmFiber10StateAt 17) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep17
  have h3 : mmFiber10StateAt 21 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 17) (mmFiber10StateAt 21) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep21
  change mmFiber10StateAt 21 ∈ closeChainFiber mmWord mmFiber10DirectStates (3 + 61) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 3 61 [mmFiber10StateAt 0] (mmFiber10StateAt 21) h3

theorem mmFiber10State22_in_close :
    mmFiber10StateAt 22 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 1 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 1) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep1
  have h2 : mmFiber10StateAt 6 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 1) (mmFiber10StateAt 6) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep6
  have h3 : mmFiber10StateAt 22 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 6) (mmFiber10StateAt 22) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep22
  change mmFiber10StateAt 22 ∈ closeChainFiber mmWord mmFiber10DirectStates (3 + 61) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 3 61 [mmFiber10StateAt 0] (mmFiber10StateAt 22) h3

theorem mmFiber10State23_in_close :
    mmFiber10StateAt 23 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 7 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 7) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep7
  have h2 : mmFiber10StateAt 23 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 7) (mmFiber10StateAt 23) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep23
  change mmFiber10StateAt 23 ∈ closeChainFiber mmWord mmFiber10DirectStates (2 + 62) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 2 62 [mmFiber10StateAt 0] (mmFiber10StateAt 23) h2

theorem mmFiber10State24_in_close :
    mmFiber10StateAt 24 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 8 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 8) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep8
  have h2 : mmFiber10StateAt 24 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 8) (mmFiber10StateAt 24) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep24
  change mmFiber10StateAt 24 ∈ closeChainFiber mmWord mmFiber10DirectStates (2 + 62) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 2 62 [mmFiber10StateAt 0] (mmFiber10StateAt 24) h2

theorem mmFiber10State25_in_close :
    mmFiber10StateAt 25 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 1 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 1) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep1
  have h2 : mmFiber10StateAt 9 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 1) (mmFiber10StateAt 9) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep9
  have h3 : mmFiber10StateAt 25 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 9) (mmFiber10StateAt 25) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep25
  change mmFiber10StateAt 25 ∈ closeChainFiber mmWord mmFiber10DirectStates (3 + 61) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 3 61 [mmFiber10StateAt 0] (mmFiber10StateAt 25) h3

theorem mmFiber10State26_in_close :
    mmFiber10StateAt 26 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 2 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 2) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep2
  have h2 : mmFiber10StateAt 10 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 2) (mmFiber10StateAt 10) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep10
  have h3 : mmFiber10StateAt 26 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 10) (mmFiber10StateAt 26) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep26
  change mmFiber10StateAt 26 ∈ closeChainFiber mmWord mmFiber10DirectStates (3 + 61) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 3 61 [mmFiber10StateAt 0] (mmFiber10StateAt 26) h3

theorem mmFiber10State27_in_close :
    mmFiber10StateAt 27 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 1 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 1) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep1
  have h2 : mmFiber10StateAt 3 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 1) (mmFiber10StateAt 3) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep3
  have h3 : mmFiber10StateAt 11 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 3) (mmFiber10StateAt 11) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep11
  have h4 : mmFiber10StateAt 27 ∈ closeChainFiber mmWord mmFiber10DirectStates 4 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0]
      (mmFiber10StateAt 11) (mmFiber10StateAt 27) (by decide) h3 (by decide)
      mmFiber10ReverseSingleStep27
  change mmFiber10StateAt 27 ∈ closeChainFiber mmWord mmFiber10DirectStates (4 + 60) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 4 60 [mmFiber10StateAt 0] (mmFiber10StateAt 27) h4

theorem mmFiber10State28_in_close :
    mmFiber10StateAt 28 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 8 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 8) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep8
  have h2 : mmFiber10StateAt 24 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 8) (mmFiber10StateAt 24) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep24
  have h3 : mmFiber10StateAt 28 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 24) (mmFiber10StateAt 28) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep28
  change mmFiber10StateAt 28 ∈ closeChainFiber mmWord mmFiber10DirectStates (3 + 61) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 3 61 [mmFiber10StateAt 0] (mmFiber10StateAt 28) h3

theorem mmFiber10State29_in_close :
    mmFiber10StateAt 29 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 1 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 1) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep1
  have h2 : mmFiber10StateAt 9 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 1) (mmFiber10StateAt 9) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep9
  have h3 : mmFiber10StateAt 25 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 9) (mmFiber10StateAt 25) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep25
  have h4 : mmFiber10StateAt 29 ∈ closeChainFiber mmWord mmFiber10DirectStates 4 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0]
      (mmFiber10StateAt 25) (mmFiber10StateAt 29) (by decide) h3 (by decide)
      mmFiber10ReverseSingleStep29
  change mmFiber10StateAt 29 ∈ closeChainFiber mmWord mmFiber10DirectStates (4 + 60) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 4 60 [mmFiber10StateAt 0] (mmFiber10StateAt 29) h4

theorem mmFiber10State30_in_close :
    mmFiber10StateAt 30 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 1 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 1) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep1
  have h2 : mmFiber10StateAt 6 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 1) (mmFiber10StateAt 6) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep6
  have h3 : mmFiber10StateAt 14 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 6) (mmFiber10StateAt 14) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep14
  have h4 : mmFiber10StateAt 30 ∈ closeChainFiber mmWord mmFiber10DirectStates 4 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0]
      (mmFiber10StateAt 14) (mmFiber10StateAt 30) (by decide) h3 (by decide)
      mmFiber10ReverseSingleStep30
  change mmFiber10StateAt 30 ∈ closeChainFiber mmWord mmFiber10DirectStates (4 + 60) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 4 60 [mmFiber10StateAt 0] (mmFiber10StateAt 30) h4

theorem mmFiber10State31_in_close :
    mmFiber10StateAt 31 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 7 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 7) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep7
  have h2 : mmFiber10StateAt 15 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 7) (mmFiber10StateAt 15) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep15
  have h3 : mmFiber10StateAt 31 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 15) (mmFiber10StateAt 31) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep31
  change mmFiber10StateAt 31 ∈ closeChainFiber mmWord mmFiber10DirectStates (3 + 61) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 3 61 [mmFiber10StateAt 0] (mmFiber10StateAt 31) h3

theorem mmFiber10State32_in_close :
    mmFiber10StateAt 32 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 32 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 32) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep32
  change mmFiber10StateAt 32 ∈ closeChainFiber mmWord mmFiber10DirectStates (1 + 63) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 1 63 [mmFiber10StateAt 0] (mmFiber10StateAt 32) h1

theorem mmFiber10State33_in_close :
    mmFiber10StateAt 33 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 1 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 1) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep1
  have h2 : mmFiber10StateAt 33 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 1) (mmFiber10StateAt 33) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep33
  change mmFiber10StateAt 33 ∈ closeChainFiber mmWord mmFiber10DirectStates (2 + 62) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 2 62 [mmFiber10StateAt 0] (mmFiber10StateAt 33) h2

theorem mmFiber10State34_in_close :
    mmFiber10StateAt 34 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 2 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 2) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep2
  have h2 : mmFiber10StateAt 34 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 2) (mmFiber10StateAt 34) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep34
  change mmFiber10StateAt 34 ∈ closeChainFiber mmWord mmFiber10DirectStates (2 + 62) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 2 62 [mmFiber10StateAt 0] (mmFiber10StateAt 34) h2

theorem mmFiber10State35_in_close :
    mmFiber10StateAt 35 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 32 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 32) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep32
  have h2 : mmFiber10StateAt 35 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 32) (mmFiber10StateAt 35) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep35
  change mmFiber10StateAt 35 ∈ closeChainFiber mmWord mmFiber10DirectStates (2 + 62) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 2 62 [mmFiber10StateAt 0] (mmFiber10StateAt 35) h2

theorem mmFiber10State36_in_close :
    mmFiber10StateAt 36 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 32 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 32) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep32
  have h2 : mmFiber10StateAt 36 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 32) (mmFiber10StateAt 36) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep36
  change mmFiber10StateAt 36 ∈ closeChainFiber mmWord mmFiber10DirectStates (2 + 62) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 2 62 [mmFiber10StateAt 0] (mmFiber10StateAt 36) h2

theorem mmFiber10State37_in_close :
    mmFiber10StateAt 37 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 1 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 1) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep1
  have h2 : mmFiber10StateAt 33 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 1) (mmFiber10StateAt 33) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep33
  have h3 : mmFiber10StateAt 37 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 33) (mmFiber10StateAt 37) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep37
  change mmFiber10StateAt 37 ∈ closeChainFiber mmWord mmFiber10DirectStates (3 + 61) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 3 61 [mmFiber10StateAt 0] (mmFiber10StateAt 37) h3

theorem mmFiber10State38_in_close :
    mmFiber10StateAt 38 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 1 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 1) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep1
  have h2 : mmFiber10StateAt 6 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 1) (mmFiber10StateAt 6) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep6
  have h3 : mmFiber10StateAt 38 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 6) (mmFiber10StateAt 38) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep38
  change mmFiber10StateAt 38 ∈ closeChainFiber mmWord mmFiber10DirectStates (3 + 61) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 3 61 [mmFiber10StateAt 0] (mmFiber10StateAt 38) h3

theorem mmFiber10State39_in_close :
    mmFiber10StateAt 39 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 7 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 7) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep7
  have h2 : mmFiber10StateAt 39 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 7) (mmFiber10StateAt 39) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep39
  change mmFiber10StateAt 39 ∈ closeChainFiber mmWord mmFiber10DirectStates (2 + 62) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 2 62 [mmFiber10StateAt 0] (mmFiber10StateAt 39) h2

theorem mmFiber10State40_in_close :
    mmFiber10StateAt 40 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 8 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 8) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep8
  have h2 : mmFiber10StateAt 40 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 8) (mmFiber10StateAt 40) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep40
  change mmFiber10StateAt 40 ∈ closeChainFiber mmWord mmFiber10DirectStates (2 + 62) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 2 62 [mmFiber10StateAt 0] (mmFiber10StateAt 40) h2

theorem mmFiber10State41_in_close :
    mmFiber10StateAt 41 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 1 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 1) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep1
  have h2 : mmFiber10StateAt 9 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 1) (mmFiber10StateAt 9) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep9
  have h3 : mmFiber10StateAt 41 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 9) (mmFiber10StateAt 41) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep41
  change mmFiber10StateAt 41 ∈ closeChainFiber mmWord mmFiber10DirectStates (3 + 61) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 3 61 [mmFiber10StateAt 0] (mmFiber10StateAt 41) h3

theorem mmFiber10State42_in_close :
    mmFiber10StateAt 42 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 2 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 2) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep2
  have h2 : mmFiber10StateAt 10 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 2) (mmFiber10StateAt 10) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep10
  have h3 : mmFiber10StateAt 42 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 10) (mmFiber10StateAt 42) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep42
  change mmFiber10StateAt 42 ∈ closeChainFiber mmWord mmFiber10DirectStates (3 + 61) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 3 61 [mmFiber10StateAt 0] (mmFiber10StateAt 42) h3

theorem mmFiber10State43_in_close :
    mmFiber10StateAt 43 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 8 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 8) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep8
  have h2 : mmFiber10StateAt 40 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 8) (mmFiber10StateAt 40) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep40
  have h3 : mmFiber10StateAt 43 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 40) (mmFiber10StateAt 43) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep43
  change mmFiber10StateAt 43 ∈ closeChainFiber mmWord mmFiber10DirectStates (3 + 61) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 3 61 [mmFiber10StateAt 0] (mmFiber10StateAt 43) h3

theorem mmFiber10State44_in_close :
    mmFiber10StateAt 44 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 8 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 8) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep8
  have h2 : mmFiber10StateAt 40 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 8) (mmFiber10StateAt 40) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep40
  have h3 : mmFiber10StateAt 44 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 40) (mmFiber10StateAt 44) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep44
  change mmFiber10StateAt 44 ∈ closeChainFiber mmWord mmFiber10DirectStates (3 + 61) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 3 61 [mmFiber10StateAt 0] (mmFiber10StateAt 44) h3

theorem mmFiber10State45_in_close :
    mmFiber10StateAt 45 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 1 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 1) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep1
  have h2 : mmFiber10StateAt 9 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 1) (mmFiber10StateAt 9) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep9
  have h3 : mmFiber10StateAt 41 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 9) (mmFiber10StateAt 41) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep41
  have h4 : mmFiber10StateAt 45 ∈ closeChainFiber mmWord mmFiber10DirectStates 4 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0]
      (mmFiber10StateAt 41) (mmFiber10StateAt 45) (by decide) h3 (by decide)
      mmFiber10ReverseSingleStep45
  change mmFiber10StateAt 45 ∈ closeChainFiber mmWord mmFiber10DirectStates (4 + 60) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 4 60 [mmFiber10StateAt 0] (mmFiber10StateAt 45) h4

theorem mmFiber10State46_in_close :
    mmFiber10StateAt 46 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 1 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 1) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep1
  have h2 : mmFiber10StateAt 6 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 1) (mmFiber10StateAt 6) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep6
  have h3 : mmFiber10StateAt 14 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 6) (mmFiber10StateAt 14) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep14
  have h4 : mmFiber10StateAt 46 ∈ closeChainFiber mmWord mmFiber10DirectStates 4 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0]
      (mmFiber10StateAt 14) (mmFiber10StateAt 46) (by decide) h3 (by decide)
      mmFiber10ReverseSingleStep46
  change mmFiber10StateAt 46 ∈ closeChainFiber mmWord mmFiber10DirectStates (4 + 60) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 4 60 [mmFiber10StateAt 0] (mmFiber10StateAt 46) h4

theorem mmFiber10State47_in_close :
    mmFiber10StateAt 47 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 7 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 7) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep7
  have h2 : mmFiber10StateAt 15 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 7) (mmFiber10StateAt 15) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep15
  have h3 : mmFiber10StateAt 47 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 15) (mmFiber10StateAt 47) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep47
  change mmFiber10StateAt 47 ∈ closeChainFiber mmWord mmFiber10DirectStates (3 + 61) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 3 61 [mmFiber10StateAt 0] (mmFiber10StateAt 47) h3

theorem mmFiber10State48_in_close :
    mmFiber10StateAt 48 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 16 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 16) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep16
  have h2 : mmFiber10StateAt 48 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 16) (mmFiber10StateAt 48) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep48
  change mmFiber10StateAt 48 ∈ closeChainFiber mmWord mmFiber10DirectStates (2 + 62) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 2 62 [mmFiber10StateAt 0] (mmFiber10StateAt 48) h2

theorem mmFiber10State49_in_close :
    mmFiber10StateAt 49 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 1 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 1) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep1
  have h2 : mmFiber10StateAt 17 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 1) (mmFiber10StateAt 17) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep17
  have h3 : mmFiber10StateAt 49 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 17) (mmFiber10StateAt 49) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep49
  change mmFiber10StateAt 49 ∈ closeChainFiber mmWord mmFiber10DirectStates (3 + 61) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 3 61 [mmFiber10StateAt 0] (mmFiber10StateAt 49) h3

theorem mmFiber10State50_in_close :
    mmFiber10StateAt 50 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 2 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 2) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep2
  have h2 : mmFiber10StateAt 18 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 2) (mmFiber10StateAt 18) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep18
  have h3 : mmFiber10StateAt 50 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 18) (mmFiber10StateAt 50) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep50
  change mmFiber10StateAt 50 ∈ closeChainFiber mmWord mmFiber10DirectStates (3 + 61) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 3 61 [mmFiber10StateAt 0] (mmFiber10StateAt 50) h3

theorem mmFiber10State51_in_close :
    mmFiber10StateAt 51 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 1 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 1) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep1
  have h2 : mmFiber10StateAt 3 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 1) (mmFiber10StateAt 3) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep3
  have h3 : mmFiber10StateAt 19 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 3) (mmFiber10StateAt 19) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep19
  have h4 : mmFiber10StateAt 51 ∈ closeChainFiber mmWord mmFiber10DirectStates 4 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0]
      (mmFiber10StateAt 19) (mmFiber10StateAt 51) (by decide) h3 (by decide)
      mmFiber10ReverseSingleStep51
  change mmFiber10StateAt 51 ∈ closeChainFiber mmWord mmFiber10DirectStates (4 + 60) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 4 60 [mmFiber10StateAt 0] (mmFiber10StateAt 51) h4

theorem mmFiber10State52_in_close :
    mmFiber10StateAt 52 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 8 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 8) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep8
  have h2 : mmFiber10StateAt 40 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 8) (mmFiber10StateAt 40) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep40
  have h3 : mmFiber10StateAt 52 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 40) (mmFiber10StateAt 52) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep52
  change mmFiber10StateAt 52 ∈ closeChainFiber mmWord mmFiber10DirectStates (3 + 61) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 3 61 [mmFiber10StateAt 0] (mmFiber10StateAt 52) h3

theorem mmFiber10State53_in_close :
    mmFiber10StateAt 53 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 1 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 1) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep1
  have h2 : mmFiber10StateAt 9 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 1) (mmFiber10StateAt 9) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep9
  have h3 : mmFiber10StateAt 41 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 9) (mmFiber10StateAt 41) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep41
  have h4 : mmFiber10StateAt 53 ∈ closeChainFiber mmWord mmFiber10DirectStates 4 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0]
      (mmFiber10StateAt 41) (mmFiber10StateAt 53) (by decide) h3 (by decide)
      mmFiber10ReverseSingleStep53
  change mmFiber10StateAt 53 ∈ closeChainFiber mmWord mmFiber10DirectStates (4 + 60) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 4 60 [mmFiber10StateAt 0] (mmFiber10StateAt 53) h4

theorem mmFiber10State54_in_close :
    mmFiber10StateAt 54 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 1 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 1) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep1
  have h2 : mmFiber10StateAt 6 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 1) (mmFiber10StateAt 6) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep6
  have h3 : mmFiber10StateAt 22 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 6) (mmFiber10StateAt 22) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep22
  have h4 : mmFiber10StateAt 54 ∈ closeChainFiber mmWord mmFiber10DirectStates 4 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0]
      (mmFiber10StateAt 22) (mmFiber10StateAt 54) (by decide) h3 (by decide)
      mmFiber10ReverseSingleStep54
  change mmFiber10StateAt 54 ∈ closeChainFiber mmWord mmFiber10DirectStates (4 + 60) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 4 60 [mmFiber10StateAt 0] (mmFiber10StateAt 54) h4

theorem mmFiber10State55_in_close :
    mmFiber10StateAt 55 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 7 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 7) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep7
  have h2 : mmFiber10StateAt 23 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 7) (mmFiber10StateAt 23) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep23
  have h3 : mmFiber10StateAt 55 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 23) (mmFiber10StateAt 55) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep55
  change mmFiber10StateAt 55 ∈ closeChainFiber mmWord mmFiber10DirectStates (3 + 61) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 3 61 [mmFiber10StateAt 0] (mmFiber10StateAt 55) h3

theorem mmFiber10State56_in_close :
    mmFiber10StateAt 56 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 7 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 7) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep7
  have h2 : mmFiber10StateAt 39 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 7) (mmFiber10StateAt 39) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep39
  have h3 : mmFiber10StateAt 56 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 39) (mmFiber10StateAt 56) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep56
  change mmFiber10StateAt 56 ∈ closeChainFiber mmWord mmFiber10DirectStates (3 + 61) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 3 61 [mmFiber10StateAt 0] (mmFiber10StateAt 56) h3

theorem mmFiber10State57_in_close :
    mmFiber10StateAt 57 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 1 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 1) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep1
  have h2 : mmFiber10StateAt 6 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 1) (mmFiber10StateAt 6) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep6
  have h3 : mmFiber10StateAt 38 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 6) (mmFiber10StateAt 38) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep38
  have h4 : mmFiber10StateAt 57 ∈ closeChainFiber mmWord mmFiber10DirectStates 4 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0]
      (mmFiber10StateAt 38) (mmFiber10StateAt 57) (by decide) h3 (by decide)
      mmFiber10ReverseSingleStep57
  change mmFiber10StateAt 57 ∈ closeChainFiber mmWord mmFiber10DirectStates (4 + 60) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 4 60 [mmFiber10StateAt 0] (mmFiber10StateAt 57) h4

theorem mmFiber10State58_in_close :
    mmFiber10StateAt 58 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 32 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 32) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep32
  have h2 : mmFiber10StateAt 36 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 32) (mmFiber10StateAt 36) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep36
  have h3 : mmFiber10StateAt 58 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 36) (mmFiber10StateAt 58) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep58
  change mmFiber10StateAt 58 ∈ closeChainFiber mmWord mmFiber10DirectStates (3 + 61) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 3 61 [mmFiber10StateAt 0] (mmFiber10StateAt 58) h3

theorem mmFiber10State59_in_close :
    mmFiber10StateAt 59 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 1 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 1) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep1
  have h2 : mmFiber10StateAt 33 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 1) (mmFiber10StateAt 33) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep33
  have h3 : mmFiber10StateAt 37 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 33) (mmFiber10StateAt 37) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep37
  have h4 : mmFiber10StateAt 59 ∈ closeChainFiber mmWord mmFiber10DirectStates 4 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0]
      (mmFiber10StateAt 37) (mmFiber10StateAt 59) (by decide) h3 (by decide)
      mmFiber10ReverseSingleStep59
  change mmFiber10StateAt 59 ∈ closeChainFiber mmWord mmFiber10DirectStates (4 + 60) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 4 60 [mmFiber10StateAt 0] (mmFiber10StateAt 59) h4

theorem mmFiber10State60_in_close :
    mmFiber10StateAt 60 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 32 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 32) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep32
  have h2 : mmFiber10StateAt 60 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 32) (mmFiber10StateAt 60) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep60
  change mmFiber10StateAt 60 ∈ closeChainFiber mmWord mmFiber10DirectStates (2 + 62) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 2 62 [mmFiber10StateAt 0] (mmFiber10StateAt 60) h2

theorem mmFiber10State61_in_close :
    mmFiber10StateAt 61 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 1 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 1) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep1
  have h2 : mmFiber10StateAt 33 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 1) (mmFiber10StateAt 33) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep33
  have h3 : mmFiber10StateAt 61 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 33) (mmFiber10StateAt 61) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep61
  change mmFiber10StateAt 61 ∈ closeChainFiber mmWord mmFiber10DirectStates (3 + 61) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 3 61 [mmFiber10StateAt 0] (mmFiber10StateAt 61) h3

theorem mmFiber10State62_in_close :
    mmFiber10StateAt 62 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 2 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 2) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep2
  have h2 : mmFiber10StateAt 34 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 2) (mmFiber10StateAt 34) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep34
  have h3 : mmFiber10StateAt 62 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 34) (mmFiber10StateAt 62) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep62
  change mmFiber10StateAt 62 ∈ closeChainFiber mmWord mmFiber10DirectStates (3 + 61) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 3 61 [mmFiber10StateAt 0] (mmFiber10StateAt 62) h3

theorem mmFiber10State63_in_close :
    mmFiber10StateAt 63 ∈ closeChainFiber mmWord mmFiber10DirectStates mmFiber10DirectStates.length [mmFiber10StateAt 0] := by
  have h0 : mmFiber10StateAt 0 ∈ closeChainFiber mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber10StateAt 32 ∈ closeChainFiber mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 0 [mmFiber10StateAt 0]
      (mmFiber10StateAt 0) (mmFiber10StateAt 32) (by decide) h0 (by decide)
      mmFiber10ReverseSingleStep32
  have h2 : mmFiber10StateAt 35 ∈ closeChainFiber mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 1 [mmFiber10StateAt 0]
      (mmFiber10StateAt 32) (mmFiber10StateAt 35) (by decide) h1 (by decide)
      mmFiber10ReverseSingleStep35
  have h3 : mmFiber10StateAt 63 ∈ closeChainFiber mmWord mmFiber10DirectStates 3 [mmFiber10StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber10DirectStates 2 [mmFiber10StateAt 0]
      (mmFiber10StateAt 35) (mmFiber10StateAt 63) (by decide) h2 (by decide)
      mmFiber10ReverseSingleStep63
  change mmFiber10StateAt 63 ∈ closeChainFiber mmWord mmFiber10DirectStates (3 + 61) [mmFiber10StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber10DirectStates 3 61 [mmFiber10StateAt 0] (mmFiber10StateAt 63) h3

theorem mmFiber10DirectConnected :
    chainFiberConnected mmWord mmFiber10DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber10DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber10State0_in_close
  · subst state
    exact mmFiber10State1_in_close
  · subst state
    exact mmFiber10State2_in_close
  · subst state
    exact mmFiber10State3_in_close
  · subst state
    exact mmFiber10State4_in_close
  · subst state
    exact mmFiber10State5_in_close
  · subst state
    exact mmFiber10State6_in_close
  · subst state
    exact mmFiber10State7_in_close
  · subst state
    exact mmFiber10State8_in_close
  · subst state
    exact mmFiber10State9_in_close
  · subst state
    exact mmFiber10State10_in_close
  · subst state
    exact mmFiber10State11_in_close
  · subst state
    exact mmFiber10State12_in_close
  · subst state
    exact mmFiber10State13_in_close
  · subst state
    exact mmFiber10State14_in_close
  · subst state
    exact mmFiber10State15_in_close
  · subst state
    exact mmFiber10State16_in_close
  · subst state
    exact mmFiber10State17_in_close
  · subst state
    exact mmFiber10State18_in_close
  · subst state
    exact mmFiber10State19_in_close
  · subst state
    exact mmFiber10State20_in_close
  · subst state
    exact mmFiber10State21_in_close
  · subst state
    exact mmFiber10State22_in_close
  · subst state
    exact mmFiber10State23_in_close
  · subst state
    exact mmFiber10State24_in_close
  · subst state
    exact mmFiber10State25_in_close
  · subst state
    exact mmFiber10State26_in_close
  · subst state
    exact mmFiber10State27_in_close
  · subst state
    exact mmFiber10State28_in_close
  · subst state
    exact mmFiber10State29_in_close
  · subst state
    exact mmFiber10State30_in_close
  · subst state
    exact mmFiber10State31_in_close
  · subst state
    exact mmFiber10State32_in_close
  · subst state
    exact mmFiber10State33_in_close
  · subst state
    exact mmFiber10State34_in_close
  · subst state
    exact mmFiber10State35_in_close
  · subst state
    exact mmFiber10State36_in_close
  · subst state
    exact mmFiber10State37_in_close
  · subst state
    exact mmFiber10State38_in_close
  · subst state
    exact mmFiber10State39_in_close
  · subst state
    exact mmFiber10State40_in_close
  · subst state
    exact mmFiber10State41_in_close
  · subst state
    exact mmFiber10State42_in_close
  · subst state
    exact mmFiber10State43_in_close
  · subst state
    exact mmFiber10State44_in_close
  · subst state
    exact mmFiber10State45_in_close
  · subst state
    exact mmFiber10State46_in_close
  · subst state
    exact mmFiber10State47_in_close
  · subst state
    exact mmFiber10State48_in_close
  · subst state
    exact mmFiber10State49_in_close
  · subst state
    exact mmFiber10State50_in_close
  · subst state
    exact mmFiber10State51_in_close
  · subst state
    exact mmFiber10State52_in_close
  · subst state
    exact mmFiber10State53_in_close
  · subst state
    exact mmFiber10State54_in_close
  · subst state
    exact mmFiber10State55_in_close
  · subst state
    exact mmFiber10State56_in_close
  · subst state
    exact mmFiber10State57_in_close
  · subst state
    exact mmFiber10State58_in_close
  · subst state
    exact mmFiber10State59_in_close
  · subst state
    exact mmFiber10State60_in_close
  · subst state
    exact mmFiber10State61_in_close
  · subst state
    exact mmFiber10State62_in_close
  · subst state
    exact mmFiber10State63_in_close
  · cases h
end GoertzelLemma818LengthTwoMMBridge

end Mettapedia.GraphTheory.FourColor
