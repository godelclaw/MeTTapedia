import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for `mirror,mirror` size-64 fiber 30

This module proves direct connectedness for one generated size-64 fiber from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMMBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorMirrorCertificate
open GoertzelLemma818MirrorMirrorReverseAudit

def mmFiber30StateAt (i : Nat) : List TauState :=
  directStates (mmFiber30RowAt i).sourceLeft (mmFiber30RowAt i).sourceRight

def mmFiber30DirectStates : List (List TauState) :=
  [mmFiber30StateAt 0, mmFiber30StateAt 1, mmFiber30StateAt 2, mmFiber30StateAt 3, mmFiber30StateAt 4, mmFiber30StateAt 5, mmFiber30StateAt 6, mmFiber30StateAt 7, mmFiber30StateAt 8, mmFiber30StateAt 9, mmFiber30StateAt 10, mmFiber30StateAt 11, mmFiber30StateAt 12, mmFiber30StateAt 13, mmFiber30StateAt 14, mmFiber30StateAt 15, mmFiber30StateAt 16, mmFiber30StateAt 17, mmFiber30StateAt 18, mmFiber30StateAt 19, mmFiber30StateAt 20, mmFiber30StateAt 21, mmFiber30StateAt 22, mmFiber30StateAt 23, mmFiber30StateAt 24, mmFiber30StateAt 25, mmFiber30StateAt 26, mmFiber30StateAt 27, mmFiber30StateAt 28, mmFiber30StateAt 29, mmFiber30StateAt 30, mmFiber30StateAt 31, mmFiber30StateAt 32, mmFiber30StateAt 33, mmFiber30StateAt 34, mmFiber30StateAt 35, mmFiber30StateAt 36, mmFiber30StateAt 37, mmFiber30StateAt 38, mmFiber30StateAt 39, mmFiber30StateAt 40, mmFiber30StateAt 41, mmFiber30StateAt 42, mmFiber30StateAt 43, mmFiber30StateAt 44, mmFiber30StateAt 45, mmFiber30StateAt 46, mmFiber30StateAt 47, mmFiber30StateAt 48, mmFiber30StateAt 49, mmFiber30StateAt 50, mmFiber30StateAt 51, mmFiber30StateAt 52, mmFiber30StateAt 53, mmFiber30StateAt 54, mmFiber30StateAt 55, mmFiber30StateAt 56, mmFiber30StateAt 57, mmFiber30StateAt 58, mmFiber30StateAt 59, mmFiber30StateAt 60, mmFiber30StateAt 61, mmFiber30StateAt 62, mmFiber30StateAt 63]

theorem mmFiber30ReverseRow_1_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk0_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 0) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 0) (mmFiber30StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 0) (mmFiber30StateAt 1)
    (mmFiber30RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 1) (by decide) mmFiber30ReverseRow_1_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_2_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk1_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 2) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber30ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 0) (mmFiber30StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 0) (mmFiber30StateAt 2)
    (mmFiber30RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 2) (by decide) mmFiber30ReverseRow_2_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_3_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk1_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 2) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 1) (mmFiber30StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 1) (mmFiber30StateAt 3)
    (mmFiber30RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 3) (by decide) mmFiber30ReverseRow_3_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_4_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk2_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 4) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber30ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 2) (mmFiber30StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 2) (mmFiber30StateAt 4)
    (mmFiber30RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 4) (by decide) mmFiber30ReverseRow_4_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_5_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk2_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 4) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 7) (mmFiber30StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 7) (mmFiber30StateAt 5)
    (mmFiber30RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 5) (by decide) mmFiber30ReverseRow_5_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_6_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk3_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 6) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber30ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 1) (mmFiber30StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 1) (mmFiber30StateAt 6)
    (mmFiber30RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 6) (by decide) mmFiber30ReverseRow_6_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_7_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk3_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 6) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 0) (mmFiber30StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 0) (mmFiber30StateAt 7)
    (mmFiber30RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 7) (by decide) mmFiber30ReverseRow_7_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_8_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 8) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk4_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 8) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber30ReverseSingleStep8 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 0) (mmFiber30StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 0) (mmFiber30StateAt 8)
    (mmFiber30RowAt 8).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 8) (by decide) mmFiber30ReverseRow_8_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_9_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 9) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk4_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 8) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep9 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 1) (mmFiber30StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 1) (mmFiber30StateAt 9)
    (mmFiber30RowAt 9).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 9) (by decide) mmFiber30ReverseRow_9_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_10_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 10) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk5_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 10) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber30ReverseSingleStep10 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 2) (mmFiber30StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 2) (mmFiber30StateAt 10)
    (mmFiber30RowAt 10).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 10) (by decide) mmFiber30ReverseRow_10_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_11_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 11) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk5_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 10) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep11 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 3) (mmFiber30StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 3) (mmFiber30StateAt 11)
    (mmFiber30RowAt 11).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 11) (by decide) mmFiber30ReverseRow_11_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_12_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 12) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk6_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 12) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber30ReverseSingleStep12 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 4) (mmFiber30StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 4) (mmFiber30StateAt 12)
    (mmFiber30RowAt 12).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 12) (by decide) mmFiber30ReverseRow_12_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_13_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 13) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk6_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 12) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep13 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 5) (mmFiber30StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 5) (mmFiber30StateAt 13)
    (mmFiber30RowAt 13).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 13) (by decide) mmFiber30ReverseRow_13_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_14_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 14) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk7_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 14) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber30ReverseSingleStep14 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 6) (mmFiber30StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 6) (mmFiber30StateAt 14)
    (mmFiber30RowAt 14).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 14) (by decide) mmFiber30ReverseRow_14_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_15_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 15) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk7_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 14) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep15 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 7) (mmFiber30StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 7) (mmFiber30StateAt 15)
    (mmFiber30RowAt 15).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 15) (by decide) mmFiber30ReverseRow_15_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_16_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 16) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk8_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 16) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber30ReverseSingleStep16 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 0) (mmFiber30StateAt 16) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 0) (mmFiber30StateAt 16)
    (mmFiber30RowAt 16).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 16) (by decide) mmFiber30ReverseRow_16_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_17_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 17) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk8_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 16) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep17 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 1) (mmFiber30StateAt 17) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 1) (mmFiber30StateAt 17)
    (mmFiber30RowAt 17).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 17) (by decide) mmFiber30ReverseRow_17_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_18_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 18) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk9_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 18) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber30ReverseSingleStep18 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 2) (mmFiber30StateAt 18) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 2) (mmFiber30StateAt 18)
    (mmFiber30RowAt 18).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 18) (by decide) mmFiber30ReverseRow_18_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_19_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 19) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk9_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 18) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep19 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 3) (mmFiber30StateAt 19) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 3) (mmFiber30StateAt 19)
    (mmFiber30RowAt 19).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 19) (by decide) mmFiber30ReverseRow_19_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_20_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 20) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk10_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 20) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber30ReverseSingleStep20 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 16) (mmFiber30StateAt 20) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 16) (mmFiber30StateAt 20)
    (mmFiber30RowAt 20).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 20) (by decide) mmFiber30ReverseRow_20_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_21_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 21) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk10_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 20) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep21 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 17) (mmFiber30StateAt 21) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 17) (mmFiber30StateAt 21)
    (mmFiber30RowAt 21).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 21) (by decide) mmFiber30ReverseRow_21_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_22_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 22) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk11_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 22) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber30ReverseSingleStep22 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 6) (mmFiber30StateAt 22) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 6) (mmFiber30StateAt 22)
    (mmFiber30RowAt 22).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 22) (by decide) mmFiber30ReverseRow_22_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_23_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 23) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk11_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 22) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep23 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 7) (mmFiber30StateAt 23) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 7) (mmFiber30StateAt 23)
    (mmFiber30RowAt 23).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 23) (by decide) mmFiber30ReverseRow_23_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_24_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 24) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk12_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 24) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber30ReverseSingleStep24 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 8) (mmFiber30StateAt 24) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 8) (mmFiber30StateAt 24)
    (mmFiber30RowAt 24).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 24) (by decide) mmFiber30ReverseRow_24_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_25_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 25) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk12_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 24) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep25 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 9) (mmFiber30StateAt 25) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 9) (mmFiber30StateAt 25)
    (mmFiber30RowAt 25).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 25) (by decide) mmFiber30ReverseRow_25_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_26_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 26) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk13_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 26) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber30ReverseSingleStep26 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 10) (mmFiber30StateAt 26) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 10) (mmFiber30StateAt 26)
    (mmFiber30RowAt 26).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 26) (by decide) mmFiber30ReverseRow_26_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_27_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 27) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk13_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 26) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep27 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 11) (mmFiber30StateAt 27) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 11) (mmFiber30StateAt 27)
    (mmFiber30RowAt 27).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 27) (by decide) mmFiber30ReverseRow_27_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_28_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 28) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk14_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 28) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber30ReverseSingleStep28 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 24) (mmFiber30StateAt 28) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 24) (mmFiber30StateAt 28)
    (mmFiber30RowAt 28).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 28) (by decide) mmFiber30ReverseRow_28_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_29_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 29) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk14_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 28) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep29 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 25) (mmFiber30StateAt 29) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 25) (mmFiber30StateAt 29)
    (mmFiber30RowAt 29).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 29) (by decide) mmFiber30ReverseRow_29_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_30_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 30) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk15_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 30) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber30ReverseSingleStep30 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 14) (mmFiber30StateAt 30) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 14) (mmFiber30StateAt 30)
    (mmFiber30RowAt 30).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 30) (by decide) mmFiber30ReverseRow_30_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_31_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 31) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk15_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 30) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep31 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 15) (mmFiber30StateAt 31) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 15) (mmFiber30StateAt 31)
    (mmFiber30RowAt 31).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 31) (by decide) mmFiber30ReverseRow_31_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_32_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 32) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk16_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 32) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber30ReverseSingleStep32 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 48) (mmFiber30StateAt 32) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 48) (mmFiber30StateAt 32)
    (mmFiber30RowAt 32).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 32) (by decide) mmFiber30ReverseRow_32_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_33_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 33) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk16_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 32) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep33 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 49) (mmFiber30StateAt 33) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 49) (mmFiber30StateAt 33)
    (mmFiber30RowAt 33).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 33) (by decide) mmFiber30ReverseRow_33_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_34_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 34) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk17_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 34) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber30ReverseSingleStep34 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 22) (mmFiber30StateAt 34) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 22) (mmFiber30StateAt 34)
    (mmFiber30RowAt 34).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 34) (by decide) mmFiber30ReverseRow_34_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_35_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 35) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk17_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 34) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep35 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 23) (mmFiber30StateAt 35) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 23) (mmFiber30StateAt 35)
    (mmFiber30RowAt 35).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 35) (by decide) mmFiber30ReverseRow_35_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_36_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 36) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk18_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 36) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber30ReverseSingleStep36 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 18) (mmFiber30StateAt 36) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 18) (mmFiber30StateAt 36)
    (mmFiber30RowAt 36).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 36) (by decide) mmFiber30ReverseRow_36_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_37_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 37) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk18_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 36) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep37 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 39) (mmFiber30StateAt 37) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 39) (mmFiber30StateAt 37)
    (mmFiber30RowAt 37).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 37) (by decide) mmFiber30ReverseRow_37_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_38_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 38) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk19_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 38) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber30ReverseSingleStep38 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 17) (mmFiber30StateAt 38) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 17) (mmFiber30StateAt 38)
    (mmFiber30RowAt 38).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 38) (by decide) mmFiber30ReverseRow_38_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_39_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 39) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk19_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 38) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep39 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 16) (mmFiber30StateAt 39) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 16) (mmFiber30StateAt 39)
    (mmFiber30RowAt 39).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 39) (by decide) mmFiber30ReverseRow_39_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_40_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 40) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk20_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 40) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber30ReverseSingleStep40 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 56) (mmFiber30StateAt 40) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 56) (mmFiber30StateAt 40)
    (mmFiber30RowAt 40).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 40) (by decide) mmFiber30ReverseRow_40_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_41_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 41) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk20_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 40) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep41 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 57) (mmFiber30StateAt 41) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 57) (mmFiber30StateAt 41)
    (mmFiber30RowAt 41).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 41) (by decide) mmFiber30ReverseRow_41_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_42_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 42) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk21_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 42) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber30ReverseSingleStep42 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 58) (mmFiber30StateAt 42) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 58) (mmFiber30StateAt 42)
    (mmFiber30RowAt 42).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 42) (by decide) mmFiber30ReverseRow_42_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_43_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 43) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk21_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 42) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep43 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 40) (mmFiber30StateAt 43) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 40) (mmFiber30StateAt 43)
    (mmFiber30RowAt 43).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 43) (by decide) mmFiber30ReverseRow_43_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_44_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 44) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk22_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 44) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber30ReverseSingleStep44 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 40) (mmFiber30StateAt 44) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 40) (mmFiber30StateAt 44)
    (mmFiber30RowAt 44).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 44) (by decide) mmFiber30ReverseRow_44_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_45_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 45) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk22_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 44) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep45 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 41) (mmFiber30StateAt 45) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 41) (mmFiber30StateAt 45)
    (mmFiber30RowAt 45).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 45) (by decide) mmFiber30ReverseRow_45_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_46_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 46) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk23_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 46) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber30ReverseSingleStep46 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 62) (mmFiber30StateAt 46) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 62) (mmFiber30StateAt 46)
    (mmFiber30RowAt 46).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 46) (by decide) mmFiber30ReverseRow_46_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_47_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 47) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk23_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 46) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep47 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 63) (mmFiber30StateAt 47) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 63) (mmFiber30StateAt 47)
    (mmFiber30RowAt 47).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 47) (by decide) mmFiber30ReverseRow_47_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_48_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 48) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk24_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 48) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber30ReverseSingleStep48 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 8) (mmFiber30StateAt 48) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 8) (mmFiber30StateAt 48)
    (mmFiber30RowAt 48).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 48) (by decide) mmFiber30ReverseRow_48_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_49_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 49) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk24_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 48) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep49 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 9) (mmFiber30StateAt 49) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 9) (mmFiber30StateAt 49)
    (mmFiber30RowAt 49).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 49) (by decide) mmFiber30ReverseRow_49_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_50_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 50) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk25_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 50) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber30ReverseSingleStep50 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 10) (mmFiber30StateAt 50) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 10) (mmFiber30StateAt 50)
    (mmFiber30RowAt 50).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 50) (by decide) mmFiber30ReverseRow_50_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_51_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 51) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk25_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 50) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep51 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 11) (mmFiber30StateAt 51) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 11) (mmFiber30StateAt 51)
    (mmFiber30RowAt 51).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 51) (by decide) mmFiber30ReverseRow_51_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_52_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 52) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk26_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 52) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber30ReverseSingleStep52 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 12) (mmFiber30StateAt 52) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 12) (mmFiber30StateAt 52)
    (mmFiber30RowAt 52).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 52) (by decide) mmFiber30ReverseRow_52_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_53_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 53) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk26_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 52) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep53 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 13) (mmFiber30StateAt 53) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 13) (mmFiber30StateAt 53)
    (mmFiber30RowAt 53).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 53) (by decide) mmFiber30ReverseRow_53_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_54_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 54) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk27_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 54) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber30ReverseSingleStep54 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 14) (mmFiber30StateAt 54) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 14) (mmFiber30StateAt 54)
    (mmFiber30RowAt 54).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 54) (by decide) mmFiber30ReverseRow_54_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_55_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 55) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk27_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 54) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep55 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 15) (mmFiber30StateAt 55) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 15) (mmFiber30StateAt 55)
    (mmFiber30RowAt 55).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 55) (by decide) mmFiber30ReverseRow_55_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_56_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 56) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk28_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 56) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber30ReverseSingleStep56 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 0) (mmFiber30StateAt 56) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 0) (mmFiber30StateAt 56)
    (mmFiber30RowAt 56).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 56) (by decide) mmFiber30ReverseRow_56_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_57_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 57) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk28_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 56) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep57 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 1) (mmFiber30StateAt 57) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 1) (mmFiber30StateAt 57)
    (mmFiber30RowAt 57).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 57) (by decide) mmFiber30ReverseRow_57_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_58_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 58) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk29_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 58) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber30ReverseSingleStep58 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 2) (mmFiber30StateAt 58) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 2) (mmFiber30StateAt 58)
    (mmFiber30RowAt 58).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 58) (by decide) mmFiber30ReverseRow_58_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_59_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 59) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk29_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 58) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep59 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 3) (mmFiber30StateAt 59) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 3) (mmFiber30StateAt 59)
    (mmFiber30RowAt 59).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 59) (by decide) mmFiber30ReverseRow_59_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_60_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 60) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk30_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 60) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber30ReverseSingleStep60 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 4) (mmFiber30StateAt 60) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 4) (mmFiber30StateAt 60)
    (mmFiber30RowAt 60).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 60) (by decide) mmFiber30ReverseRow_60_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_61_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 61) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk30_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 60) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep61 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 5) (mmFiber30StateAt 61) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 5) (mmFiber30StateAt 61)
    (mmFiber30RowAt 61).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 61) (by decide) mmFiber30ReverseRow_61_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_62_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 62) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk31_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 62) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber30ReverseSingleStep62 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 6) (mmFiber30StateAt 62) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 6) (mmFiber30StateAt 62)
    (mmFiber30RowAt 62).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 62) (by decide) mmFiber30ReverseRow_62_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30ReverseRow_63_ok :
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 63) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber30Chunk31_ok
  change (mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 62) &&
    mmRowReverseValid mmFiber30Key mmFiber30Expected (mmFiber30RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber30ReverseSingleStep63 :
    chainSingleKempeStep mmWord (mmFiber30StateAt 7) (mmFiber30StateAt 63) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber30StateAt 7) (mmFiber30StateAt 63)
    (mmFiber30RowAt 63).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber30Key mmFiber30Expected
        (mmFiber30RowAt 63) (by decide) mmFiber30ReverseRow_63_ok
      simpa [mmFiber30StateAt, mmFiber30RowAt, mmFiber30Rows, listGetD, directRow] using h)

theorem mmFiber30State0_in_close :
    mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  change mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 64 [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 0 64 [mmFiber30StateAt 0] (mmFiber30StateAt 0) (by simp [closeChainFiber])

theorem mmFiber30State1_in_close :
    mmFiber30StateAt 1 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 1 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 1) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep1
  change mmFiber30StateAt 1 ∈ closeChainFiber mmWord mmFiber30DirectStates (1 + 63) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 1 63 [mmFiber30StateAt 0] (mmFiber30StateAt 1) h1

theorem mmFiber30State2_in_close :
    mmFiber30StateAt 2 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 2 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 2) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep2
  change mmFiber30StateAt 2 ∈ closeChainFiber mmWord mmFiber30DirectStates (1 + 63) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 1 63 [mmFiber30StateAt 0] (mmFiber30StateAt 2) h1

theorem mmFiber30State3_in_close :
    mmFiber30StateAt 3 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 1 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 1) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep1
  have h2 : mmFiber30StateAt 3 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 1) (mmFiber30StateAt 3) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep3
  change mmFiber30StateAt 3 ∈ closeChainFiber mmWord mmFiber30DirectStates (2 + 62) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 2 62 [mmFiber30StateAt 0] (mmFiber30StateAt 3) h2

theorem mmFiber30State4_in_close :
    mmFiber30StateAt 4 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 2 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 2) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep2
  have h2 : mmFiber30StateAt 4 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 2) (mmFiber30StateAt 4) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep4
  change mmFiber30StateAt 4 ∈ closeChainFiber mmWord mmFiber30DirectStates (2 + 62) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 2 62 [mmFiber30StateAt 0] (mmFiber30StateAt 4) h2

theorem mmFiber30State5_in_close :
    mmFiber30StateAt 5 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 7 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 7) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep7
  have h2 : mmFiber30StateAt 5 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 7) (mmFiber30StateAt 5) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep5
  change mmFiber30StateAt 5 ∈ closeChainFiber mmWord mmFiber30DirectStates (2 + 62) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 2 62 [mmFiber30StateAt 0] (mmFiber30StateAt 5) h2

theorem mmFiber30State6_in_close :
    mmFiber30StateAt 6 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 1 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 1) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep1
  have h2 : mmFiber30StateAt 6 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 1) (mmFiber30StateAt 6) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep6
  change mmFiber30StateAt 6 ∈ closeChainFiber mmWord mmFiber30DirectStates (2 + 62) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 2 62 [mmFiber30StateAt 0] (mmFiber30StateAt 6) h2

theorem mmFiber30State7_in_close :
    mmFiber30StateAt 7 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 7 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 7) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep7
  change mmFiber30StateAt 7 ∈ closeChainFiber mmWord mmFiber30DirectStates (1 + 63) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 1 63 [mmFiber30StateAt 0] (mmFiber30StateAt 7) h1

theorem mmFiber30State8_in_close :
    mmFiber30StateAt 8 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 8 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 8) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep8
  change mmFiber30StateAt 8 ∈ closeChainFiber mmWord mmFiber30DirectStates (1 + 63) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 1 63 [mmFiber30StateAt 0] (mmFiber30StateAt 8) h1

theorem mmFiber30State9_in_close :
    mmFiber30StateAt 9 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 1 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 1) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep1
  have h2 : mmFiber30StateAt 9 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 1) (mmFiber30StateAt 9) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep9
  change mmFiber30StateAt 9 ∈ closeChainFiber mmWord mmFiber30DirectStates (2 + 62) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 2 62 [mmFiber30StateAt 0] (mmFiber30StateAt 9) h2

theorem mmFiber30State10_in_close :
    mmFiber30StateAt 10 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 2 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 2) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep2
  have h2 : mmFiber30StateAt 10 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 2) (mmFiber30StateAt 10) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep10
  change mmFiber30StateAt 10 ∈ closeChainFiber mmWord mmFiber30DirectStates (2 + 62) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 2 62 [mmFiber30StateAt 0] (mmFiber30StateAt 10) h2

theorem mmFiber30State11_in_close :
    mmFiber30StateAt 11 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 1 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 1) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep1
  have h2 : mmFiber30StateAt 3 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 1) (mmFiber30StateAt 3) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep3
  have h3 : mmFiber30StateAt 11 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 3) (mmFiber30StateAt 11) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep11
  change mmFiber30StateAt 11 ∈ closeChainFiber mmWord mmFiber30DirectStates (3 + 61) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 3 61 [mmFiber30StateAt 0] (mmFiber30StateAt 11) h3

theorem mmFiber30State12_in_close :
    mmFiber30StateAt 12 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 2 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 2) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep2
  have h2 : mmFiber30StateAt 4 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 2) (mmFiber30StateAt 4) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep4
  have h3 : mmFiber30StateAt 12 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 4) (mmFiber30StateAt 12) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep12
  change mmFiber30StateAt 12 ∈ closeChainFiber mmWord mmFiber30DirectStates (3 + 61) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 3 61 [mmFiber30StateAt 0] (mmFiber30StateAt 12) h3

theorem mmFiber30State13_in_close :
    mmFiber30StateAt 13 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 7 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 7) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep7
  have h2 : mmFiber30StateAt 5 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 7) (mmFiber30StateAt 5) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep5
  have h3 : mmFiber30StateAt 13 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 5) (mmFiber30StateAt 13) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep13
  change mmFiber30StateAt 13 ∈ closeChainFiber mmWord mmFiber30DirectStates (3 + 61) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 3 61 [mmFiber30StateAt 0] (mmFiber30StateAt 13) h3

theorem mmFiber30State14_in_close :
    mmFiber30StateAt 14 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 1 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 1) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep1
  have h2 : mmFiber30StateAt 6 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 1) (mmFiber30StateAt 6) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep6
  have h3 : mmFiber30StateAt 14 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 6) (mmFiber30StateAt 14) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep14
  change mmFiber30StateAt 14 ∈ closeChainFiber mmWord mmFiber30DirectStates (3 + 61) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 3 61 [mmFiber30StateAt 0] (mmFiber30StateAt 14) h3

theorem mmFiber30State15_in_close :
    mmFiber30StateAt 15 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 7 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 7) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep7
  have h2 : mmFiber30StateAt 15 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 7) (mmFiber30StateAt 15) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep15
  change mmFiber30StateAt 15 ∈ closeChainFiber mmWord mmFiber30DirectStates (2 + 62) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 2 62 [mmFiber30StateAt 0] (mmFiber30StateAt 15) h2

theorem mmFiber30State16_in_close :
    mmFiber30StateAt 16 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 16 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 16) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep16
  change mmFiber30StateAt 16 ∈ closeChainFiber mmWord mmFiber30DirectStates (1 + 63) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 1 63 [mmFiber30StateAt 0] (mmFiber30StateAt 16) h1

theorem mmFiber30State17_in_close :
    mmFiber30StateAt 17 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 1 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 1) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep1
  have h2 : mmFiber30StateAt 17 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 1) (mmFiber30StateAt 17) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep17
  change mmFiber30StateAt 17 ∈ closeChainFiber mmWord mmFiber30DirectStates (2 + 62) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 2 62 [mmFiber30StateAt 0] (mmFiber30StateAt 17) h2

theorem mmFiber30State18_in_close :
    mmFiber30StateAt 18 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 2 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 2) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep2
  have h2 : mmFiber30StateAt 18 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 2) (mmFiber30StateAt 18) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep18
  change mmFiber30StateAt 18 ∈ closeChainFiber mmWord mmFiber30DirectStates (2 + 62) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 2 62 [mmFiber30StateAt 0] (mmFiber30StateAt 18) h2

theorem mmFiber30State19_in_close :
    mmFiber30StateAt 19 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 1 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 1) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep1
  have h2 : mmFiber30StateAt 3 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 1) (mmFiber30StateAt 3) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep3
  have h3 : mmFiber30StateAt 19 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 3) (mmFiber30StateAt 19) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep19
  change mmFiber30StateAt 19 ∈ closeChainFiber mmWord mmFiber30DirectStates (3 + 61) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 3 61 [mmFiber30StateAt 0] (mmFiber30StateAt 19) h3

theorem mmFiber30State20_in_close :
    mmFiber30StateAt 20 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 16 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 16) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep16
  have h2 : mmFiber30StateAt 20 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 16) (mmFiber30StateAt 20) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep20
  change mmFiber30StateAt 20 ∈ closeChainFiber mmWord mmFiber30DirectStates (2 + 62) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 2 62 [mmFiber30StateAt 0] (mmFiber30StateAt 20) h2

theorem mmFiber30State21_in_close :
    mmFiber30StateAt 21 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 1 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 1) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep1
  have h2 : mmFiber30StateAt 17 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 1) (mmFiber30StateAt 17) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep17
  have h3 : mmFiber30StateAt 21 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 17) (mmFiber30StateAt 21) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep21
  change mmFiber30StateAt 21 ∈ closeChainFiber mmWord mmFiber30DirectStates (3 + 61) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 3 61 [mmFiber30StateAt 0] (mmFiber30StateAt 21) h3

theorem mmFiber30State22_in_close :
    mmFiber30StateAt 22 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 1 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 1) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep1
  have h2 : mmFiber30StateAt 6 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 1) (mmFiber30StateAt 6) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep6
  have h3 : mmFiber30StateAt 22 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 6) (mmFiber30StateAt 22) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep22
  change mmFiber30StateAt 22 ∈ closeChainFiber mmWord mmFiber30DirectStates (3 + 61) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 3 61 [mmFiber30StateAt 0] (mmFiber30StateAt 22) h3

theorem mmFiber30State23_in_close :
    mmFiber30StateAt 23 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 7 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 7) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep7
  have h2 : mmFiber30StateAt 23 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 7) (mmFiber30StateAt 23) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep23
  change mmFiber30StateAt 23 ∈ closeChainFiber mmWord mmFiber30DirectStates (2 + 62) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 2 62 [mmFiber30StateAt 0] (mmFiber30StateAt 23) h2

theorem mmFiber30State24_in_close :
    mmFiber30StateAt 24 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 8 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 8) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep8
  have h2 : mmFiber30StateAt 24 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 8) (mmFiber30StateAt 24) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep24
  change mmFiber30StateAt 24 ∈ closeChainFiber mmWord mmFiber30DirectStates (2 + 62) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 2 62 [mmFiber30StateAt 0] (mmFiber30StateAt 24) h2

theorem mmFiber30State25_in_close :
    mmFiber30StateAt 25 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 1 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 1) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep1
  have h2 : mmFiber30StateAt 9 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 1) (mmFiber30StateAt 9) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep9
  have h3 : mmFiber30StateAt 25 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 9) (mmFiber30StateAt 25) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep25
  change mmFiber30StateAt 25 ∈ closeChainFiber mmWord mmFiber30DirectStates (3 + 61) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 3 61 [mmFiber30StateAt 0] (mmFiber30StateAt 25) h3

theorem mmFiber30State26_in_close :
    mmFiber30StateAt 26 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 2 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 2) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep2
  have h2 : mmFiber30StateAt 10 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 2) (mmFiber30StateAt 10) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep10
  have h3 : mmFiber30StateAt 26 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 10) (mmFiber30StateAt 26) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep26
  change mmFiber30StateAt 26 ∈ closeChainFiber mmWord mmFiber30DirectStates (3 + 61) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 3 61 [mmFiber30StateAt 0] (mmFiber30StateAt 26) h3

theorem mmFiber30State27_in_close :
    mmFiber30StateAt 27 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 1 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 1) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep1
  have h2 : mmFiber30StateAt 3 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 1) (mmFiber30StateAt 3) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep3
  have h3 : mmFiber30StateAt 11 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 3) (mmFiber30StateAt 11) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep11
  have h4 : mmFiber30StateAt 27 ∈ closeChainFiber mmWord mmFiber30DirectStates 4 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0]
      (mmFiber30StateAt 11) (mmFiber30StateAt 27) (by decide) h3 (by decide)
      mmFiber30ReverseSingleStep27
  change mmFiber30StateAt 27 ∈ closeChainFiber mmWord mmFiber30DirectStates (4 + 60) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 4 60 [mmFiber30StateAt 0] (mmFiber30StateAt 27) h4

theorem mmFiber30State28_in_close :
    mmFiber30StateAt 28 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 8 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 8) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep8
  have h2 : mmFiber30StateAt 24 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 8) (mmFiber30StateAt 24) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep24
  have h3 : mmFiber30StateAt 28 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 24) (mmFiber30StateAt 28) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep28
  change mmFiber30StateAt 28 ∈ closeChainFiber mmWord mmFiber30DirectStates (3 + 61) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 3 61 [mmFiber30StateAt 0] (mmFiber30StateAt 28) h3

theorem mmFiber30State29_in_close :
    mmFiber30StateAt 29 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 1 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 1) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep1
  have h2 : mmFiber30StateAt 9 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 1) (mmFiber30StateAt 9) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep9
  have h3 : mmFiber30StateAt 25 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 9) (mmFiber30StateAt 25) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep25
  have h4 : mmFiber30StateAt 29 ∈ closeChainFiber mmWord mmFiber30DirectStates 4 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0]
      (mmFiber30StateAt 25) (mmFiber30StateAt 29) (by decide) h3 (by decide)
      mmFiber30ReverseSingleStep29
  change mmFiber30StateAt 29 ∈ closeChainFiber mmWord mmFiber30DirectStates (4 + 60) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 4 60 [mmFiber30StateAt 0] (mmFiber30StateAt 29) h4

theorem mmFiber30State30_in_close :
    mmFiber30StateAt 30 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 1 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 1) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep1
  have h2 : mmFiber30StateAt 6 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 1) (mmFiber30StateAt 6) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep6
  have h3 : mmFiber30StateAt 14 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 6) (mmFiber30StateAt 14) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep14
  have h4 : mmFiber30StateAt 30 ∈ closeChainFiber mmWord mmFiber30DirectStates 4 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0]
      (mmFiber30StateAt 14) (mmFiber30StateAt 30) (by decide) h3 (by decide)
      mmFiber30ReverseSingleStep30
  change mmFiber30StateAt 30 ∈ closeChainFiber mmWord mmFiber30DirectStates (4 + 60) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 4 60 [mmFiber30StateAt 0] (mmFiber30StateAt 30) h4

theorem mmFiber30State31_in_close :
    mmFiber30StateAt 31 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 7 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 7) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep7
  have h2 : mmFiber30StateAt 15 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 7) (mmFiber30StateAt 15) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep15
  have h3 : mmFiber30StateAt 31 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 15) (mmFiber30StateAt 31) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep31
  change mmFiber30StateAt 31 ∈ closeChainFiber mmWord mmFiber30DirectStates (3 + 61) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 3 61 [mmFiber30StateAt 0] (mmFiber30StateAt 31) h3

theorem mmFiber30State32_in_close :
    mmFiber30StateAt 32 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 8 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 8) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep8
  have h2 : mmFiber30StateAt 48 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 8) (mmFiber30StateAt 48) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep48
  have h3 : mmFiber30StateAt 32 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 48) (mmFiber30StateAt 32) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep32
  change mmFiber30StateAt 32 ∈ closeChainFiber mmWord mmFiber30DirectStates (3 + 61) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 3 61 [mmFiber30StateAt 0] (mmFiber30StateAt 32) h3

theorem mmFiber30State33_in_close :
    mmFiber30StateAt 33 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 1 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 1) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep1
  have h2 : mmFiber30StateAt 9 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 1) (mmFiber30StateAt 9) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep9
  have h3 : mmFiber30StateAt 49 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 9) (mmFiber30StateAt 49) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep49
  have h4 : mmFiber30StateAt 33 ∈ closeChainFiber mmWord mmFiber30DirectStates 4 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0]
      (mmFiber30StateAt 49) (mmFiber30StateAt 33) (by decide) h3 (by decide)
      mmFiber30ReverseSingleStep33
  change mmFiber30StateAt 33 ∈ closeChainFiber mmWord mmFiber30DirectStates (4 + 60) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 4 60 [mmFiber30StateAt 0] (mmFiber30StateAt 33) h4

theorem mmFiber30State34_in_close :
    mmFiber30StateAt 34 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 1 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 1) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep1
  have h2 : mmFiber30StateAt 6 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 1) (mmFiber30StateAt 6) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep6
  have h3 : mmFiber30StateAt 22 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 6) (mmFiber30StateAt 22) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep22
  have h4 : mmFiber30StateAt 34 ∈ closeChainFiber mmWord mmFiber30DirectStates 4 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0]
      (mmFiber30StateAt 22) (mmFiber30StateAt 34) (by decide) h3 (by decide)
      mmFiber30ReverseSingleStep34
  change mmFiber30StateAt 34 ∈ closeChainFiber mmWord mmFiber30DirectStates (4 + 60) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 4 60 [mmFiber30StateAt 0] (mmFiber30StateAt 34) h4

theorem mmFiber30State35_in_close :
    mmFiber30StateAt 35 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 7 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 7) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep7
  have h2 : mmFiber30StateAt 23 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 7) (mmFiber30StateAt 23) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep23
  have h3 : mmFiber30StateAt 35 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 23) (mmFiber30StateAt 35) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep35
  change mmFiber30StateAt 35 ∈ closeChainFiber mmWord mmFiber30DirectStates (3 + 61) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 3 61 [mmFiber30StateAt 0] (mmFiber30StateAt 35) h3

theorem mmFiber30State36_in_close :
    mmFiber30StateAt 36 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 2 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 2) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep2
  have h2 : mmFiber30StateAt 18 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 2) (mmFiber30StateAt 18) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep18
  have h3 : mmFiber30StateAt 36 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 18) (mmFiber30StateAt 36) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep36
  change mmFiber30StateAt 36 ∈ closeChainFiber mmWord mmFiber30DirectStates (3 + 61) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 3 61 [mmFiber30StateAt 0] (mmFiber30StateAt 36) h3

theorem mmFiber30State37_in_close :
    mmFiber30StateAt 37 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 16 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 16) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep16
  have h2 : mmFiber30StateAt 39 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 16) (mmFiber30StateAt 39) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep39
  have h3 : mmFiber30StateAt 37 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 39) (mmFiber30StateAt 37) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep37
  change mmFiber30StateAt 37 ∈ closeChainFiber mmWord mmFiber30DirectStates (3 + 61) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 3 61 [mmFiber30StateAt 0] (mmFiber30StateAt 37) h3

theorem mmFiber30State38_in_close :
    mmFiber30StateAt 38 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 1 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 1) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep1
  have h2 : mmFiber30StateAt 17 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 1) (mmFiber30StateAt 17) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep17
  have h3 : mmFiber30StateAt 38 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 17) (mmFiber30StateAt 38) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep38
  change mmFiber30StateAt 38 ∈ closeChainFiber mmWord mmFiber30DirectStates (3 + 61) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 3 61 [mmFiber30StateAt 0] (mmFiber30StateAt 38) h3

theorem mmFiber30State39_in_close :
    mmFiber30StateAt 39 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 16 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 16) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep16
  have h2 : mmFiber30StateAt 39 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 16) (mmFiber30StateAt 39) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep39
  change mmFiber30StateAt 39 ∈ closeChainFiber mmWord mmFiber30DirectStates (2 + 62) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 2 62 [mmFiber30StateAt 0] (mmFiber30StateAt 39) h2

theorem mmFiber30State40_in_close :
    mmFiber30StateAt 40 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 56 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 56) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep56
  have h2 : mmFiber30StateAt 40 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 56) (mmFiber30StateAt 40) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep40
  change mmFiber30StateAt 40 ∈ closeChainFiber mmWord mmFiber30DirectStates (2 + 62) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 2 62 [mmFiber30StateAt 0] (mmFiber30StateAt 40) h2

theorem mmFiber30State41_in_close :
    mmFiber30StateAt 41 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 1 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 1) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep1
  have h2 : mmFiber30StateAt 57 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 1) (mmFiber30StateAt 57) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep57
  have h3 : mmFiber30StateAt 41 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 57) (mmFiber30StateAt 41) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep41
  change mmFiber30StateAt 41 ∈ closeChainFiber mmWord mmFiber30DirectStates (3 + 61) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 3 61 [mmFiber30StateAt 0] (mmFiber30StateAt 41) h3

theorem mmFiber30State42_in_close :
    mmFiber30StateAt 42 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 2 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 2) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep2
  have h2 : mmFiber30StateAt 58 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 2) (mmFiber30StateAt 58) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep58
  have h3 : mmFiber30StateAt 42 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 58) (mmFiber30StateAt 42) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep42
  change mmFiber30StateAt 42 ∈ closeChainFiber mmWord mmFiber30DirectStates (3 + 61) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 3 61 [mmFiber30StateAt 0] (mmFiber30StateAt 42) h3

theorem mmFiber30State43_in_close :
    mmFiber30StateAt 43 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 56 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 56) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep56
  have h2 : mmFiber30StateAt 40 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 56) (mmFiber30StateAt 40) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep40
  have h3 : mmFiber30StateAt 43 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 40) (mmFiber30StateAt 43) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep43
  change mmFiber30StateAt 43 ∈ closeChainFiber mmWord mmFiber30DirectStates (3 + 61) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 3 61 [mmFiber30StateAt 0] (mmFiber30StateAt 43) h3

theorem mmFiber30State44_in_close :
    mmFiber30StateAt 44 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 56 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 56) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep56
  have h2 : mmFiber30StateAt 40 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 56) (mmFiber30StateAt 40) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep40
  have h3 : mmFiber30StateAt 44 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 40) (mmFiber30StateAt 44) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep44
  change mmFiber30StateAt 44 ∈ closeChainFiber mmWord mmFiber30DirectStates (3 + 61) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 3 61 [mmFiber30StateAt 0] (mmFiber30StateAt 44) h3

theorem mmFiber30State45_in_close :
    mmFiber30StateAt 45 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 1 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 1) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep1
  have h2 : mmFiber30StateAt 57 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 1) (mmFiber30StateAt 57) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep57
  have h3 : mmFiber30StateAt 41 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 57) (mmFiber30StateAt 41) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep41
  have h4 : mmFiber30StateAt 45 ∈ closeChainFiber mmWord mmFiber30DirectStates 4 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0]
      (mmFiber30StateAt 41) (mmFiber30StateAt 45) (by decide) h3 (by decide)
      mmFiber30ReverseSingleStep45
  change mmFiber30StateAt 45 ∈ closeChainFiber mmWord mmFiber30DirectStates (4 + 60) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 4 60 [mmFiber30StateAt 0] (mmFiber30StateAt 45) h4

theorem mmFiber30State46_in_close :
    mmFiber30StateAt 46 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 1 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 1) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep1
  have h2 : mmFiber30StateAt 6 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 1) (mmFiber30StateAt 6) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep6
  have h3 : mmFiber30StateAt 62 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 6) (mmFiber30StateAt 62) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep62
  have h4 : mmFiber30StateAt 46 ∈ closeChainFiber mmWord mmFiber30DirectStates 4 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0]
      (mmFiber30StateAt 62) (mmFiber30StateAt 46) (by decide) h3 (by decide)
      mmFiber30ReverseSingleStep46
  change mmFiber30StateAt 46 ∈ closeChainFiber mmWord mmFiber30DirectStates (4 + 60) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 4 60 [mmFiber30StateAt 0] (mmFiber30StateAt 46) h4

theorem mmFiber30State47_in_close :
    mmFiber30StateAt 47 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 7 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 7) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep7
  have h2 : mmFiber30StateAt 63 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 7) (mmFiber30StateAt 63) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep63
  have h3 : mmFiber30StateAt 47 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 63) (mmFiber30StateAt 47) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep47
  change mmFiber30StateAt 47 ∈ closeChainFiber mmWord mmFiber30DirectStates (3 + 61) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 3 61 [mmFiber30StateAt 0] (mmFiber30StateAt 47) h3

theorem mmFiber30State48_in_close :
    mmFiber30StateAt 48 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 8 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 8) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep8
  have h2 : mmFiber30StateAt 48 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 8) (mmFiber30StateAt 48) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep48
  change mmFiber30StateAt 48 ∈ closeChainFiber mmWord mmFiber30DirectStates (2 + 62) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 2 62 [mmFiber30StateAt 0] (mmFiber30StateAt 48) h2

theorem mmFiber30State49_in_close :
    mmFiber30StateAt 49 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 1 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 1) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep1
  have h2 : mmFiber30StateAt 9 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 1) (mmFiber30StateAt 9) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep9
  have h3 : mmFiber30StateAt 49 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 9) (mmFiber30StateAt 49) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep49
  change mmFiber30StateAt 49 ∈ closeChainFiber mmWord mmFiber30DirectStates (3 + 61) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 3 61 [mmFiber30StateAt 0] (mmFiber30StateAt 49) h3

theorem mmFiber30State50_in_close :
    mmFiber30StateAt 50 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 2 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 2) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep2
  have h2 : mmFiber30StateAt 10 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 2) (mmFiber30StateAt 10) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep10
  have h3 : mmFiber30StateAt 50 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 10) (mmFiber30StateAt 50) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep50
  change mmFiber30StateAt 50 ∈ closeChainFiber mmWord mmFiber30DirectStates (3 + 61) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 3 61 [mmFiber30StateAt 0] (mmFiber30StateAt 50) h3

theorem mmFiber30State51_in_close :
    mmFiber30StateAt 51 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 1 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 1) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep1
  have h2 : mmFiber30StateAt 3 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 1) (mmFiber30StateAt 3) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep3
  have h3 : mmFiber30StateAt 11 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 3) (mmFiber30StateAt 11) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep11
  have h4 : mmFiber30StateAt 51 ∈ closeChainFiber mmWord mmFiber30DirectStates 4 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0]
      (mmFiber30StateAt 11) (mmFiber30StateAt 51) (by decide) h3 (by decide)
      mmFiber30ReverseSingleStep51
  change mmFiber30StateAt 51 ∈ closeChainFiber mmWord mmFiber30DirectStates (4 + 60) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 4 60 [mmFiber30StateAt 0] (mmFiber30StateAt 51) h4

theorem mmFiber30State52_in_close :
    mmFiber30StateAt 52 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 2 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 2) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep2
  have h2 : mmFiber30StateAt 4 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 2) (mmFiber30StateAt 4) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep4
  have h3 : mmFiber30StateAt 12 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 4) (mmFiber30StateAt 12) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep12
  have h4 : mmFiber30StateAt 52 ∈ closeChainFiber mmWord mmFiber30DirectStates 4 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0]
      (mmFiber30StateAt 12) (mmFiber30StateAt 52) (by decide) h3 (by decide)
      mmFiber30ReverseSingleStep52
  change mmFiber30StateAt 52 ∈ closeChainFiber mmWord mmFiber30DirectStates (4 + 60) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 4 60 [mmFiber30StateAt 0] (mmFiber30StateAt 52) h4

theorem mmFiber30State53_in_close :
    mmFiber30StateAt 53 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 7 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 7) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep7
  have h2 : mmFiber30StateAt 5 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 7) (mmFiber30StateAt 5) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep5
  have h3 : mmFiber30StateAt 13 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 5) (mmFiber30StateAt 13) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep13
  have h4 : mmFiber30StateAt 53 ∈ closeChainFiber mmWord mmFiber30DirectStates 4 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0]
      (mmFiber30StateAt 13) (mmFiber30StateAt 53) (by decide) h3 (by decide)
      mmFiber30ReverseSingleStep53
  change mmFiber30StateAt 53 ∈ closeChainFiber mmWord mmFiber30DirectStates (4 + 60) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 4 60 [mmFiber30StateAt 0] (mmFiber30StateAt 53) h4

theorem mmFiber30State54_in_close :
    mmFiber30StateAt 54 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 1 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 1) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep1
  have h2 : mmFiber30StateAt 6 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 1) (mmFiber30StateAt 6) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep6
  have h3 : mmFiber30StateAt 14 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 6) (mmFiber30StateAt 14) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep14
  have h4 : mmFiber30StateAt 54 ∈ closeChainFiber mmWord mmFiber30DirectStates 4 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0]
      (mmFiber30StateAt 14) (mmFiber30StateAt 54) (by decide) h3 (by decide)
      mmFiber30ReverseSingleStep54
  change mmFiber30StateAt 54 ∈ closeChainFiber mmWord mmFiber30DirectStates (4 + 60) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 4 60 [mmFiber30StateAt 0] (mmFiber30StateAt 54) h4

theorem mmFiber30State55_in_close :
    mmFiber30StateAt 55 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 7 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 7) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep7
  have h2 : mmFiber30StateAt 15 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 7) (mmFiber30StateAt 15) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep15
  have h3 : mmFiber30StateAt 55 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 15) (mmFiber30StateAt 55) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep55
  change mmFiber30StateAt 55 ∈ closeChainFiber mmWord mmFiber30DirectStates (3 + 61) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 3 61 [mmFiber30StateAt 0] (mmFiber30StateAt 55) h3

theorem mmFiber30State56_in_close :
    mmFiber30StateAt 56 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 56 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 56) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep56
  change mmFiber30StateAt 56 ∈ closeChainFiber mmWord mmFiber30DirectStates (1 + 63) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 1 63 [mmFiber30StateAt 0] (mmFiber30StateAt 56) h1

theorem mmFiber30State57_in_close :
    mmFiber30StateAt 57 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 1 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 1) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep1
  have h2 : mmFiber30StateAt 57 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 1) (mmFiber30StateAt 57) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep57
  change mmFiber30StateAt 57 ∈ closeChainFiber mmWord mmFiber30DirectStates (2 + 62) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 2 62 [mmFiber30StateAt 0] (mmFiber30StateAt 57) h2

theorem mmFiber30State58_in_close :
    mmFiber30StateAt 58 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 2 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 2) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep2
  have h2 : mmFiber30StateAt 58 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 2) (mmFiber30StateAt 58) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep58
  change mmFiber30StateAt 58 ∈ closeChainFiber mmWord mmFiber30DirectStates (2 + 62) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 2 62 [mmFiber30StateAt 0] (mmFiber30StateAt 58) h2

theorem mmFiber30State59_in_close :
    mmFiber30StateAt 59 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 1 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 1) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep1
  have h2 : mmFiber30StateAt 3 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 1) (mmFiber30StateAt 3) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep3
  have h3 : mmFiber30StateAt 59 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 3) (mmFiber30StateAt 59) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep59
  change mmFiber30StateAt 59 ∈ closeChainFiber mmWord mmFiber30DirectStates (3 + 61) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 3 61 [mmFiber30StateAt 0] (mmFiber30StateAt 59) h3

theorem mmFiber30State60_in_close :
    mmFiber30StateAt 60 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 2 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 2) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep2
  have h2 : mmFiber30StateAt 4 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 2) (mmFiber30StateAt 4) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep4
  have h3 : mmFiber30StateAt 60 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 4) (mmFiber30StateAt 60) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep60
  change mmFiber30StateAt 60 ∈ closeChainFiber mmWord mmFiber30DirectStates (3 + 61) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 3 61 [mmFiber30StateAt 0] (mmFiber30StateAt 60) h3

theorem mmFiber30State61_in_close :
    mmFiber30StateAt 61 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 7 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 7) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep7
  have h2 : mmFiber30StateAt 5 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 7) (mmFiber30StateAt 5) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep5
  have h3 : mmFiber30StateAt 61 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 5) (mmFiber30StateAt 61) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep61
  change mmFiber30StateAt 61 ∈ closeChainFiber mmWord mmFiber30DirectStates (3 + 61) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 3 61 [mmFiber30StateAt 0] (mmFiber30StateAt 61) h3

theorem mmFiber30State62_in_close :
    mmFiber30StateAt 62 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 1 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 1) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep1
  have h2 : mmFiber30StateAt 6 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 1) (mmFiber30StateAt 6) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep6
  have h3 : mmFiber30StateAt 62 ∈ closeChainFiber mmWord mmFiber30DirectStates 3 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0]
      (mmFiber30StateAt 6) (mmFiber30StateAt 62) (by decide) h2 (by decide)
      mmFiber30ReverseSingleStep62
  change mmFiber30StateAt 62 ∈ closeChainFiber mmWord mmFiber30DirectStates (3 + 61) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 3 61 [mmFiber30StateAt 0] (mmFiber30StateAt 62) h3

theorem mmFiber30State63_in_close :
    mmFiber30StateAt 63 ∈ closeChainFiber mmWord mmFiber30DirectStates mmFiber30DirectStates.length [mmFiber30StateAt 0] := by
  have h0 : mmFiber30StateAt 0 ∈ closeChainFiber mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber30StateAt 7 ∈ closeChainFiber mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 0 [mmFiber30StateAt 0]
      (mmFiber30StateAt 0) (mmFiber30StateAt 7) (by decide) h0 (by decide)
      mmFiber30ReverseSingleStep7
  have h2 : mmFiber30StateAt 63 ∈ closeChainFiber mmWord mmFiber30DirectStates 2 [mmFiber30StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber30DirectStates 1 [mmFiber30StateAt 0]
      (mmFiber30StateAt 7) (mmFiber30StateAt 63) (by decide) h1 (by decide)
      mmFiber30ReverseSingleStep63
  change mmFiber30StateAt 63 ∈ closeChainFiber mmWord mmFiber30DirectStates (2 + 62) [mmFiber30StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber30DirectStates 2 62 [mmFiber30StateAt 0] (mmFiber30StateAt 63) h2

theorem mmFiber30DirectConnected :
    chainFiberConnected mmWord mmFiber30DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber30DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber30State0_in_close
  · subst state
    exact mmFiber30State1_in_close
  · subst state
    exact mmFiber30State2_in_close
  · subst state
    exact mmFiber30State3_in_close
  · subst state
    exact mmFiber30State4_in_close
  · subst state
    exact mmFiber30State5_in_close
  · subst state
    exact mmFiber30State6_in_close
  · subst state
    exact mmFiber30State7_in_close
  · subst state
    exact mmFiber30State8_in_close
  · subst state
    exact mmFiber30State9_in_close
  · subst state
    exact mmFiber30State10_in_close
  · subst state
    exact mmFiber30State11_in_close
  · subst state
    exact mmFiber30State12_in_close
  · subst state
    exact mmFiber30State13_in_close
  · subst state
    exact mmFiber30State14_in_close
  · subst state
    exact mmFiber30State15_in_close
  · subst state
    exact mmFiber30State16_in_close
  · subst state
    exact mmFiber30State17_in_close
  · subst state
    exact mmFiber30State18_in_close
  · subst state
    exact mmFiber30State19_in_close
  · subst state
    exact mmFiber30State20_in_close
  · subst state
    exact mmFiber30State21_in_close
  · subst state
    exact mmFiber30State22_in_close
  · subst state
    exact mmFiber30State23_in_close
  · subst state
    exact mmFiber30State24_in_close
  · subst state
    exact mmFiber30State25_in_close
  · subst state
    exact mmFiber30State26_in_close
  · subst state
    exact mmFiber30State27_in_close
  · subst state
    exact mmFiber30State28_in_close
  · subst state
    exact mmFiber30State29_in_close
  · subst state
    exact mmFiber30State30_in_close
  · subst state
    exact mmFiber30State31_in_close
  · subst state
    exact mmFiber30State32_in_close
  · subst state
    exact mmFiber30State33_in_close
  · subst state
    exact mmFiber30State34_in_close
  · subst state
    exact mmFiber30State35_in_close
  · subst state
    exact mmFiber30State36_in_close
  · subst state
    exact mmFiber30State37_in_close
  · subst state
    exact mmFiber30State38_in_close
  · subst state
    exact mmFiber30State39_in_close
  · subst state
    exact mmFiber30State40_in_close
  · subst state
    exact mmFiber30State41_in_close
  · subst state
    exact mmFiber30State42_in_close
  · subst state
    exact mmFiber30State43_in_close
  · subst state
    exact mmFiber30State44_in_close
  · subst state
    exact mmFiber30State45_in_close
  · subst state
    exact mmFiber30State46_in_close
  · subst state
    exact mmFiber30State47_in_close
  · subst state
    exact mmFiber30State48_in_close
  · subst state
    exact mmFiber30State49_in_close
  · subst state
    exact mmFiber30State50_in_close
  · subst state
    exact mmFiber30State51_in_close
  · subst state
    exact mmFiber30State52_in_close
  · subst state
    exact mmFiber30State53_in_close
  · subst state
    exact mmFiber30State54_in_close
  · subst state
    exact mmFiber30State55_in_close
  · subst state
    exact mmFiber30State56_in_close
  · subst state
    exact mmFiber30State57_in_close
  · subst state
    exact mmFiber30State58_in_close
  · subst state
    exact mmFiber30State59_in_close
  · subst state
    exact mmFiber30State60_in_close
  · subst state
    exact mmFiber30State61_in_close
  · subst state
    exact mmFiber30State62_in_close
  · subst state
    exact mmFiber30State63_in_close
  · cases h
end GoertzelLemma818LengthTwoMMBridge

end Mettapedia.GraphTheory.FourColor
