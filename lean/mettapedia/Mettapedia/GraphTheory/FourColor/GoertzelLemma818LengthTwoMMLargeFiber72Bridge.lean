import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for `mirror,mirror` size-64 fiber 72

This module proves direct connectedness for one generated size-64 fiber from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMMBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorMirrorCertificate
open GoertzelLemma818MirrorMirrorReverseAudit

def mmFiber72StateAt (i : Nat) : List TauState :=
  directStates (mmFiber72RowAt i).sourceLeft (mmFiber72RowAt i).sourceRight

def mmFiber72DirectStates : List (List TauState) :=
  [mmFiber72StateAt 0, mmFiber72StateAt 1, mmFiber72StateAt 2, mmFiber72StateAt 3, mmFiber72StateAt 4, mmFiber72StateAt 5, mmFiber72StateAt 6, mmFiber72StateAt 7, mmFiber72StateAt 8, mmFiber72StateAt 9, mmFiber72StateAt 10, mmFiber72StateAt 11, mmFiber72StateAt 12, mmFiber72StateAt 13, mmFiber72StateAt 14, mmFiber72StateAt 15, mmFiber72StateAt 16, mmFiber72StateAt 17, mmFiber72StateAt 18, mmFiber72StateAt 19, mmFiber72StateAt 20, mmFiber72StateAt 21, mmFiber72StateAt 22, mmFiber72StateAt 23, mmFiber72StateAt 24, mmFiber72StateAt 25, mmFiber72StateAt 26, mmFiber72StateAt 27, mmFiber72StateAt 28, mmFiber72StateAt 29, mmFiber72StateAt 30, mmFiber72StateAt 31, mmFiber72StateAt 32, mmFiber72StateAt 33, mmFiber72StateAt 34, mmFiber72StateAt 35, mmFiber72StateAt 36, mmFiber72StateAt 37, mmFiber72StateAt 38, mmFiber72StateAt 39, mmFiber72StateAt 40, mmFiber72StateAt 41, mmFiber72StateAt 42, mmFiber72StateAt 43, mmFiber72StateAt 44, mmFiber72StateAt 45, mmFiber72StateAt 46, mmFiber72StateAt 47, mmFiber72StateAt 48, mmFiber72StateAt 49, mmFiber72StateAt 50, mmFiber72StateAt 51, mmFiber72StateAt 52, mmFiber72StateAt 53, mmFiber72StateAt 54, mmFiber72StateAt 55, mmFiber72StateAt 56, mmFiber72StateAt 57, mmFiber72StateAt 58, mmFiber72StateAt 59, mmFiber72StateAt 60, mmFiber72StateAt 61, mmFiber72StateAt 62, mmFiber72StateAt 63]

theorem mmFiber72ReverseRow_1_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk0_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 0) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 0) (mmFiber72StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 0) (mmFiber72StateAt 1)
    (mmFiber72RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 1) (by decide) mmFiber72ReverseRow_1_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_2_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk1_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 2) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber72ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 1) (mmFiber72StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 1) (mmFiber72StateAt 2)
    (mmFiber72RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 2) (by decide) mmFiber72ReverseRow_2_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_3_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk1_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 2) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 0) (mmFiber72StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 0) (mmFiber72StateAt 3)
    (mmFiber72RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 3) (by decide) mmFiber72ReverseRow_3_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_4_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk2_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 4) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber72ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 0) (mmFiber72StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 0) (mmFiber72StateAt 4)
    (mmFiber72RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 4) (by decide) mmFiber72ReverseRow_4_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_5_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk2_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 4) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 1) (mmFiber72StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 1) (mmFiber72StateAt 5)
    (mmFiber72RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 5) (by decide) mmFiber72ReverseRow_5_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_6_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk3_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 6) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber72ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 4) (mmFiber72StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 4) (mmFiber72StateAt 6)
    (mmFiber72RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 6) (by decide) mmFiber72ReverseRow_6_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_7_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk3_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 6) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 3) (mmFiber72StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 3) (mmFiber72StateAt 7)
    (mmFiber72RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 7) (by decide) mmFiber72ReverseRow_7_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_8_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 8) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk4_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 8) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber72ReverseSingleStep8 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 0) (mmFiber72StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 0) (mmFiber72StateAt 8)
    (mmFiber72RowAt 8).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 8) (by decide) mmFiber72ReverseRow_8_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_9_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 9) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk4_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 8) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep9 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 1) (mmFiber72StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 1) (mmFiber72StateAt 9)
    (mmFiber72RowAt 9).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 9) (by decide) mmFiber72ReverseRow_9_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_10_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 10) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk5_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 10) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber72ReverseSingleStep10 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 2) (mmFiber72StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 2) (mmFiber72StateAt 10)
    (mmFiber72RowAt 10).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 10) (by decide) mmFiber72ReverseRow_10_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_11_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 11) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk5_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 10) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep11 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 3) (mmFiber72StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 3) (mmFiber72StateAt 11)
    (mmFiber72RowAt 11).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 11) (by decide) mmFiber72ReverseRow_11_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_12_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 12) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk6_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 12) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber72ReverseSingleStep12 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 4) (mmFiber72StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 4) (mmFiber72StateAt 12)
    (mmFiber72RowAt 12).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 12) (by decide) mmFiber72ReverseRow_12_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_13_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 13) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk6_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 12) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep13 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 5) (mmFiber72StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 5) (mmFiber72StateAt 13)
    (mmFiber72RowAt 13).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 13) (by decide) mmFiber72ReverseRow_13_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_14_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 14) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk7_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 14) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber72ReverseSingleStep14 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 6) (mmFiber72StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 6) (mmFiber72StateAt 14)
    (mmFiber72RowAt 14).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 14) (by decide) mmFiber72ReverseRow_14_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_15_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 15) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk7_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 14) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep15 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 7) (mmFiber72StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 7) (mmFiber72StateAt 15)
    (mmFiber72RowAt 15).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 15) (by decide) mmFiber72ReverseRow_15_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_16_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 16) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk8_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 16) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber72ReverseSingleStep16 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 20) (mmFiber72StateAt 16) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 20) (mmFiber72StateAt 16)
    (mmFiber72RowAt 16).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 16) (by decide) mmFiber72ReverseRow_16_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_17_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 17) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk8_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 16) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep17 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 21) (mmFiber72StateAt 17) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 21) (mmFiber72StateAt 17)
    (mmFiber72RowAt 17).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 17) (by decide) mmFiber72ReverseRow_17_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_18_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 18) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk9_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 18) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber72ReverseSingleStep18 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 12) (mmFiber72StateAt 18) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 12) (mmFiber72StateAt 18)
    (mmFiber72RowAt 18).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 18) (by decide) mmFiber72ReverseRow_18_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_19_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 19) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk9_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 18) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep19 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 13) (mmFiber72StateAt 19) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 13) (mmFiber72StateAt 19)
    (mmFiber72RowAt 19).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 19) (by decide) mmFiber72ReverseRow_19_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_20_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 20) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk10_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 20) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber72ReverseSingleStep20 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 8) (mmFiber72StateAt 20) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 8) (mmFiber72StateAt 20)
    (mmFiber72RowAt 20).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 20) (by decide) mmFiber72ReverseRow_20_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_21_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 21) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk10_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 20) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep21 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 9) (mmFiber72StateAt 21) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 9) (mmFiber72StateAt 21)
    (mmFiber72RowAt 21).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 21) (by decide) mmFiber72ReverseRow_21_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_22_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 22) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk11_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 22) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber72ReverseSingleStep22 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 10) (mmFiber72StateAt 22) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 10) (mmFiber72StateAt 22)
    (mmFiber72RowAt 22).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 22) (by decide) mmFiber72ReverseRow_22_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_23_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 23) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk11_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 22) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep23 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 11) (mmFiber72StateAt 23) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 11) (mmFiber72StateAt 23)
    (mmFiber72RowAt 23).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 23) (by decide) mmFiber72ReverseRow_23_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_24_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 24) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk12_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 24) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber72ReverseSingleStep24 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 28) (mmFiber72StateAt 24) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 28) (mmFiber72StateAt 24)
    (mmFiber72RowAt 24).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 24) (by decide) mmFiber72ReverseRow_24_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_25_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 25) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk12_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 24) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep25 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 29) (mmFiber72StateAt 25) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 29) (mmFiber72StateAt 25)
    (mmFiber72RowAt 25).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 25) (by decide) mmFiber72ReverseRow_25_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_26_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 26) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk13_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 26) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber72ReverseSingleStep26 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 4) (mmFiber72StateAt 26) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 4) (mmFiber72StateAt 26)
    (mmFiber72RowAt 26).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 26) (by decide) mmFiber72ReverseRow_26_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_27_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 27) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk13_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 26) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep27 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 5) (mmFiber72StateAt 27) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 5) (mmFiber72StateAt 27)
    (mmFiber72RowAt 27).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 27) (by decide) mmFiber72ReverseRow_27_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_28_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 28) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk14_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 28) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber72ReverseSingleStep28 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 0) (mmFiber72StateAt 28) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 0) (mmFiber72StateAt 28)
    (mmFiber72RowAt 28).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 28) (by decide) mmFiber72ReverseRow_28_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_29_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 29) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk14_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 28) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep29 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 1) (mmFiber72StateAt 29) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 1) (mmFiber72StateAt 29)
    (mmFiber72RowAt 29).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 29) (by decide) mmFiber72ReverseRow_29_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_30_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 30) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk15_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 30) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber72ReverseSingleStep30 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 2) (mmFiber72StateAt 30) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 2) (mmFiber72StateAt 30)
    (mmFiber72RowAt 30).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 30) (by decide) mmFiber72ReverseRow_30_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_31_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 31) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk15_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 30) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep31 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 3) (mmFiber72StateAt 31) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 3) (mmFiber72StateAt 31)
    (mmFiber72RowAt 31).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 31) (by decide) mmFiber72ReverseRow_31_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_32_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 32) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk16_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 32) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber72ReverseSingleStep32 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 0) (mmFiber72StateAt 32) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 0) (mmFiber72StateAt 32)
    (mmFiber72RowAt 32).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 32) (by decide) mmFiber72ReverseRow_32_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_33_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 33) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk16_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 32) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep33 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 1) (mmFiber72StateAt 33) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 1) (mmFiber72StateAt 33)
    (mmFiber72RowAt 33).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 33) (by decide) mmFiber72ReverseRow_33_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_34_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 34) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk17_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 34) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber72ReverseSingleStep34 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 2) (mmFiber72StateAt 34) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 2) (mmFiber72StateAt 34)
    (mmFiber72RowAt 34).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 34) (by decide) mmFiber72ReverseRow_34_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_35_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 35) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk17_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 34) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep35 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 3) (mmFiber72StateAt 35) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 3) (mmFiber72StateAt 35)
    (mmFiber72RowAt 35).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 35) (by decide) mmFiber72ReverseRow_35_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_36_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 36) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk18_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 36) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber72ReverseSingleStep36 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 4) (mmFiber72StateAt 36) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 4) (mmFiber72StateAt 36)
    (mmFiber72RowAt 36).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 36) (by decide) mmFiber72ReverseRow_36_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_37_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 37) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk18_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 36) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep37 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 5) (mmFiber72StateAt 37) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 5) (mmFiber72StateAt 37)
    (mmFiber72RowAt 37).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 37) (by decide) mmFiber72ReverseRow_37_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_38_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 38) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk19_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 38) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber72ReverseSingleStep38 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 6) (mmFiber72StateAt 38) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 6) (mmFiber72StateAt 38)
    (mmFiber72RowAt 38).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 38) (by decide) mmFiber72ReverseRow_38_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_39_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 39) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk19_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 38) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep39 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 7) (mmFiber72StateAt 39) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 7) (mmFiber72StateAt 39)
    (mmFiber72RowAt 39).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 39) (by decide) mmFiber72ReverseRow_39_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_40_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 40) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk20_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 40) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber72ReverseSingleStep40 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 8) (mmFiber72StateAt 40) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 8) (mmFiber72StateAt 40)
    (mmFiber72RowAt 40).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 40) (by decide) mmFiber72ReverseRow_40_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_41_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 41) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk20_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 40) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep41 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 9) (mmFiber72StateAt 41) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 9) (mmFiber72StateAt 41)
    (mmFiber72RowAt 41).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 41) (by decide) mmFiber72ReverseRow_41_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_42_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 42) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk21_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 42) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber72ReverseSingleStep42 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 10) (mmFiber72StateAt 42) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 10) (mmFiber72StateAt 42)
    (mmFiber72RowAt 42).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 42) (by decide) mmFiber72ReverseRow_42_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_43_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 43) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk21_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 42) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep43 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 11) (mmFiber72StateAt 43) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 11) (mmFiber72StateAt 43)
    (mmFiber72RowAt 43).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 43) (by decide) mmFiber72ReverseRow_43_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_44_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 44) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk22_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 44) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber72ReverseSingleStep44 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 12) (mmFiber72StateAt 44) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 12) (mmFiber72StateAt 44)
    (mmFiber72RowAt 44).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 44) (by decide) mmFiber72ReverseRow_44_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_45_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 45) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk22_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 44) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep45 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 13) (mmFiber72StateAt 45) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 13) (mmFiber72StateAt 45)
    (mmFiber72RowAt 45).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 45) (by decide) mmFiber72ReverseRow_45_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_46_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 46) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk23_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 46) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber72ReverseSingleStep46 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 14) (mmFiber72StateAt 46) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 14) (mmFiber72StateAt 46)
    (mmFiber72RowAt 46).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 46) (by decide) mmFiber72ReverseRow_46_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_47_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 47) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk23_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 46) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep47 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 15) (mmFiber72StateAt 47) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 15) (mmFiber72StateAt 47)
    (mmFiber72RowAt 47).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 47) (by decide) mmFiber72ReverseRow_47_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_48_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 48) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk24_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 48) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber72ReverseSingleStep48 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 32) (mmFiber72StateAt 48) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 32) (mmFiber72StateAt 48)
    (mmFiber72RowAt 48).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 48) (by decide) mmFiber72ReverseRow_48_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_49_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 49) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk24_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 48) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep49 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 33) (mmFiber72StateAt 49) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 33) (mmFiber72StateAt 49)
    (mmFiber72RowAt 49).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 49) (by decide) mmFiber72ReverseRow_49_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_50_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 50) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk25_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 50) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber72ReverseSingleStep50 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 48) (mmFiber72StateAt 50) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 48) (mmFiber72StateAt 50)
    (mmFiber72RowAt 50).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 50) (by decide) mmFiber72ReverseRow_50_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_51_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 51) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk25_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 50) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep51 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 35) (mmFiber72StateAt 51) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 35) (mmFiber72StateAt 51)
    (mmFiber72RowAt 51).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 51) (by decide) mmFiber72ReverseRow_51_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_52_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 52) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk26_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 52) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber72ReverseSingleStep52 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 36) (mmFiber72StateAt 52) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 36) (mmFiber72StateAt 52)
    (mmFiber72RowAt 52).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 52) (by decide) mmFiber72ReverseRow_52_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_53_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 53) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk26_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 52) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep53 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 37) (mmFiber72StateAt 53) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 37) (mmFiber72StateAt 53)
    (mmFiber72RowAt 53).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 53) (by decide) mmFiber72ReverseRow_53_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_54_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 54) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk27_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 54) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber72ReverseSingleStep54 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 49) (mmFiber72StateAt 54) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 49) (mmFiber72StateAt 54)
    (mmFiber72RowAt 54).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 54) (by decide) mmFiber72ReverseRow_54_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_55_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 55) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk27_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 54) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep55 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 48) (mmFiber72StateAt 55) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 48) (mmFiber72StateAt 55)
    (mmFiber72RowAt 55).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 55) (by decide) mmFiber72ReverseRow_55_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_56_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 56) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk28_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 56) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber72ReverseSingleStep56 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 40) (mmFiber72StateAt 56) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 40) (mmFiber72StateAt 56)
    (mmFiber72RowAt 56).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 56) (by decide) mmFiber72ReverseRow_56_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_57_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 57) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk28_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 56) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep57 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 41) (mmFiber72StateAt 57) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 41) (mmFiber72StateAt 57)
    (mmFiber72RowAt 57).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 57) (by decide) mmFiber72ReverseRow_57_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_58_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 58) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk29_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 58) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber72ReverseSingleStep58 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 26) (mmFiber72StateAt 58) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 26) (mmFiber72StateAt 58)
    (mmFiber72RowAt 58).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 58) (by decide) mmFiber72ReverseRow_58_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_59_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 59) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk29_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 58) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep59 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 27) (mmFiber72StateAt 59) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 27) (mmFiber72StateAt 59)
    (mmFiber72RowAt 59).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 59) (by decide) mmFiber72ReverseRow_59_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_60_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 60) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk30_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 60) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber72ReverseSingleStep60 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 28) (mmFiber72StateAt 60) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 28) (mmFiber72StateAt 60)
    (mmFiber72RowAt 60).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 60) (by decide) mmFiber72ReverseRow_60_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_61_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 61) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk30_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 60) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep61 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 29) (mmFiber72StateAt 61) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 29) (mmFiber72StateAt 61)
    (mmFiber72RowAt 61).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 61) (by decide) mmFiber72ReverseRow_61_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_62_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 62) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk31_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 62) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber72ReverseSingleStep62 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 60) (mmFiber72StateAt 62) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 60) (mmFiber72StateAt 62)
    (mmFiber72RowAt 62).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 62) (by decide) mmFiber72ReverseRow_62_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72ReverseRow_63_ok :
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 63) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber72Chunk31_ok
  change (mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 62) &&
    mmRowReverseValid mmFiber72Key mmFiber72Expected (mmFiber72RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber72ReverseSingleStep63 :
    chainSingleKempeStep mmWord (mmFiber72StateAt 31) (mmFiber72StateAt 63) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber72StateAt 31) (mmFiber72StateAt 63)
    (mmFiber72RowAt 63).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber72Key mmFiber72Expected
        (mmFiber72RowAt 63) (by decide) mmFiber72ReverseRow_63_ok
      simpa [mmFiber72StateAt, mmFiber72RowAt, mmFiber72Rows, listGetD, directRow] using h)

theorem mmFiber72State0_in_close :
    mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  change mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 64 [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 0 64 [mmFiber72StateAt 0] (mmFiber72StateAt 0) (by simp [closeChainFiber])

theorem mmFiber72State1_in_close :
    mmFiber72StateAt 1 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 1 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 1) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep1
  change mmFiber72StateAt 1 ∈ closeChainFiber mmWord mmFiber72DirectStates (1 + 63) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 1 63 [mmFiber72StateAt 0] (mmFiber72StateAt 1) h1

theorem mmFiber72State2_in_close :
    mmFiber72StateAt 2 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 1 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 1) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep1
  have h2 : mmFiber72StateAt 2 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 1) (mmFiber72StateAt 2) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep2
  change mmFiber72StateAt 2 ∈ closeChainFiber mmWord mmFiber72DirectStates (2 + 62) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 2 62 [mmFiber72StateAt 0] (mmFiber72StateAt 2) h2

theorem mmFiber72State3_in_close :
    mmFiber72StateAt 3 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 3 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 3) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep3
  change mmFiber72StateAt 3 ∈ closeChainFiber mmWord mmFiber72DirectStates (1 + 63) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 1 63 [mmFiber72StateAt 0] (mmFiber72StateAt 3) h1

theorem mmFiber72State4_in_close :
    mmFiber72StateAt 4 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 4 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 4) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep4
  change mmFiber72StateAt 4 ∈ closeChainFiber mmWord mmFiber72DirectStates (1 + 63) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 1 63 [mmFiber72StateAt 0] (mmFiber72StateAt 4) h1

theorem mmFiber72State5_in_close :
    mmFiber72StateAt 5 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 1 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 1) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep1
  have h2 : mmFiber72StateAt 5 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 1) (mmFiber72StateAt 5) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep5
  change mmFiber72StateAt 5 ∈ closeChainFiber mmWord mmFiber72DirectStates (2 + 62) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 2 62 [mmFiber72StateAt 0] (mmFiber72StateAt 5) h2

theorem mmFiber72State6_in_close :
    mmFiber72StateAt 6 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 4 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 4) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep4
  have h2 : mmFiber72StateAt 6 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 4) (mmFiber72StateAt 6) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep6
  change mmFiber72StateAt 6 ∈ closeChainFiber mmWord mmFiber72DirectStates (2 + 62) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 2 62 [mmFiber72StateAt 0] (mmFiber72StateAt 6) h2

theorem mmFiber72State7_in_close :
    mmFiber72StateAt 7 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 3 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 3) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep3
  have h2 : mmFiber72StateAt 7 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 3) (mmFiber72StateAt 7) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep7
  change mmFiber72StateAt 7 ∈ closeChainFiber mmWord mmFiber72DirectStates (2 + 62) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 2 62 [mmFiber72StateAt 0] (mmFiber72StateAt 7) h2

theorem mmFiber72State8_in_close :
    mmFiber72StateAt 8 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 8 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 8) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep8
  change mmFiber72StateAt 8 ∈ closeChainFiber mmWord mmFiber72DirectStates (1 + 63) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 1 63 [mmFiber72StateAt 0] (mmFiber72StateAt 8) h1

theorem mmFiber72State9_in_close :
    mmFiber72StateAt 9 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 1 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 1) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep1
  have h2 : mmFiber72StateAt 9 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 1) (mmFiber72StateAt 9) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep9
  change mmFiber72StateAt 9 ∈ closeChainFiber mmWord mmFiber72DirectStates (2 + 62) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 2 62 [mmFiber72StateAt 0] (mmFiber72StateAt 9) h2

theorem mmFiber72State10_in_close :
    mmFiber72StateAt 10 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 1 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 1) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep1
  have h2 : mmFiber72StateAt 2 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 1) (mmFiber72StateAt 2) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep2
  have h3 : mmFiber72StateAt 10 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 2) (mmFiber72StateAt 10) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep10
  change mmFiber72StateAt 10 ∈ closeChainFiber mmWord mmFiber72DirectStates (3 + 61) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 3 61 [mmFiber72StateAt 0] (mmFiber72StateAt 10) h3

theorem mmFiber72State11_in_close :
    mmFiber72StateAt 11 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 3 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 3) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep3
  have h2 : mmFiber72StateAt 11 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 3) (mmFiber72StateAt 11) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep11
  change mmFiber72StateAt 11 ∈ closeChainFiber mmWord mmFiber72DirectStates (2 + 62) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 2 62 [mmFiber72StateAt 0] (mmFiber72StateAt 11) h2

theorem mmFiber72State12_in_close :
    mmFiber72StateAt 12 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 4 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 4) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep4
  have h2 : mmFiber72StateAt 12 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 4) (mmFiber72StateAt 12) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep12
  change mmFiber72StateAt 12 ∈ closeChainFiber mmWord mmFiber72DirectStates (2 + 62) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 2 62 [mmFiber72StateAt 0] (mmFiber72StateAt 12) h2

theorem mmFiber72State13_in_close :
    mmFiber72StateAt 13 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 1 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 1) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep1
  have h2 : mmFiber72StateAt 5 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 1) (mmFiber72StateAt 5) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep5
  have h3 : mmFiber72StateAt 13 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 5) (mmFiber72StateAt 13) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep13
  change mmFiber72StateAt 13 ∈ closeChainFiber mmWord mmFiber72DirectStates (3 + 61) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 3 61 [mmFiber72StateAt 0] (mmFiber72StateAt 13) h3

theorem mmFiber72State14_in_close :
    mmFiber72StateAt 14 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 4 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 4) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep4
  have h2 : mmFiber72StateAt 6 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 4) (mmFiber72StateAt 6) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep6
  have h3 : mmFiber72StateAt 14 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 6) (mmFiber72StateAt 14) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep14
  change mmFiber72StateAt 14 ∈ closeChainFiber mmWord mmFiber72DirectStates (3 + 61) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 3 61 [mmFiber72StateAt 0] (mmFiber72StateAt 14) h3

theorem mmFiber72State15_in_close :
    mmFiber72StateAt 15 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 3 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 3) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep3
  have h2 : mmFiber72StateAt 7 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 3) (mmFiber72StateAt 7) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep7
  have h3 : mmFiber72StateAt 15 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 7) (mmFiber72StateAt 15) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep15
  change mmFiber72StateAt 15 ∈ closeChainFiber mmWord mmFiber72DirectStates (3 + 61) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 3 61 [mmFiber72StateAt 0] (mmFiber72StateAt 15) h3

theorem mmFiber72State16_in_close :
    mmFiber72StateAt 16 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 8 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 8) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep8
  have h2 : mmFiber72StateAt 20 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 8) (mmFiber72StateAt 20) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep20
  have h3 : mmFiber72StateAt 16 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 20) (mmFiber72StateAt 16) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep16
  change mmFiber72StateAt 16 ∈ closeChainFiber mmWord mmFiber72DirectStates (3 + 61) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 3 61 [mmFiber72StateAt 0] (mmFiber72StateAt 16) h3

theorem mmFiber72State17_in_close :
    mmFiber72StateAt 17 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 1 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 1) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep1
  have h2 : mmFiber72StateAt 9 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 1) (mmFiber72StateAt 9) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep9
  have h3 : mmFiber72StateAt 21 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 9) (mmFiber72StateAt 21) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep21
  have h4 : mmFiber72StateAt 17 ∈ closeChainFiber mmWord mmFiber72DirectStates 4 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0]
      (mmFiber72StateAt 21) (mmFiber72StateAt 17) (by decide) h3 (by decide)
      mmFiber72ReverseSingleStep17
  change mmFiber72StateAt 17 ∈ closeChainFiber mmWord mmFiber72DirectStates (4 + 60) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 4 60 [mmFiber72StateAt 0] (mmFiber72StateAt 17) h4

theorem mmFiber72State18_in_close :
    mmFiber72StateAt 18 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 4 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 4) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep4
  have h2 : mmFiber72StateAt 12 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 4) (mmFiber72StateAt 12) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep12
  have h3 : mmFiber72StateAt 18 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 12) (mmFiber72StateAt 18) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep18
  change mmFiber72StateAt 18 ∈ closeChainFiber mmWord mmFiber72DirectStates (3 + 61) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 3 61 [mmFiber72StateAt 0] (mmFiber72StateAt 18) h3

theorem mmFiber72State19_in_close :
    mmFiber72StateAt 19 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 1 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 1) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep1
  have h2 : mmFiber72StateAt 5 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 1) (mmFiber72StateAt 5) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep5
  have h3 : mmFiber72StateAt 13 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 5) (mmFiber72StateAt 13) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep13
  have h4 : mmFiber72StateAt 19 ∈ closeChainFiber mmWord mmFiber72DirectStates 4 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0]
      (mmFiber72StateAt 13) (mmFiber72StateAt 19) (by decide) h3 (by decide)
      mmFiber72ReverseSingleStep19
  change mmFiber72StateAt 19 ∈ closeChainFiber mmWord mmFiber72DirectStates (4 + 60) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 4 60 [mmFiber72StateAt 0] (mmFiber72StateAt 19) h4

theorem mmFiber72State20_in_close :
    mmFiber72StateAt 20 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 8 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 8) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep8
  have h2 : mmFiber72StateAt 20 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 8) (mmFiber72StateAt 20) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep20
  change mmFiber72StateAt 20 ∈ closeChainFiber mmWord mmFiber72DirectStates (2 + 62) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 2 62 [mmFiber72StateAt 0] (mmFiber72StateAt 20) h2

theorem mmFiber72State21_in_close :
    mmFiber72StateAt 21 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 1 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 1) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep1
  have h2 : mmFiber72StateAt 9 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 1) (mmFiber72StateAt 9) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep9
  have h3 : mmFiber72StateAt 21 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 9) (mmFiber72StateAt 21) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep21
  change mmFiber72StateAt 21 ∈ closeChainFiber mmWord mmFiber72DirectStates (3 + 61) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 3 61 [mmFiber72StateAt 0] (mmFiber72StateAt 21) h3

theorem mmFiber72State22_in_close :
    mmFiber72StateAt 22 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 1 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 1) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep1
  have h2 : mmFiber72StateAt 2 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 1) (mmFiber72StateAt 2) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep2
  have h3 : mmFiber72StateAt 10 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 2) (mmFiber72StateAt 10) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep10
  have h4 : mmFiber72StateAt 22 ∈ closeChainFiber mmWord mmFiber72DirectStates 4 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0]
      (mmFiber72StateAt 10) (mmFiber72StateAt 22) (by decide) h3 (by decide)
      mmFiber72ReverseSingleStep22
  change mmFiber72StateAt 22 ∈ closeChainFiber mmWord mmFiber72DirectStates (4 + 60) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 4 60 [mmFiber72StateAt 0] (mmFiber72StateAt 22) h4

theorem mmFiber72State23_in_close :
    mmFiber72StateAt 23 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 3 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 3) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep3
  have h2 : mmFiber72StateAt 11 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 3) (mmFiber72StateAt 11) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep11
  have h3 : mmFiber72StateAt 23 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 11) (mmFiber72StateAt 23) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep23
  change mmFiber72StateAt 23 ∈ closeChainFiber mmWord mmFiber72DirectStates (3 + 61) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 3 61 [mmFiber72StateAt 0] (mmFiber72StateAt 23) h3

theorem mmFiber72State24_in_close :
    mmFiber72StateAt 24 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 28 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 28) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep28
  have h2 : mmFiber72StateAt 24 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 28) (mmFiber72StateAt 24) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep24
  change mmFiber72StateAt 24 ∈ closeChainFiber mmWord mmFiber72DirectStates (2 + 62) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 2 62 [mmFiber72StateAt 0] (mmFiber72StateAt 24) h2

theorem mmFiber72State25_in_close :
    mmFiber72StateAt 25 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 1 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 1) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep1
  have h2 : mmFiber72StateAt 29 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 1) (mmFiber72StateAt 29) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep29
  have h3 : mmFiber72StateAt 25 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 29) (mmFiber72StateAt 25) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep25
  change mmFiber72StateAt 25 ∈ closeChainFiber mmWord mmFiber72DirectStates (3 + 61) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 3 61 [mmFiber72StateAt 0] (mmFiber72StateAt 25) h3

theorem mmFiber72State26_in_close :
    mmFiber72StateAt 26 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 4 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 4) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep4
  have h2 : mmFiber72StateAt 26 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 4) (mmFiber72StateAt 26) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep26
  change mmFiber72StateAt 26 ∈ closeChainFiber mmWord mmFiber72DirectStates (2 + 62) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 2 62 [mmFiber72StateAt 0] (mmFiber72StateAt 26) h2

theorem mmFiber72State27_in_close :
    mmFiber72StateAt 27 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 1 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 1) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep1
  have h2 : mmFiber72StateAt 5 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 1) (mmFiber72StateAt 5) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep5
  have h3 : mmFiber72StateAt 27 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 5) (mmFiber72StateAt 27) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep27
  change mmFiber72StateAt 27 ∈ closeChainFiber mmWord mmFiber72DirectStates (3 + 61) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 3 61 [mmFiber72StateAt 0] (mmFiber72StateAt 27) h3

theorem mmFiber72State28_in_close :
    mmFiber72StateAt 28 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 28 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 28) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep28
  change mmFiber72StateAt 28 ∈ closeChainFiber mmWord mmFiber72DirectStates (1 + 63) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 1 63 [mmFiber72StateAt 0] (mmFiber72StateAt 28) h1

theorem mmFiber72State29_in_close :
    mmFiber72StateAt 29 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 1 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 1) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep1
  have h2 : mmFiber72StateAt 29 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 1) (mmFiber72StateAt 29) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep29
  change mmFiber72StateAt 29 ∈ closeChainFiber mmWord mmFiber72DirectStates (2 + 62) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 2 62 [mmFiber72StateAt 0] (mmFiber72StateAt 29) h2

theorem mmFiber72State30_in_close :
    mmFiber72StateAt 30 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 1 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 1) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep1
  have h2 : mmFiber72StateAt 2 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 1) (mmFiber72StateAt 2) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep2
  have h3 : mmFiber72StateAt 30 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 2) (mmFiber72StateAt 30) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep30
  change mmFiber72StateAt 30 ∈ closeChainFiber mmWord mmFiber72DirectStates (3 + 61) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 3 61 [mmFiber72StateAt 0] (mmFiber72StateAt 30) h3

theorem mmFiber72State31_in_close :
    mmFiber72StateAt 31 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 3 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 3) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep3
  have h2 : mmFiber72StateAt 31 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 3) (mmFiber72StateAt 31) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep31
  change mmFiber72StateAt 31 ∈ closeChainFiber mmWord mmFiber72DirectStates (2 + 62) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 2 62 [mmFiber72StateAt 0] (mmFiber72StateAt 31) h2

theorem mmFiber72State32_in_close :
    mmFiber72StateAt 32 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 32 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 32) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep32
  change mmFiber72StateAt 32 ∈ closeChainFiber mmWord mmFiber72DirectStates (1 + 63) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 1 63 [mmFiber72StateAt 0] (mmFiber72StateAt 32) h1

theorem mmFiber72State33_in_close :
    mmFiber72StateAt 33 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 1 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 1) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep1
  have h2 : mmFiber72StateAt 33 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 1) (mmFiber72StateAt 33) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep33
  change mmFiber72StateAt 33 ∈ closeChainFiber mmWord mmFiber72DirectStates (2 + 62) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 2 62 [mmFiber72StateAt 0] (mmFiber72StateAt 33) h2

theorem mmFiber72State34_in_close :
    mmFiber72StateAt 34 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 1 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 1) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep1
  have h2 : mmFiber72StateAt 2 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 1) (mmFiber72StateAt 2) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep2
  have h3 : mmFiber72StateAt 34 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 2) (mmFiber72StateAt 34) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep34
  change mmFiber72StateAt 34 ∈ closeChainFiber mmWord mmFiber72DirectStates (3 + 61) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 3 61 [mmFiber72StateAt 0] (mmFiber72StateAt 34) h3

theorem mmFiber72State35_in_close :
    mmFiber72StateAt 35 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 3 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 3) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep3
  have h2 : mmFiber72StateAt 35 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 3) (mmFiber72StateAt 35) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep35
  change mmFiber72StateAt 35 ∈ closeChainFiber mmWord mmFiber72DirectStates (2 + 62) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 2 62 [mmFiber72StateAt 0] (mmFiber72StateAt 35) h2

theorem mmFiber72State36_in_close :
    mmFiber72StateAt 36 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 4 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 4) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep4
  have h2 : mmFiber72StateAt 36 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 4) (mmFiber72StateAt 36) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep36
  change mmFiber72StateAt 36 ∈ closeChainFiber mmWord mmFiber72DirectStates (2 + 62) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 2 62 [mmFiber72StateAt 0] (mmFiber72StateAt 36) h2

theorem mmFiber72State37_in_close :
    mmFiber72StateAt 37 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 1 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 1) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep1
  have h2 : mmFiber72StateAt 5 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 1) (mmFiber72StateAt 5) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep5
  have h3 : mmFiber72StateAt 37 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 5) (mmFiber72StateAt 37) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep37
  change mmFiber72StateAt 37 ∈ closeChainFiber mmWord mmFiber72DirectStates (3 + 61) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 3 61 [mmFiber72StateAt 0] (mmFiber72StateAt 37) h3

theorem mmFiber72State38_in_close :
    mmFiber72StateAt 38 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 4 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 4) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep4
  have h2 : mmFiber72StateAt 6 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 4) (mmFiber72StateAt 6) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep6
  have h3 : mmFiber72StateAt 38 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 6) (mmFiber72StateAt 38) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep38
  change mmFiber72StateAt 38 ∈ closeChainFiber mmWord mmFiber72DirectStates (3 + 61) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 3 61 [mmFiber72StateAt 0] (mmFiber72StateAt 38) h3

theorem mmFiber72State39_in_close :
    mmFiber72StateAt 39 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 3 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 3) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep3
  have h2 : mmFiber72StateAt 7 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 3) (mmFiber72StateAt 7) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep7
  have h3 : mmFiber72StateAt 39 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 7) (mmFiber72StateAt 39) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep39
  change mmFiber72StateAt 39 ∈ closeChainFiber mmWord mmFiber72DirectStates (3 + 61) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 3 61 [mmFiber72StateAt 0] (mmFiber72StateAt 39) h3

theorem mmFiber72State40_in_close :
    mmFiber72StateAt 40 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 8 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 8) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep8
  have h2 : mmFiber72StateAt 40 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 8) (mmFiber72StateAt 40) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep40
  change mmFiber72StateAt 40 ∈ closeChainFiber mmWord mmFiber72DirectStates (2 + 62) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 2 62 [mmFiber72StateAt 0] (mmFiber72StateAt 40) h2

theorem mmFiber72State41_in_close :
    mmFiber72StateAt 41 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 1 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 1) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep1
  have h2 : mmFiber72StateAt 9 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 1) (mmFiber72StateAt 9) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep9
  have h3 : mmFiber72StateAt 41 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 9) (mmFiber72StateAt 41) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep41
  change mmFiber72StateAt 41 ∈ closeChainFiber mmWord mmFiber72DirectStates (3 + 61) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 3 61 [mmFiber72StateAt 0] (mmFiber72StateAt 41) h3

theorem mmFiber72State42_in_close :
    mmFiber72StateAt 42 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 1 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 1) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep1
  have h2 : mmFiber72StateAt 2 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 1) (mmFiber72StateAt 2) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep2
  have h3 : mmFiber72StateAt 10 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 2) (mmFiber72StateAt 10) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep10
  have h4 : mmFiber72StateAt 42 ∈ closeChainFiber mmWord mmFiber72DirectStates 4 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0]
      (mmFiber72StateAt 10) (mmFiber72StateAt 42) (by decide) h3 (by decide)
      mmFiber72ReverseSingleStep42
  change mmFiber72StateAt 42 ∈ closeChainFiber mmWord mmFiber72DirectStates (4 + 60) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 4 60 [mmFiber72StateAt 0] (mmFiber72StateAt 42) h4

theorem mmFiber72State43_in_close :
    mmFiber72StateAt 43 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 3 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 3) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep3
  have h2 : mmFiber72StateAt 11 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 3) (mmFiber72StateAt 11) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep11
  have h3 : mmFiber72StateAt 43 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 11) (mmFiber72StateAt 43) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep43
  change mmFiber72StateAt 43 ∈ closeChainFiber mmWord mmFiber72DirectStates (3 + 61) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 3 61 [mmFiber72StateAt 0] (mmFiber72StateAt 43) h3

theorem mmFiber72State44_in_close :
    mmFiber72StateAt 44 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 4 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 4) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep4
  have h2 : mmFiber72StateAt 12 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 4) (mmFiber72StateAt 12) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep12
  have h3 : mmFiber72StateAt 44 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 12) (mmFiber72StateAt 44) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep44
  change mmFiber72StateAt 44 ∈ closeChainFiber mmWord mmFiber72DirectStates (3 + 61) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 3 61 [mmFiber72StateAt 0] (mmFiber72StateAt 44) h3

theorem mmFiber72State45_in_close :
    mmFiber72StateAt 45 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 1 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 1) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep1
  have h2 : mmFiber72StateAt 5 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 1) (mmFiber72StateAt 5) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep5
  have h3 : mmFiber72StateAt 13 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 5) (mmFiber72StateAt 13) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep13
  have h4 : mmFiber72StateAt 45 ∈ closeChainFiber mmWord mmFiber72DirectStates 4 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0]
      (mmFiber72StateAt 13) (mmFiber72StateAt 45) (by decide) h3 (by decide)
      mmFiber72ReverseSingleStep45
  change mmFiber72StateAt 45 ∈ closeChainFiber mmWord mmFiber72DirectStates (4 + 60) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 4 60 [mmFiber72StateAt 0] (mmFiber72StateAt 45) h4

theorem mmFiber72State46_in_close :
    mmFiber72StateAt 46 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 4 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 4) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep4
  have h2 : mmFiber72StateAt 6 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 4) (mmFiber72StateAt 6) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep6
  have h3 : mmFiber72StateAt 14 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 6) (mmFiber72StateAt 14) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep14
  have h4 : mmFiber72StateAt 46 ∈ closeChainFiber mmWord mmFiber72DirectStates 4 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0]
      (mmFiber72StateAt 14) (mmFiber72StateAt 46) (by decide) h3 (by decide)
      mmFiber72ReverseSingleStep46
  change mmFiber72StateAt 46 ∈ closeChainFiber mmWord mmFiber72DirectStates (4 + 60) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 4 60 [mmFiber72StateAt 0] (mmFiber72StateAt 46) h4

theorem mmFiber72State47_in_close :
    mmFiber72StateAt 47 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 3 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 3) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep3
  have h2 : mmFiber72StateAt 7 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 3) (mmFiber72StateAt 7) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep7
  have h3 : mmFiber72StateAt 15 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 7) (mmFiber72StateAt 15) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep15
  have h4 : mmFiber72StateAt 47 ∈ closeChainFiber mmWord mmFiber72DirectStates 4 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0]
      (mmFiber72StateAt 15) (mmFiber72StateAt 47) (by decide) h3 (by decide)
      mmFiber72ReverseSingleStep47
  change mmFiber72StateAt 47 ∈ closeChainFiber mmWord mmFiber72DirectStates (4 + 60) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 4 60 [mmFiber72StateAt 0] (mmFiber72StateAt 47) h4

theorem mmFiber72State48_in_close :
    mmFiber72StateAt 48 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 32 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 32) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep32
  have h2 : mmFiber72StateAt 48 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 32) (mmFiber72StateAt 48) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep48
  change mmFiber72StateAt 48 ∈ closeChainFiber mmWord mmFiber72DirectStates (2 + 62) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 2 62 [mmFiber72StateAt 0] (mmFiber72StateAt 48) h2

theorem mmFiber72State49_in_close :
    mmFiber72StateAt 49 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 1 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 1) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep1
  have h2 : mmFiber72StateAt 33 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 1) (mmFiber72StateAt 33) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep33
  have h3 : mmFiber72StateAt 49 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 33) (mmFiber72StateAt 49) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep49
  change mmFiber72StateAt 49 ∈ closeChainFiber mmWord mmFiber72DirectStates (3 + 61) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 3 61 [mmFiber72StateAt 0] (mmFiber72StateAt 49) h3

theorem mmFiber72State50_in_close :
    mmFiber72StateAt 50 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 32 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 32) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep32
  have h2 : mmFiber72StateAt 48 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 32) (mmFiber72StateAt 48) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep48
  have h3 : mmFiber72StateAt 50 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 48) (mmFiber72StateAt 50) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep50
  change mmFiber72StateAt 50 ∈ closeChainFiber mmWord mmFiber72DirectStates (3 + 61) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 3 61 [mmFiber72StateAt 0] (mmFiber72StateAt 50) h3

theorem mmFiber72State51_in_close :
    mmFiber72StateAt 51 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 3 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 3) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep3
  have h2 : mmFiber72StateAt 35 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 3) (mmFiber72StateAt 35) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep35
  have h3 : mmFiber72StateAt 51 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 35) (mmFiber72StateAt 51) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep51
  change mmFiber72StateAt 51 ∈ closeChainFiber mmWord mmFiber72DirectStates (3 + 61) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 3 61 [mmFiber72StateAt 0] (mmFiber72StateAt 51) h3

theorem mmFiber72State52_in_close :
    mmFiber72StateAt 52 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 4 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 4) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep4
  have h2 : mmFiber72StateAt 36 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 4) (mmFiber72StateAt 36) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep36
  have h3 : mmFiber72StateAt 52 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 36) (mmFiber72StateAt 52) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep52
  change mmFiber72StateAt 52 ∈ closeChainFiber mmWord mmFiber72DirectStates (3 + 61) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 3 61 [mmFiber72StateAt 0] (mmFiber72StateAt 52) h3

theorem mmFiber72State53_in_close :
    mmFiber72StateAt 53 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 1 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 1) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep1
  have h2 : mmFiber72StateAt 5 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 1) (mmFiber72StateAt 5) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep5
  have h3 : mmFiber72StateAt 37 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 5) (mmFiber72StateAt 37) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep37
  have h4 : mmFiber72StateAt 53 ∈ closeChainFiber mmWord mmFiber72DirectStates 4 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0]
      (mmFiber72StateAt 37) (mmFiber72StateAt 53) (by decide) h3 (by decide)
      mmFiber72ReverseSingleStep53
  change mmFiber72StateAt 53 ∈ closeChainFiber mmWord mmFiber72DirectStates (4 + 60) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 4 60 [mmFiber72StateAt 0] (mmFiber72StateAt 53) h4

theorem mmFiber72State54_in_close :
    mmFiber72StateAt 54 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 1 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 1) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep1
  have h2 : mmFiber72StateAt 33 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 1) (mmFiber72StateAt 33) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep33
  have h3 : mmFiber72StateAt 49 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 33) (mmFiber72StateAt 49) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep49
  have h4 : mmFiber72StateAt 54 ∈ closeChainFiber mmWord mmFiber72DirectStates 4 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0]
      (mmFiber72StateAt 49) (mmFiber72StateAt 54) (by decide) h3 (by decide)
      mmFiber72ReverseSingleStep54
  change mmFiber72StateAt 54 ∈ closeChainFiber mmWord mmFiber72DirectStates (4 + 60) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 4 60 [mmFiber72StateAt 0] (mmFiber72StateAt 54) h4

theorem mmFiber72State55_in_close :
    mmFiber72StateAt 55 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 32 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 32) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep32
  have h2 : mmFiber72StateAt 48 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 32) (mmFiber72StateAt 48) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep48
  have h3 : mmFiber72StateAt 55 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 48) (mmFiber72StateAt 55) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep55
  change mmFiber72StateAt 55 ∈ closeChainFiber mmWord mmFiber72DirectStates (3 + 61) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 3 61 [mmFiber72StateAt 0] (mmFiber72StateAt 55) h3

theorem mmFiber72State56_in_close :
    mmFiber72StateAt 56 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 8 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 8) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep8
  have h2 : mmFiber72StateAt 40 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 8) (mmFiber72StateAt 40) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep40
  have h3 : mmFiber72StateAt 56 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 40) (mmFiber72StateAt 56) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep56
  change mmFiber72StateAt 56 ∈ closeChainFiber mmWord mmFiber72DirectStates (3 + 61) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 3 61 [mmFiber72StateAt 0] (mmFiber72StateAt 56) h3

theorem mmFiber72State57_in_close :
    mmFiber72StateAt 57 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 1 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 1) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep1
  have h2 : mmFiber72StateAt 9 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 1) (mmFiber72StateAt 9) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep9
  have h3 : mmFiber72StateAt 41 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 9) (mmFiber72StateAt 41) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep41
  have h4 : mmFiber72StateAt 57 ∈ closeChainFiber mmWord mmFiber72DirectStates 4 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0]
      (mmFiber72StateAt 41) (mmFiber72StateAt 57) (by decide) h3 (by decide)
      mmFiber72ReverseSingleStep57
  change mmFiber72StateAt 57 ∈ closeChainFiber mmWord mmFiber72DirectStates (4 + 60) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 4 60 [mmFiber72StateAt 0] (mmFiber72StateAt 57) h4

theorem mmFiber72State58_in_close :
    mmFiber72StateAt 58 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 4 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 4) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep4
  have h2 : mmFiber72StateAt 26 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 4) (mmFiber72StateAt 26) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep26
  have h3 : mmFiber72StateAt 58 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 26) (mmFiber72StateAt 58) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep58
  change mmFiber72StateAt 58 ∈ closeChainFiber mmWord mmFiber72DirectStates (3 + 61) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 3 61 [mmFiber72StateAt 0] (mmFiber72StateAt 58) h3

theorem mmFiber72State59_in_close :
    mmFiber72StateAt 59 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 1 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 1) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep1
  have h2 : mmFiber72StateAt 5 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 1) (mmFiber72StateAt 5) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep5
  have h3 : mmFiber72StateAt 27 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 5) (mmFiber72StateAt 27) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep27
  have h4 : mmFiber72StateAt 59 ∈ closeChainFiber mmWord mmFiber72DirectStates 4 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0]
      (mmFiber72StateAt 27) (mmFiber72StateAt 59) (by decide) h3 (by decide)
      mmFiber72ReverseSingleStep59
  change mmFiber72StateAt 59 ∈ closeChainFiber mmWord mmFiber72DirectStates (4 + 60) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 4 60 [mmFiber72StateAt 0] (mmFiber72StateAt 59) h4

theorem mmFiber72State60_in_close :
    mmFiber72StateAt 60 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 28 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 28) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep28
  have h2 : mmFiber72StateAt 60 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 28) (mmFiber72StateAt 60) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep60
  change mmFiber72StateAt 60 ∈ closeChainFiber mmWord mmFiber72DirectStates (2 + 62) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 2 62 [mmFiber72StateAt 0] (mmFiber72StateAt 60) h2

theorem mmFiber72State61_in_close :
    mmFiber72StateAt 61 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 1 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 1) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep1
  have h2 : mmFiber72StateAt 29 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 1) (mmFiber72StateAt 29) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep29
  have h3 : mmFiber72StateAt 61 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 29) (mmFiber72StateAt 61) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep61
  change mmFiber72StateAt 61 ∈ closeChainFiber mmWord mmFiber72DirectStates (3 + 61) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 3 61 [mmFiber72StateAt 0] (mmFiber72StateAt 61) h3

theorem mmFiber72State62_in_close :
    mmFiber72StateAt 62 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 28 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 28) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep28
  have h2 : mmFiber72StateAt 60 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 28) (mmFiber72StateAt 60) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep60
  have h3 : mmFiber72StateAt 62 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 60) (mmFiber72StateAt 62) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep62
  change mmFiber72StateAt 62 ∈ closeChainFiber mmWord mmFiber72DirectStates (3 + 61) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 3 61 [mmFiber72StateAt 0] (mmFiber72StateAt 62) h3

theorem mmFiber72State63_in_close :
    mmFiber72StateAt 63 ∈ closeChainFiber mmWord mmFiber72DirectStates mmFiber72DirectStates.length [mmFiber72StateAt 0] := by
  have h0 : mmFiber72StateAt 0 ∈ closeChainFiber mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber72StateAt 3 ∈ closeChainFiber mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 0 [mmFiber72StateAt 0]
      (mmFiber72StateAt 0) (mmFiber72StateAt 3) (by decide) h0 (by decide)
      mmFiber72ReverseSingleStep3
  have h2 : mmFiber72StateAt 31 ∈ closeChainFiber mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 1 [mmFiber72StateAt 0]
      (mmFiber72StateAt 3) (mmFiber72StateAt 31) (by decide) h1 (by decide)
      mmFiber72ReverseSingleStep31
  have h3 : mmFiber72StateAt 63 ∈ closeChainFiber mmWord mmFiber72DirectStates 3 [mmFiber72StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber72DirectStates 2 [mmFiber72StateAt 0]
      (mmFiber72StateAt 31) (mmFiber72StateAt 63) (by decide) h2 (by decide)
      mmFiber72ReverseSingleStep63
  change mmFiber72StateAt 63 ∈ closeChainFiber mmWord mmFiber72DirectStates (3 + 61) [mmFiber72StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber72DirectStates 3 61 [mmFiber72StateAt 0] (mmFiber72StateAt 63) h3

theorem mmFiber72DirectConnected :
    chainFiberConnected mmWord mmFiber72DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber72DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber72State0_in_close
  · subst state
    exact mmFiber72State1_in_close
  · subst state
    exact mmFiber72State2_in_close
  · subst state
    exact mmFiber72State3_in_close
  · subst state
    exact mmFiber72State4_in_close
  · subst state
    exact mmFiber72State5_in_close
  · subst state
    exact mmFiber72State6_in_close
  · subst state
    exact mmFiber72State7_in_close
  · subst state
    exact mmFiber72State8_in_close
  · subst state
    exact mmFiber72State9_in_close
  · subst state
    exact mmFiber72State10_in_close
  · subst state
    exact mmFiber72State11_in_close
  · subst state
    exact mmFiber72State12_in_close
  · subst state
    exact mmFiber72State13_in_close
  · subst state
    exact mmFiber72State14_in_close
  · subst state
    exact mmFiber72State15_in_close
  · subst state
    exact mmFiber72State16_in_close
  · subst state
    exact mmFiber72State17_in_close
  · subst state
    exact mmFiber72State18_in_close
  · subst state
    exact mmFiber72State19_in_close
  · subst state
    exact mmFiber72State20_in_close
  · subst state
    exact mmFiber72State21_in_close
  · subst state
    exact mmFiber72State22_in_close
  · subst state
    exact mmFiber72State23_in_close
  · subst state
    exact mmFiber72State24_in_close
  · subst state
    exact mmFiber72State25_in_close
  · subst state
    exact mmFiber72State26_in_close
  · subst state
    exact mmFiber72State27_in_close
  · subst state
    exact mmFiber72State28_in_close
  · subst state
    exact mmFiber72State29_in_close
  · subst state
    exact mmFiber72State30_in_close
  · subst state
    exact mmFiber72State31_in_close
  · subst state
    exact mmFiber72State32_in_close
  · subst state
    exact mmFiber72State33_in_close
  · subst state
    exact mmFiber72State34_in_close
  · subst state
    exact mmFiber72State35_in_close
  · subst state
    exact mmFiber72State36_in_close
  · subst state
    exact mmFiber72State37_in_close
  · subst state
    exact mmFiber72State38_in_close
  · subst state
    exact mmFiber72State39_in_close
  · subst state
    exact mmFiber72State40_in_close
  · subst state
    exact mmFiber72State41_in_close
  · subst state
    exact mmFiber72State42_in_close
  · subst state
    exact mmFiber72State43_in_close
  · subst state
    exact mmFiber72State44_in_close
  · subst state
    exact mmFiber72State45_in_close
  · subst state
    exact mmFiber72State46_in_close
  · subst state
    exact mmFiber72State47_in_close
  · subst state
    exact mmFiber72State48_in_close
  · subst state
    exact mmFiber72State49_in_close
  · subst state
    exact mmFiber72State50_in_close
  · subst state
    exact mmFiber72State51_in_close
  · subst state
    exact mmFiber72State52_in_close
  · subst state
    exact mmFiber72State53_in_close
  · subst state
    exact mmFiber72State54_in_close
  · subst state
    exact mmFiber72State55_in_close
  · subst state
    exact mmFiber72State56_in_close
  · subst state
    exact mmFiber72State57_in_close
  · subst state
    exact mmFiber72State58_in_close
  · subst state
    exact mmFiber72State59_in_close
  · subst state
    exact mmFiber72State60_in_close
  · subst state
    exact mmFiber72State61_in_close
  · subst state
    exact mmFiber72State62_in_close
  · subst state
    exact mmFiber72State63_in_close
  · cases h
end GoertzelLemma818LengthTwoMMBridge

end Mettapedia.GraphTheory.FourColor
