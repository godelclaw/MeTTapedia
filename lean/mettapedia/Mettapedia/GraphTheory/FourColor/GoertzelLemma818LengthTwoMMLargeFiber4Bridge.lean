import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for `mirror,mirror` size-64 fiber 4

This module proves direct connectedness for one generated size-64 fiber from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMMBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorMirrorCertificate
open GoertzelLemma818MirrorMirrorReverseAudit

def mmFiber4StateAt (i : Nat) : List TauState :=
  directStates (mmFiber4RowAt i).sourceLeft (mmFiber4RowAt i).sourceRight

def mmFiber4DirectStates : List (List TauState) :=
  [mmFiber4StateAt 0, mmFiber4StateAt 1, mmFiber4StateAt 2, mmFiber4StateAt 3, mmFiber4StateAt 4, mmFiber4StateAt 5, mmFiber4StateAt 6, mmFiber4StateAt 7, mmFiber4StateAt 8, mmFiber4StateAt 9, mmFiber4StateAt 10, mmFiber4StateAt 11, mmFiber4StateAt 12, mmFiber4StateAt 13, mmFiber4StateAt 14, mmFiber4StateAt 15, mmFiber4StateAt 16, mmFiber4StateAt 17, mmFiber4StateAt 18, mmFiber4StateAt 19, mmFiber4StateAt 20, mmFiber4StateAt 21, mmFiber4StateAt 22, mmFiber4StateAt 23, mmFiber4StateAt 24, mmFiber4StateAt 25, mmFiber4StateAt 26, mmFiber4StateAt 27, mmFiber4StateAt 28, mmFiber4StateAt 29, mmFiber4StateAt 30, mmFiber4StateAt 31, mmFiber4StateAt 32, mmFiber4StateAt 33, mmFiber4StateAt 34, mmFiber4StateAt 35, mmFiber4StateAt 36, mmFiber4StateAt 37, mmFiber4StateAt 38, mmFiber4StateAt 39, mmFiber4StateAt 40, mmFiber4StateAt 41, mmFiber4StateAt 42, mmFiber4StateAt 43, mmFiber4StateAt 44, mmFiber4StateAt 45, mmFiber4StateAt 46, mmFiber4StateAt 47, mmFiber4StateAt 48, mmFiber4StateAt 49, mmFiber4StateAt 50, mmFiber4StateAt 51, mmFiber4StateAt 52, mmFiber4StateAt 53, mmFiber4StateAt 54, mmFiber4StateAt 55, mmFiber4StateAt 56, mmFiber4StateAt 57, mmFiber4StateAt 58, mmFiber4StateAt 59, mmFiber4StateAt 60, mmFiber4StateAt 61, mmFiber4StateAt 62, mmFiber4StateAt 63]

theorem mmFiber4ReverseRow_1_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk0_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 0) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 0) (mmFiber4StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 0) (mmFiber4StateAt 1)
    (mmFiber4RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 1) (by decide) mmFiber4ReverseRow_1_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_2_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk1_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 2) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber4ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 0) (mmFiber4StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 0) (mmFiber4StateAt 2)
    (mmFiber4RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 2) (by decide) mmFiber4ReverseRow_2_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_3_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk1_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 2) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 1) (mmFiber4StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 1) (mmFiber4StateAt 3)
    (mmFiber4RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 3) (by decide) mmFiber4ReverseRow_3_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_4_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk2_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 4) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber4ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 2) (mmFiber4StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 2) (mmFiber4StateAt 4)
    (mmFiber4RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 4) (by decide) mmFiber4ReverseRow_4_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_5_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk2_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 4) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 7) (mmFiber4StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 7) (mmFiber4StateAt 5)
    (mmFiber4RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 5) (by decide) mmFiber4ReverseRow_5_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_6_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk3_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 6) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber4ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 1) (mmFiber4StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 1) (mmFiber4StateAt 6)
    (mmFiber4RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 6) (by decide) mmFiber4ReverseRow_6_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_7_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk3_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 6) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 0) (mmFiber4StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 0) (mmFiber4StateAt 7)
    (mmFiber4RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 7) (by decide) mmFiber4ReverseRow_7_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_8_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 8) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk4_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 8) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber4ReverseSingleStep8 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 0) (mmFiber4StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 0) (mmFiber4StateAt 8)
    (mmFiber4RowAt 8).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 8) (by decide) mmFiber4ReverseRow_8_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_9_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 9) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk4_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 8) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep9 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 1) (mmFiber4StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 1) (mmFiber4StateAt 9)
    (mmFiber4RowAt 9).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 9) (by decide) mmFiber4ReverseRow_9_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_10_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 10) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk5_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 10) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber4ReverseSingleStep10 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 2) (mmFiber4StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 2) (mmFiber4StateAt 10)
    (mmFiber4RowAt 10).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 10) (by decide) mmFiber4ReverseRow_10_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_11_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 11) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk5_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 10) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep11 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 3) (mmFiber4StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 3) (mmFiber4StateAt 11)
    (mmFiber4RowAt 11).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 11) (by decide) mmFiber4ReverseRow_11_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_12_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 12) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk6_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 12) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber4ReverseSingleStep12 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 4) (mmFiber4StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 4) (mmFiber4StateAt 12)
    (mmFiber4RowAt 12).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 12) (by decide) mmFiber4ReverseRow_12_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_13_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 13) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk6_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 12) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep13 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 5) (mmFiber4StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 5) (mmFiber4StateAt 13)
    (mmFiber4RowAt 13).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 13) (by decide) mmFiber4ReverseRow_13_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_14_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 14) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk7_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 14) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber4ReverseSingleStep14 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 6) (mmFiber4StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 6) (mmFiber4StateAt 14)
    (mmFiber4RowAt 14).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 14) (by decide) mmFiber4ReverseRow_14_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_15_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 15) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk7_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 14) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep15 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 7) (mmFiber4StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 7) (mmFiber4StateAt 15)
    (mmFiber4RowAt 15).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 15) (by decide) mmFiber4ReverseRow_15_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_16_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 16) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk8_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 16) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber4ReverseSingleStep16 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 0) (mmFiber4StateAt 16) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 0) (mmFiber4StateAt 16)
    (mmFiber4RowAt 16).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 16) (by decide) mmFiber4ReverseRow_16_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_17_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 17) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk8_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 16) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep17 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 1) (mmFiber4StateAt 17) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 1) (mmFiber4StateAt 17)
    (mmFiber4RowAt 17).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 17) (by decide) mmFiber4ReverseRow_17_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_18_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 18) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk9_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 18) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber4ReverseSingleStep18 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 2) (mmFiber4StateAt 18) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 2) (mmFiber4StateAt 18)
    (mmFiber4RowAt 18).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 18) (by decide) mmFiber4ReverseRow_18_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_19_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 19) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk9_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 18) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep19 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 3) (mmFiber4StateAt 19) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 3) (mmFiber4StateAt 19)
    (mmFiber4RowAt 19).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 19) (by decide) mmFiber4ReverseRow_19_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_20_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 20) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk10_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 20) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber4ReverseSingleStep20 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 16) (mmFiber4StateAt 20) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 16) (mmFiber4StateAt 20)
    (mmFiber4RowAt 20).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 20) (by decide) mmFiber4ReverseRow_20_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_21_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 21) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk10_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 20) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep21 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 17) (mmFiber4StateAt 21) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 17) (mmFiber4StateAt 21)
    (mmFiber4RowAt 21).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 21) (by decide) mmFiber4ReverseRow_21_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_22_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 22) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk11_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 22) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber4ReverseSingleStep22 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 6) (mmFiber4StateAt 22) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 6) (mmFiber4StateAt 22)
    (mmFiber4RowAt 22).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 22) (by decide) mmFiber4ReverseRow_22_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_23_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 23) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk11_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 22) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep23 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 7) (mmFiber4StateAt 23) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 7) (mmFiber4StateAt 23)
    (mmFiber4RowAt 23).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 23) (by decide) mmFiber4ReverseRow_23_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_24_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 24) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk12_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 24) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber4ReverseSingleStep24 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 8) (mmFiber4StateAt 24) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 8) (mmFiber4StateAt 24)
    (mmFiber4RowAt 24).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 24) (by decide) mmFiber4ReverseRow_24_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_25_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 25) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk12_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 24) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep25 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 9) (mmFiber4StateAt 25) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 9) (mmFiber4StateAt 25)
    (mmFiber4RowAt 25).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 25) (by decide) mmFiber4ReverseRow_25_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_26_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 26) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk13_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 26) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber4ReverseSingleStep26 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 10) (mmFiber4StateAt 26) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 10) (mmFiber4StateAt 26)
    (mmFiber4RowAt 26).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 26) (by decide) mmFiber4ReverseRow_26_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_27_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 27) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk13_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 26) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep27 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 11) (mmFiber4StateAt 27) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 11) (mmFiber4StateAt 27)
    (mmFiber4RowAt 27).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 27) (by decide) mmFiber4ReverseRow_27_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_28_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 28) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk14_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 28) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber4ReverseSingleStep28 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 24) (mmFiber4StateAt 28) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 24) (mmFiber4StateAt 28)
    (mmFiber4RowAt 28).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 28) (by decide) mmFiber4ReverseRow_28_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_29_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 29) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk14_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 28) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep29 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 25) (mmFiber4StateAt 29) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 25) (mmFiber4StateAt 29)
    (mmFiber4RowAt 29).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 29) (by decide) mmFiber4ReverseRow_29_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_30_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 30) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk15_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 30) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber4ReverseSingleStep30 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 14) (mmFiber4StateAt 30) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 14) (mmFiber4StateAt 30)
    (mmFiber4RowAt 30).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 30) (by decide) mmFiber4ReverseRow_30_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_31_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 31) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk15_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 30) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep31 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 15) (mmFiber4StateAt 31) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 15) (mmFiber4StateAt 31)
    (mmFiber4RowAt 31).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 31) (by decide) mmFiber4ReverseRow_31_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_32_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 32) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk16_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 32) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber4ReverseSingleStep32 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 0) (mmFiber4StateAt 32) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 0) (mmFiber4StateAt 32)
    (mmFiber4RowAt 32).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 32) (by decide) mmFiber4ReverseRow_32_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_33_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 33) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk16_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 32) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep33 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 1) (mmFiber4StateAt 33) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 1) (mmFiber4StateAt 33)
    (mmFiber4RowAt 33).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 33) (by decide) mmFiber4ReverseRow_33_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_34_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 34) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk17_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 34) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber4ReverseSingleStep34 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 2) (mmFiber4StateAt 34) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 2) (mmFiber4StateAt 34)
    (mmFiber4RowAt 34).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 34) (by decide) mmFiber4ReverseRow_34_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_35_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 35) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk17_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 34) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep35 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 32) (mmFiber4StateAt 35) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 32) (mmFiber4StateAt 35)
    (mmFiber4RowAt 35).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 35) (by decide) mmFiber4ReverseRow_35_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_36_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 36) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk18_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 36) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber4ReverseSingleStep36 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 32) (mmFiber4StateAt 36) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 32) (mmFiber4StateAt 36)
    (mmFiber4RowAt 36).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 36) (by decide) mmFiber4ReverseRow_36_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_37_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 37) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk18_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 36) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep37 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 33) (mmFiber4StateAt 37) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 33) (mmFiber4StateAt 37)
    (mmFiber4RowAt 37).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 37) (by decide) mmFiber4ReverseRow_37_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_38_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 38) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk19_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 38) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber4ReverseSingleStep38 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 6) (mmFiber4StateAt 38) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 6) (mmFiber4StateAt 38)
    (mmFiber4RowAt 38).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 38) (by decide) mmFiber4ReverseRow_38_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_39_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 39) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk19_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 38) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep39 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 7) (mmFiber4StateAt 39) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 7) (mmFiber4StateAt 39)
    (mmFiber4RowAt 39).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 39) (by decide) mmFiber4ReverseRow_39_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_40_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 40) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk20_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 40) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber4ReverseSingleStep40 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 8) (mmFiber4StateAt 40) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 8) (mmFiber4StateAt 40)
    (mmFiber4RowAt 40).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 40) (by decide) mmFiber4ReverseRow_40_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_41_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 41) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk20_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 40) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep41 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 9) (mmFiber4StateAt 41) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 9) (mmFiber4StateAt 41)
    (mmFiber4RowAt 41).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 41) (by decide) mmFiber4ReverseRow_41_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_42_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 42) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk21_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 42) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber4ReverseSingleStep42 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 10) (mmFiber4StateAt 42) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 10) (mmFiber4StateAt 42)
    (mmFiber4RowAt 42).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 42) (by decide) mmFiber4ReverseRow_42_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_43_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 43) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk21_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 42) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep43 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 40) (mmFiber4StateAt 43) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 40) (mmFiber4StateAt 43)
    (mmFiber4RowAt 43).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 43) (by decide) mmFiber4ReverseRow_43_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_44_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 44) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk22_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 44) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber4ReverseSingleStep44 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 40) (mmFiber4StateAt 44) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 40) (mmFiber4StateAt 44)
    (mmFiber4RowAt 44).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 44) (by decide) mmFiber4ReverseRow_44_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_45_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 45) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk22_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 44) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep45 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 41) (mmFiber4StateAt 45) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 41) (mmFiber4StateAt 45)
    (mmFiber4RowAt 45).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 45) (by decide) mmFiber4ReverseRow_45_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_46_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 46) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk23_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 46) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber4ReverseSingleStep46 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 14) (mmFiber4StateAt 46) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 14) (mmFiber4StateAt 46)
    (mmFiber4RowAt 46).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 46) (by decide) mmFiber4ReverseRow_46_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_47_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 47) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk23_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 46) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep47 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 15) (mmFiber4StateAt 47) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 15) (mmFiber4StateAt 47)
    (mmFiber4RowAt 47).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 47) (by decide) mmFiber4ReverseRow_47_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_48_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 48) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk24_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 48) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber4ReverseSingleStep48 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 16) (mmFiber4StateAt 48) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 16) (mmFiber4StateAt 48)
    (mmFiber4RowAt 48).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 48) (by decide) mmFiber4ReverseRow_48_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_49_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 49) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk24_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 48) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep49 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 17) (mmFiber4StateAt 49) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 17) (mmFiber4StateAt 49)
    (mmFiber4RowAt 49).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 49) (by decide) mmFiber4ReverseRow_49_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_50_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 50) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk25_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 50) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber4ReverseSingleStep50 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 18) (mmFiber4StateAt 50) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 18) (mmFiber4StateAt 50)
    (mmFiber4RowAt 50).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 50) (by decide) mmFiber4ReverseRow_50_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_51_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 51) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk25_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 50) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep51 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 19) (mmFiber4StateAt 51) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 19) (mmFiber4StateAt 51)
    (mmFiber4RowAt 51).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 51) (by decide) mmFiber4ReverseRow_51_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_52_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 52) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk26_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 52) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber4ReverseSingleStep52 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 40) (mmFiber4StateAt 52) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 40) (mmFiber4StateAt 52)
    (mmFiber4RowAt 52).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 52) (by decide) mmFiber4ReverseRow_52_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_53_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 53) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk26_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 52) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep53 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 41) (mmFiber4StateAt 53) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 41) (mmFiber4StateAt 53)
    (mmFiber4RowAt 53).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 53) (by decide) mmFiber4ReverseRow_53_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_54_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 54) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk27_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 54) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber4ReverseSingleStep54 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 22) (mmFiber4StateAt 54) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 22) (mmFiber4StateAt 54)
    (mmFiber4RowAt 54).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 54) (by decide) mmFiber4ReverseRow_54_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_55_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 55) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk27_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 54) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep55 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 23) (mmFiber4StateAt 55) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 23) (mmFiber4StateAt 55)
    (mmFiber4RowAt 55).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 55) (by decide) mmFiber4ReverseRow_55_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_56_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 56) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk28_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 56) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber4ReverseSingleStep56 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 39) (mmFiber4StateAt 56) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 39) (mmFiber4StateAt 56)
    (mmFiber4RowAt 56).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 56) (by decide) mmFiber4ReverseRow_56_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_57_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 57) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk28_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 56) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep57 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 38) (mmFiber4StateAt 57) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 38) (mmFiber4StateAt 57)
    (mmFiber4RowAt 57).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 57) (by decide) mmFiber4ReverseRow_57_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_58_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 58) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk29_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 58) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber4ReverseSingleStep58 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 36) (mmFiber4StateAt 58) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 36) (mmFiber4StateAt 58)
    (mmFiber4RowAt 58).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 58) (by decide) mmFiber4ReverseRow_58_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_59_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 59) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk29_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 58) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep59 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 37) (mmFiber4StateAt 59) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 37) (mmFiber4StateAt 59)
    (mmFiber4RowAt 59).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 59) (by decide) mmFiber4ReverseRow_59_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_60_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 60) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk30_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 60) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber4ReverseSingleStep60 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 32) (mmFiber4StateAt 60) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 32) (mmFiber4StateAt 60)
    (mmFiber4RowAt 60).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 60) (by decide) mmFiber4ReverseRow_60_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_61_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 61) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk30_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 60) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep61 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 33) (mmFiber4StateAt 61) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 33) (mmFiber4StateAt 61)
    (mmFiber4RowAt 61).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 61) (by decide) mmFiber4ReverseRow_61_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_62_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 62) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk31_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 62) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber4ReverseSingleStep62 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 34) (mmFiber4StateAt 62) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 34) (mmFiber4StateAt 62)
    (mmFiber4RowAt 62).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 62) (by decide) mmFiber4ReverseRow_62_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4ReverseRow_63_ok :
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 63) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber4Chunk31_ok
  change (mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 62) &&
    mmRowReverseValid mmFiber4Key mmFiber4Expected (mmFiber4RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber4ReverseSingleStep63 :
    chainSingleKempeStep mmWord (mmFiber4StateAt 35) (mmFiber4StateAt 63) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber4StateAt 35) (mmFiber4StateAt 63)
    (mmFiber4RowAt 63).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber4Key mmFiber4Expected
        (mmFiber4RowAt 63) (by decide) mmFiber4ReverseRow_63_ok
      simpa [mmFiber4StateAt, mmFiber4RowAt, mmFiber4Rows, listGetD, directRow] using h)

theorem mmFiber4State0_in_close :
    mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  change mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 64 [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 0 64 [mmFiber4StateAt 0] (mmFiber4StateAt 0) (by simp [closeChainFiber])

theorem mmFiber4State1_in_close :
    mmFiber4StateAt 1 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 1 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 1) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep1
  change mmFiber4StateAt 1 ∈ closeChainFiber mmWord mmFiber4DirectStates (1 + 63) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 1 63 [mmFiber4StateAt 0] (mmFiber4StateAt 1) h1

theorem mmFiber4State2_in_close :
    mmFiber4StateAt 2 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 2 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 2) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep2
  change mmFiber4StateAt 2 ∈ closeChainFiber mmWord mmFiber4DirectStates (1 + 63) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 1 63 [mmFiber4StateAt 0] (mmFiber4StateAt 2) h1

theorem mmFiber4State3_in_close :
    mmFiber4StateAt 3 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 1 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 1) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep1
  have h2 : mmFiber4StateAt 3 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 1) (mmFiber4StateAt 3) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep3
  change mmFiber4StateAt 3 ∈ closeChainFiber mmWord mmFiber4DirectStates (2 + 62) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 2 62 [mmFiber4StateAt 0] (mmFiber4StateAt 3) h2

theorem mmFiber4State4_in_close :
    mmFiber4StateAt 4 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 2 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 2) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep2
  have h2 : mmFiber4StateAt 4 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 2) (mmFiber4StateAt 4) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep4
  change mmFiber4StateAt 4 ∈ closeChainFiber mmWord mmFiber4DirectStates (2 + 62) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 2 62 [mmFiber4StateAt 0] (mmFiber4StateAt 4) h2

theorem mmFiber4State5_in_close :
    mmFiber4StateAt 5 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 7 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 7) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep7
  have h2 : mmFiber4StateAt 5 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 7) (mmFiber4StateAt 5) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep5
  change mmFiber4StateAt 5 ∈ closeChainFiber mmWord mmFiber4DirectStates (2 + 62) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 2 62 [mmFiber4StateAt 0] (mmFiber4StateAt 5) h2

theorem mmFiber4State6_in_close :
    mmFiber4StateAt 6 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 1 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 1) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep1
  have h2 : mmFiber4StateAt 6 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 1) (mmFiber4StateAt 6) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep6
  change mmFiber4StateAt 6 ∈ closeChainFiber mmWord mmFiber4DirectStates (2 + 62) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 2 62 [mmFiber4StateAt 0] (mmFiber4StateAt 6) h2

theorem mmFiber4State7_in_close :
    mmFiber4StateAt 7 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 7 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 7) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep7
  change mmFiber4StateAt 7 ∈ closeChainFiber mmWord mmFiber4DirectStates (1 + 63) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 1 63 [mmFiber4StateAt 0] (mmFiber4StateAt 7) h1

theorem mmFiber4State8_in_close :
    mmFiber4StateAt 8 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 8 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 8) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep8
  change mmFiber4StateAt 8 ∈ closeChainFiber mmWord mmFiber4DirectStates (1 + 63) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 1 63 [mmFiber4StateAt 0] (mmFiber4StateAt 8) h1

theorem mmFiber4State9_in_close :
    mmFiber4StateAt 9 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 1 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 1) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep1
  have h2 : mmFiber4StateAt 9 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 1) (mmFiber4StateAt 9) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep9
  change mmFiber4StateAt 9 ∈ closeChainFiber mmWord mmFiber4DirectStates (2 + 62) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 2 62 [mmFiber4StateAt 0] (mmFiber4StateAt 9) h2

theorem mmFiber4State10_in_close :
    mmFiber4StateAt 10 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 2 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 2) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep2
  have h2 : mmFiber4StateAt 10 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 2) (mmFiber4StateAt 10) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep10
  change mmFiber4StateAt 10 ∈ closeChainFiber mmWord mmFiber4DirectStates (2 + 62) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 2 62 [mmFiber4StateAt 0] (mmFiber4StateAt 10) h2

theorem mmFiber4State11_in_close :
    mmFiber4StateAt 11 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 1 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 1) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep1
  have h2 : mmFiber4StateAt 3 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 1) (mmFiber4StateAt 3) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep3
  have h3 : mmFiber4StateAt 11 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 3) (mmFiber4StateAt 11) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep11
  change mmFiber4StateAt 11 ∈ closeChainFiber mmWord mmFiber4DirectStates (3 + 61) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 3 61 [mmFiber4StateAt 0] (mmFiber4StateAt 11) h3

theorem mmFiber4State12_in_close :
    mmFiber4StateAt 12 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 2 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 2) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep2
  have h2 : mmFiber4StateAt 4 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 2) (mmFiber4StateAt 4) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep4
  have h3 : mmFiber4StateAt 12 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 4) (mmFiber4StateAt 12) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep12
  change mmFiber4StateAt 12 ∈ closeChainFiber mmWord mmFiber4DirectStates (3 + 61) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 3 61 [mmFiber4StateAt 0] (mmFiber4StateAt 12) h3

theorem mmFiber4State13_in_close :
    mmFiber4StateAt 13 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 7 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 7) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep7
  have h2 : mmFiber4StateAt 5 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 7) (mmFiber4StateAt 5) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep5
  have h3 : mmFiber4StateAt 13 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 5) (mmFiber4StateAt 13) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep13
  change mmFiber4StateAt 13 ∈ closeChainFiber mmWord mmFiber4DirectStates (3 + 61) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 3 61 [mmFiber4StateAt 0] (mmFiber4StateAt 13) h3

theorem mmFiber4State14_in_close :
    mmFiber4StateAt 14 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 1 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 1) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep1
  have h2 : mmFiber4StateAt 6 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 1) (mmFiber4StateAt 6) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep6
  have h3 : mmFiber4StateAt 14 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 6) (mmFiber4StateAt 14) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep14
  change mmFiber4StateAt 14 ∈ closeChainFiber mmWord mmFiber4DirectStates (3 + 61) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 3 61 [mmFiber4StateAt 0] (mmFiber4StateAt 14) h3

theorem mmFiber4State15_in_close :
    mmFiber4StateAt 15 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 7 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 7) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep7
  have h2 : mmFiber4StateAt 15 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 7) (mmFiber4StateAt 15) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep15
  change mmFiber4StateAt 15 ∈ closeChainFiber mmWord mmFiber4DirectStates (2 + 62) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 2 62 [mmFiber4StateAt 0] (mmFiber4StateAt 15) h2

theorem mmFiber4State16_in_close :
    mmFiber4StateAt 16 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 16 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 16) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep16
  change mmFiber4StateAt 16 ∈ closeChainFiber mmWord mmFiber4DirectStates (1 + 63) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 1 63 [mmFiber4StateAt 0] (mmFiber4StateAt 16) h1

theorem mmFiber4State17_in_close :
    mmFiber4StateAt 17 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 1 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 1) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep1
  have h2 : mmFiber4StateAt 17 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 1) (mmFiber4StateAt 17) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep17
  change mmFiber4StateAt 17 ∈ closeChainFiber mmWord mmFiber4DirectStates (2 + 62) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 2 62 [mmFiber4StateAt 0] (mmFiber4StateAt 17) h2

theorem mmFiber4State18_in_close :
    mmFiber4StateAt 18 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 2 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 2) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep2
  have h2 : mmFiber4StateAt 18 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 2) (mmFiber4StateAt 18) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep18
  change mmFiber4StateAt 18 ∈ closeChainFiber mmWord mmFiber4DirectStates (2 + 62) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 2 62 [mmFiber4StateAt 0] (mmFiber4StateAt 18) h2

theorem mmFiber4State19_in_close :
    mmFiber4StateAt 19 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 1 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 1) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep1
  have h2 : mmFiber4StateAt 3 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 1) (mmFiber4StateAt 3) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep3
  have h3 : mmFiber4StateAt 19 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 3) (mmFiber4StateAt 19) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep19
  change mmFiber4StateAt 19 ∈ closeChainFiber mmWord mmFiber4DirectStates (3 + 61) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 3 61 [mmFiber4StateAt 0] (mmFiber4StateAt 19) h3

theorem mmFiber4State20_in_close :
    mmFiber4StateAt 20 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 16 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 16) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep16
  have h2 : mmFiber4StateAt 20 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 16) (mmFiber4StateAt 20) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep20
  change mmFiber4StateAt 20 ∈ closeChainFiber mmWord mmFiber4DirectStates (2 + 62) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 2 62 [mmFiber4StateAt 0] (mmFiber4StateAt 20) h2

theorem mmFiber4State21_in_close :
    mmFiber4StateAt 21 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 1 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 1) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep1
  have h2 : mmFiber4StateAt 17 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 1) (mmFiber4StateAt 17) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep17
  have h3 : mmFiber4StateAt 21 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 17) (mmFiber4StateAt 21) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep21
  change mmFiber4StateAt 21 ∈ closeChainFiber mmWord mmFiber4DirectStates (3 + 61) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 3 61 [mmFiber4StateAt 0] (mmFiber4StateAt 21) h3

theorem mmFiber4State22_in_close :
    mmFiber4StateAt 22 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 1 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 1) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep1
  have h2 : mmFiber4StateAt 6 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 1) (mmFiber4StateAt 6) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep6
  have h3 : mmFiber4StateAt 22 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 6) (mmFiber4StateAt 22) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep22
  change mmFiber4StateAt 22 ∈ closeChainFiber mmWord mmFiber4DirectStates (3 + 61) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 3 61 [mmFiber4StateAt 0] (mmFiber4StateAt 22) h3

theorem mmFiber4State23_in_close :
    mmFiber4StateAt 23 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 7 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 7) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep7
  have h2 : mmFiber4StateAt 23 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 7) (mmFiber4StateAt 23) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep23
  change mmFiber4StateAt 23 ∈ closeChainFiber mmWord mmFiber4DirectStates (2 + 62) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 2 62 [mmFiber4StateAt 0] (mmFiber4StateAt 23) h2

theorem mmFiber4State24_in_close :
    mmFiber4StateAt 24 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 8 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 8) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep8
  have h2 : mmFiber4StateAt 24 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 8) (mmFiber4StateAt 24) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep24
  change mmFiber4StateAt 24 ∈ closeChainFiber mmWord mmFiber4DirectStates (2 + 62) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 2 62 [mmFiber4StateAt 0] (mmFiber4StateAt 24) h2

theorem mmFiber4State25_in_close :
    mmFiber4StateAt 25 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 1 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 1) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep1
  have h2 : mmFiber4StateAt 9 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 1) (mmFiber4StateAt 9) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep9
  have h3 : mmFiber4StateAt 25 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 9) (mmFiber4StateAt 25) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep25
  change mmFiber4StateAt 25 ∈ closeChainFiber mmWord mmFiber4DirectStates (3 + 61) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 3 61 [mmFiber4StateAt 0] (mmFiber4StateAt 25) h3

theorem mmFiber4State26_in_close :
    mmFiber4StateAt 26 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 2 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 2) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep2
  have h2 : mmFiber4StateAt 10 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 2) (mmFiber4StateAt 10) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep10
  have h3 : mmFiber4StateAt 26 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 10) (mmFiber4StateAt 26) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep26
  change mmFiber4StateAt 26 ∈ closeChainFiber mmWord mmFiber4DirectStates (3 + 61) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 3 61 [mmFiber4StateAt 0] (mmFiber4StateAt 26) h3

theorem mmFiber4State27_in_close :
    mmFiber4StateAt 27 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 1 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 1) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep1
  have h2 : mmFiber4StateAt 3 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 1) (mmFiber4StateAt 3) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep3
  have h3 : mmFiber4StateAt 11 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 3) (mmFiber4StateAt 11) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep11
  have h4 : mmFiber4StateAt 27 ∈ closeChainFiber mmWord mmFiber4DirectStates 4 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0]
      (mmFiber4StateAt 11) (mmFiber4StateAt 27) (by decide) h3 (by decide)
      mmFiber4ReverseSingleStep27
  change mmFiber4StateAt 27 ∈ closeChainFiber mmWord mmFiber4DirectStates (4 + 60) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 4 60 [mmFiber4StateAt 0] (mmFiber4StateAt 27) h4

theorem mmFiber4State28_in_close :
    mmFiber4StateAt 28 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 8 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 8) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep8
  have h2 : mmFiber4StateAt 24 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 8) (mmFiber4StateAt 24) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep24
  have h3 : mmFiber4StateAt 28 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 24) (mmFiber4StateAt 28) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep28
  change mmFiber4StateAt 28 ∈ closeChainFiber mmWord mmFiber4DirectStates (3 + 61) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 3 61 [mmFiber4StateAt 0] (mmFiber4StateAt 28) h3

theorem mmFiber4State29_in_close :
    mmFiber4StateAt 29 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 1 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 1) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep1
  have h2 : mmFiber4StateAt 9 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 1) (mmFiber4StateAt 9) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep9
  have h3 : mmFiber4StateAt 25 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 9) (mmFiber4StateAt 25) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep25
  have h4 : mmFiber4StateAt 29 ∈ closeChainFiber mmWord mmFiber4DirectStates 4 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0]
      (mmFiber4StateAt 25) (mmFiber4StateAt 29) (by decide) h3 (by decide)
      mmFiber4ReverseSingleStep29
  change mmFiber4StateAt 29 ∈ closeChainFiber mmWord mmFiber4DirectStates (4 + 60) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 4 60 [mmFiber4StateAt 0] (mmFiber4StateAt 29) h4

theorem mmFiber4State30_in_close :
    mmFiber4StateAt 30 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 1 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 1) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep1
  have h2 : mmFiber4StateAt 6 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 1) (mmFiber4StateAt 6) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep6
  have h3 : mmFiber4StateAt 14 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 6) (mmFiber4StateAt 14) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep14
  have h4 : mmFiber4StateAt 30 ∈ closeChainFiber mmWord mmFiber4DirectStates 4 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0]
      (mmFiber4StateAt 14) (mmFiber4StateAt 30) (by decide) h3 (by decide)
      mmFiber4ReverseSingleStep30
  change mmFiber4StateAt 30 ∈ closeChainFiber mmWord mmFiber4DirectStates (4 + 60) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 4 60 [mmFiber4StateAt 0] (mmFiber4StateAt 30) h4

theorem mmFiber4State31_in_close :
    mmFiber4StateAt 31 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 7 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 7) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep7
  have h2 : mmFiber4StateAt 15 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 7) (mmFiber4StateAt 15) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep15
  have h3 : mmFiber4StateAt 31 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 15) (mmFiber4StateAt 31) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep31
  change mmFiber4StateAt 31 ∈ closeChainFiber mmWord mmFiber4DirectStates (3 + 61) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 3 61 [mmFiber4StateAt 0] (mmFiber4StateAt 31) h3

theorem mmFiber4State32_in_close :
    mmFiber4StateAt 32 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 32 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 32) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep32
  change mmFiber4StateAt 32 ∈ closeChainFiber mmWord mmFiber4DirectStates (1 + 63) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 1 63 [mmFiber4StateAt 0] (mmFiber4StateAt 32) h1

theorem mmFiber4State33_in_close :
    mmFiber4StateAt 33 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 1 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 1) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep1
  have h2 : mmFiber4StateAt 33 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 1) (mmFiber4StateAt 33) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep33
  change mmFiber4StateAt 33 ∈ closeChainFiber mmWord mmFiber4DirectStates (2 + 62) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 2 62 [mmFiber4StateAt 0] (mmFiber4StateAt 33) h2

theorem mmFiber4State34_in_close :
    mmFiber4StateAt 34 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 2 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 2) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep2
  have h2 : mmFiber4StateAt 34 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 2) (mmFiber4StateAt 34) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep34
  change mmFiber4StateAt 34 ∈ closeChainFiber mmWord mmFiber4DirectStates (2 + 62) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 2 62 [mmFiber4StateAt 0] (mmFiber4StateAt 34) h2

theorem mmFiber4State35_in_close :
    mmFiber4StateAt 35 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 32 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 32) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep32
  have h2 : mmFiber4StateAt 35 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 32) (mmFiber4StateAt 35) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep35
  change mmFiber4StateAt 35 ∈ closeChainFiber mmWord mmFiber4DirectStates (2 + 62) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 2 62 [mmFiber4StateAt 0] (mmFiber4StateAt 35) h2

theorem mmFiber4State36_in_close :
    mmFiber4StateAt 36 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 32 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 32) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep32
  have h2 : mmFiber4StateAt 36 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 32) (mmFiber4StateAt 36) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep36
  change mmFiber4StateAt 36 ∈ closeChainFiber mmWord mmFiber4DirectStates (2 + 62) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 2 62 [mmFiber4StateAt 0] (mmFiber4StateAt 36) h2

theorem mmFiber4State37_in_close :
    mmFiber4StateAt 37 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 1 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 1) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep1
  have h2 : mmFiber4StateAt 33 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 1) (mmFiber4StateAt 33) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep33
  have h3 : mmFiber4StateAt 37 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 33) (mmFiber4StateAt 37) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep37
  change mmFiber4StateAt 37 ∈ closeChainFiber mmWord mmFiber4DirectStates (3 + 61) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 3 61 [mmFiber4StateAt 0] (mmFiber4StateAt 37) h3

theorem mmFiber4State38_in_close :
    mmFiber4StateAt 38 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 1 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 1) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep1
  have h2 : mmFiber4StateAt 6 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 1) (mmFiber4StateAt 6) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep6
  have h3 : mmFiber4StateAt 38 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 6) (mmFiber4StateAt 38) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep38
  change mmFiber4StateAt 38 ∈ closeChainFiber mmWord mmFiber4DirectStates (3 + 61) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 3 61 [mmFiber4StateAt 0] (mmFiber4StateAt 38) h3

theorem mmFiber4State39_in_close :
    mmFiber4StateAt 39 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 7 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 7) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep7
  have h2 : mmFiber4StateAt 39 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 7) (mmFiber4StateAt 39) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep39
  change mmFiber4StateAt 39 ∈ closeChainFiber mmWord mmFiber4DirectStates (2 + 62) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 2 62 [mmFiber4StateAt 0] (mmFiber4StateAt 39) h2

theorem mmFiber4State40_in_close :
    mmFiber4StateAt 40 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 8 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 8) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep8
  have h2 : mmFiber4StateAt 40 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 8) (mmFiber4StateAt 40) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep40
  change mmFiber4StateAt 40 ∈ closeChainFiber mmWord mmFiber4DirectStates (2 + 62) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 2 62 [mmFiber4StateAt 0] (mmFiber4StateAt 40) h2

theorem mmFiber4State41_in_close :
    mmFiber4StateAt 41 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 1 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 1) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep1
  have h2 : mmFiber4StateAt 9 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 1) (mmFiber4StateAt 9) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep9
  have h3 : mmFiber4StateAt 41 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 9) (mmFiber4StateAt 41) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep41
  change mmFiber4StateAt 41 ∈ closeChainFiber mmWord mmFiber4DirectStates (3 + 61) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 3 61 [mmFiber4StateAt 0] (mmFiber4StateAt 41) h3

theorem mmFiber4State42_in_close :
    mmFiber4StateAt 42 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 2 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 2) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep2
  have h2 : mmFiber4StateAt 10 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 2) (mmFiber4StateAt 10) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep10
  have h3 : mmFiber4StateAt 42 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 10) (mmFiber4StateAt 42) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep42
  change mmFiber4StateAt 42 ∈ closeChainFiber mmWord mmFiber4DirectStates (3 + 61) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 3 61 [mmFiber4StateAt 0] (mmFiber4StateAt 42) h3

theorem mmFiber4State43_in_close :
    mmFiber4StateAt 43 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 8 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 8) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep8
  have h2 : mmFiber4StateAt 40 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 8) (mmFiber4StateAt 40) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep40
  have h3 : mmFiber4StateAt 43 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 40) (mmFiber4StateAt 43) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep43
  change mmFiber4StateAt 43 ∈ closeChainFiber mmWord mmFiber4DirectStates (3 + 61) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 3 61 [mmFiber4StateAt 0] (mmFiber4StateAt 43) h3

theorem mmFiber4State44_in_close :
    mmFiber4StateAt 44 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 8 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 8) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep8
  have h2 : mmFiber4StateAt 40 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 8) (mmFiber4StateAt 40) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep40
  have h3 : mmFiber4StateAt 44 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 40) (mmFiber4StateAt 44) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep44
  change mmFiber4StateAt 44 ∈ closeChainFiber mmWord mmFiber4DirectStates (3 + 61) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 3 61 [mmFiber4StateAt 0] (mmFiber4StateAt 44) h3

theorem mmFiber4State45_in_close :
    mmFiber4StateAt 45 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 1 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 1) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep1
  have h2 : mmFiber4StateAt 9 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 1) (mmFiber4StateAt 9) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep9
  have h3 : mmFiber4StateAt 41 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 9) (mmFiber4StateAt 41) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep41
  have h4 : mmFiber4StateAt 45 ∈ closeChainFiber mmWord mmFiber4DirectStates 4 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0]
      (mmFiber4StateAt 41) (mmFiber4StateAt 45) (by decide) h3 (by decide)
      mmFiber4ReverseSingleStep45
  change mmFiber4StateAt 45 ∈ closeChainFiber mmWord mmFiber4DirectStates (4 + 60) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 4 60 [mmFiber4StateAt 0] (mmFiber4StateAt 45) h4

theorem mmFiber4State46_in_close :
    mmFiber4StateAt 46 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 1 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 1) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep1
  have h2 : mmFiber4StateAt 6 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 1) (mmFiber4StateAt 6) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep6
  have h3 : mmFiber4StateAt 14 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 6) (mmFiber4StateAt 14) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep14
  have h4 : mmFiber4StateAt 46 ∈ closeChainFiber mmWord mmFiber4DirectStates 4 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0]
      (mmFiber4StateAt 14) (mmFiber4StateAt 46) (by decide) h3 (by decide)
      mmFiber4ReverseSingleStep46
  change mmFiber4StateAt 46 ∈ closeChainFiber mmWord mmFiber4DirectStates (4 + 60) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 4 60 [mmFiber4StateAt 0] (mmFiber4StateAt 46) h4

theorem mmFiber4State47_in_close :
    mmFiber4StateAt 47 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 7 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 7) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep7
  have h2 : mmFiber4StateAt 15 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 7) (mmFiber4StateAt 15) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep15
  have h3 : mmFiber4StateAt 47 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 15) (mmFiber4StateAt 47) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep47
  change mmFiber4StateAt 47 ∈ closeChainFiber mmWord mmFiber4DirectStates (3 + 61) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 3 61 [mmFiber4StateAt 0] (mmFiber4StateAt 47) h3

theorem mmFiber4State48_in_close :
    mmFiber4StateAt 48 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 16 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 16) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep16
  have h2 : mmFiber4StateAt 48 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 16) (mmFiber4StateAt 48) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep48
  change mmFiber4StateAt 48 ∈ closeChainFiber mmWord mmFiber4DirectStates (2 + 62) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 2 62 [mmFiber4StateAt 0] (mmFiber4StateAt 48) h2

theorem mmFiber4State49_in_close :
    mmFiber4StateAt 49 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 1 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 1) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep1
  have h2 : mmFiber4StateAt 17 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 1) (mmFiber4StateAt 17) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep17
  have h3 : mmFiber4StateAt 49 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 17) (mmFiber4StateAt 49) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep49
  change mmFiber4StateAt 49 ∈ closeChainFiber mmWord mmFiber4DirectStates (3 + 61) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 3 61 [mmFiber4StateAt 0] (mmFiber4StateAt 49) h3

theorem mmFiber4State50_in_close :
    mmFiber4StateAt 50 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 2 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 2) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep2
  have h2 : mmFiber4StateAt 18 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 2) (mmFiber4StateAt 18) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep18
  have h3 : mmFiber4StateAt 50 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 18) (mmFiber4StateAt 50) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep50
  change mmFiber4StateAt 50 ∈ closeChainFiber mmWord mmFiber4DirectStates (3 + 61) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 3 61 [mmFiber4StateAt 0] (mmFiber4StateAt 50) h3

theorem mmFiber4State51_in_close :
    mmFiber4StateAt 51 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 1 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 1) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep1
  have h2 : mmFiber4StateAt 3 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 1) (mmFiber4StateAt 3) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep3
  have h3 : mmFiber4StateAt 19 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 3) (mmFiber4StateAt 19) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep19
  have h4 : mmFiber4StateAt 51 ∈ closeChainFiber mmWord mmFiber4DirectStates 4 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0]
      (mmFiber4StateAt 19) (mmFiber4StateAt 51) (by decide) h3 (by decide)
      mmFiber4ReverseSingleStep51
  change mmFiber4StateAt 51 ∈ closeChainFiber mmWord mmFiber4DirectStates (4 + 60) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 4 60 [mmFiber4StateAt 0] (mmFiber4StateAt 51) h4

theorem mmFiber4State52_in_close :
    mmFiber4StateAt 52 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 8 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 8) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep8
  have h2 : mmFiber4StateAt 40 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 8) (mmFiber4StateAt 40) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep40
  have h3 : mmFiber4StateAt 52 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 40) (mmFiber4StateAt 52) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep52
  change mmFiber4StateAt 52 ∈ closeChainFiber mmWord mmFiber4DirectStates (3 + 61) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 3 61 [mmFiber4StateAt 0] (mmFiber4StateAt 52) h3

theorem mmFiber4State53_in_close :
    mmFiber4StateAt 53 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 1 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 1) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep1
  have h2 : mmFiber4StateAt 9 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 1) (mmFiber4StateAt 9) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep9
  have h3 : mmFiber4StateAt 41 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 9) (mmFiber4StateAt 41) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep41
  have h4 : mmFiber4StateAt 53 ∈ closeChainFiber mmWord mmFiber4DirectStates 4 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0]
      (mmFiber4StateAt 41) (mmFiber4StateAt 53) (by decide) h3 (by decide)
      mmFiber4ReverseSingleStep53
  change mmFiber4StateAt 53 ∈ closeChainFiber mmWord mmFiber4DirectStates (4 + 60) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 4 60 [mmFiber4StateAt 0] (mmFiber4StateAt 53) h4

theorem mmFiber4State54_in_close :
    mmFiber4StateAt 54 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 1 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 1) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep1
  have h2 : mmFiber4StateAt 6 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 1) (mmFiber4StateAt 6) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep6
  have h3 : mmFiber4StateAt 22 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 6) (mmFiber4StateAt 22) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep22
  have h4 : mmFiber4StateAt 54 ∈ closeChainFiber mmWord mmFiber4DirectStates 4 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0]
      (mmFiber4StateAt 22) (mmFiber4StateAt 54) (by decide) h3 (by decide)
      mmFiber4ReverseSingleStep54
  change mmFiber4StateAt 54 ∈ closeChainFiber mmWord mmFiber4DirectStates (4 + 60) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 4 60 [mmFiber4StateAt 0] (mmFiber4StateAt 54) h4

theorem mmFiber4State55_in_close :
    mmFiber4StateAt 55 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 7 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 7) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep7
  have h2 : mmFiber4StateAt 23 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 7) (mmFiber4StateAt 23) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep23
  have h3 : mmFiber4StateAt 55 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 23) (mmFiber4StateAt 55) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep55
  change mmFiber4StateAt 55 ∈ closeChainFiber mmWord mmFiber4DirectStates (3 + 61) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 3 61 [mmFiber4StateAt 0] (mmFiber4StateAt 55) h3

theorem mmFiber4State56_in_close :
    mmFiber4StateAt 56 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 7 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 7) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep7
  have h2 : mmFiber4StateAt 39 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 7) (mmFiber4StateAt 39) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep39
  have h3 : mmFiber4StateAt 56 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 39) (mmFiber4StateAt 56) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep56
  change mmFiber4StateAt 56 ∈ closeChainFiber mmWord mmFiber4DirectStates (3 + 61) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 3 61 [mmFiber4StateAt 0] (mmFiber4StateAt 56) h3

theorem mmFiber4State57_in_close :
    mmFiber4StateAt 57 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 1 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 1) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep1
  have h2 : mmFiber4StateAt 6 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 1) (mmFiber4StateAt 6) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep6
  have h3 : mmFiber4StateAt 38 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 6) (mmFiber4StateAt 38) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep38
  have h4 : mmFiber4StateAt 57 ∈ closeChainFiber mmWord mmFiber4DirectStates 4 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0]
      (mmFiber4StateAt 38) (mmFiber4StateAt 57) (by decide) h3 (by decide)
      mmFiber4ReverseSingleStep57
  change mmFiber4StateAt 57 ∈ closeChainFiber mmWord mmFiber4DirectStates (4 + 60) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 4 60 [mmFiber4StateAt 0] (mmFiber4StateAt 57) h4

theorem mmFiber4State58_in_close :
    mmFiber4StateAt 58 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 32 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 32) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep32
  have h2 : mmFiber4StateAt 36 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 32) (mmFiber4StateAt 36) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep36
  have h3 : mmFiber4StateAt 58 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 36) (mmFiber4StateAt 58) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep58
  change mmFiber4StateAt 58 ∈ closeChainFiber mmWord mmFiber4DirectStates (3 + 61) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 3 61 [mmFiber4StateAt 0] (mmFiber4StateAt 58) h3

theorem mmFiber4State59_in_close :
    mmFiber4StateAt 59 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 1 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 1) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep1
  have h2 : mmFiber4StateAt 33 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 1) (mmFiber4StateAt 33) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep33
  have h3 : mmFiber4StateAt 37 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 33) (mmFiber4StateAt 37) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep37
  have h4 : mmFiber4StateAt 59 ∈ closeChainFiber mmWord mmFiber4DirectStates 4 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0]
      (mmFiber4StateAt 37) (mmFiber4StateAt 59) (by decide) h3 (by decide)
      mmFiber4ReverseSingleStep59
  change mmFiber4StateAt 59 ∈ closeChainFiber mmWord mmFiber4DirectStates (4 + 60) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 4 60 [mmFiber4StateAt 0] (mmFiber4StateAt 59) h4

theorem mmFiber4State60_in_close :
    mmFiber4StateAt 60 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 32 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 32) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep32
  have h2 : mmFiber4StateAt 60 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 32) (mmFiber4StateAt 60) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep60
  change mmFiber4StateAt 60 ∈ closeChainFiber mmWord mmFiber4DirectStates (2 + 62) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 2 62 [mmFiber4StateAt 0] (mmFiber4StateAt 60) h2

theorem mmFiber4State61_in_close :
    mmFiber4StateAt 61 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 1 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 1) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep1
  have h2 : mmFiber4StateAt 33 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 1) (mmFiber4StateAt 33) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep33
  have h3 : mmFiber4StateAt 61 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 33) (mmFiber4StateAt 61) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep61
  change mmFiber4StateAt 61 ∈ closeChainFiber mmWord mmFiber4DirectStates (3 + 61) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 3 61 [mmFiber4StateAt 0] (mmFiber4StateAt 61) h3

theorem mmFiber4State62_in_close :
    mmFiber4StateAt 62 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 2 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 2) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep2
  have h2 : mmFiber4StateAt 34 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 2) (mmFiber4StateAt 34) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep34
  have h3 : mmFiber4StateAt 62 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 34) (mmFiber4StateAt 62) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep62
  change mmFiber4StateAt 62 ∈ closeChainFiber mmWord mmFiber4DirectStates (3 + 61) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 3 61 [mmFiber4StateAt 0] (mmFiber4StateAt 62) h3

theorem mmFiber4State63_in_close :
    mmFiber4StateAt 63 ∈ closeChainFiber mmWord mmFiber4DirectStates mmFiber4DirectStates.length [mmFiber4StateAt 0] := by
  have h0 : mmFiber4StateAt 0 ∈ closeChainFiber mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber4StateAt 32 ∈ closeChainFiber mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 0 [mmFiber4StateAt 0]
      (mmFiber4StateAt 0) (mmFiber4StateAt 32) (by decide) h0 (by decide)
      mmFiber4ReverseSingleStep32
  have h2 : mmFiber4StateAt 35 ∈ closeChainFiber mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 1 [mmFiber4StateAt 0]
      (mmFiber4StateAt 32) (mmFiber4StateAt 35) (by decide) h1 (by decide)
      mmFiber4ReverseSingleStep35
  have h3 : mmFiber4StateAt 63 ∈ closeChainFiber mmWord mmFiber4DirectStates 3 [mmFiber4StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber4DirectStates 2 [mmFiber4StateAt 0]
      (mmFiber4StateAt 35) (mmFiber4StateAt 63) (by decide) h2 (by decide)
      mmFiber4ReverseSingleStep63
  change mmFiber4StateAt 63 ∈ closeChainFiber mmWord mmFiber4DirectStates (3 + 61) [mmFiber4StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber4DirectStates 3 61 [mmFiber4StateAt 0] (mmFiber4StateAt 63) h3

theorem mmFiber4DirectConnected :
    chainFiberConnected mmWord mmFiber4DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber4DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber4State0_in_close
  · subst state
    exact mmFiber4State1_in_close
  · subst state
    exact mmFiber4State2_in_close
  · subst state
    exact mmFiber4State3_in_close
  · subst state
    exact mmFiber4State4_in_close
  · subst state
    exact mmFiber4State5_in_close
  · subst state
    exact mmFiber4State6_in_close
  · subst state
    exact mmFiber4State7_in_close
  · subst state
    exact mmFiber4State8_in_close
  · subst state
    exact mmFiber4State9_in_close
  · subst state
    exact mmFiber4State10_in_close
  · subst state
    exact mmFiber4State11_in_close
  · subst state
    exact mmFiber4State12_in_close
  · subst state
    exact mmFiber4State13_in_close
  · subst state
    exact mmFiber4State14_in_close
  · subst state
    exact mmFiber4State15_in_close
  · subst state
    exact mmFiber4State16_in_close
  · subst state
    exact mmFiber4State17_in_close
  · subst state
    exact mmFiber4State18_in_close
  · subst state
    exact mmFiber4State19_in_close
  · subst state
    exact mmFiber4State20_in_close
  · subst state
    exact mmFiber4State21_in_close
  · subst state
    exact mmFiber4State22_in_close
  · subst state
    exact mmFiber4State23_in_close
  · subst state
    exact mmFiber4State24_in_close
  · subst state
    exact mmFiber4State25_in_close
  · subst state
    exact mmFiber4State26_in_close
  · subst state
    exact mmFiber4State27_in_close
  · subst state
    exact mmFiber4State28_in_close
  · subst state
    exact mmFiber4State29_in_close
  · subst state
    exact mmFiber4State30_in_close
  · subst state
    exact mmFiber4State31_in_close
  · subst state
    exact mmFiber4State32_in_close
  · subst state
    exact mmFiber4State33_in_close
  · subst state
    exact mmFiber4State34_in_close
  · subst state
    exact mmFiber4State35_in_close
  · subst state
    exact mmFiber4State36_in_close
  · subst state
    exact mmFiber4State37_in_close
  · subst state
    exact mmFiber4State38_in_close
  · subst state
    exact mmFiber4State39_in_close
  · subst state
    exact mmFiber4State40_in_close
  · subst state
    exact mmFiber4State41_in_close
  · subst state
    exact mmFiber4State42_in_close
  · subst state
    exact mmFiber4State43_in_close
  · subst state
    exact mmFiber4State44_in_close
  · subst state
    exact mmFiber4State45_in_close
  · subst state
    exact mmFiber4State46_in_close
  · subst state
    exact mmFiber4State47_in_close
  · subst state
    exact mmFiber4State48_in_close
  · subst state
    exact mmFiber4State49_in_close
  · subst state
    exact mmFiber4State50_in_close
  · subst state
    exact mmFiber4State51_in_close
  · subst state
    exact mmFiber4State52_in_close
  · subst state
    exact mmFiber4State53_in_close
  · subst state
    exact mmFiber4State54_in_close
  · subst state
    exact mmFiber4State55_in_close
  · subst state
    exact mmFiber4State56_in_close
  · subst state
    exact mmFiber4State57_in_close
  · subst state
    exact mmFiber4State58_in_close
  · subst state
    exact mmFiber4State59_in_close
  · subst state
    exact mmFiber4State60_in_close
  · subst state
    exact mmFiber4State61_in_close
  · subst state
    exact mmFiber4State62_in_close
  · subst state
    exact mmFiber4State63_in_close
  · cases h
end GoertzelLemma818LengthTwoMMBridge

end Mettapedia.GraphTheory.FourColor
