import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for size-16 `mirror,normal` length-two fibers, group 0

This module proves direct connectedness for generated `mirror,normal` size-16 fibers from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMTBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorTauCertificate
open GoertzelLemma818MirrorTauReverseAudit

def mtFiber3StateAt (i : Nat) : List TauState :=
  directStates (mtFiber3RowAt i).sourceLeft (mtFiber3RowAt i).sourceRight

def mtFiber3DirectStates : List (List TauState) :=
  [mtFiber3StateAt 0, mtFiber3StateAt 1, mtFiber3StateAt 2, mtFiber3StateAt 3, mtFiber3StateAt 4, mtFiber3StateAt 5, mtFiber3StateAt 6, mtFiber3StateAt 7, mtFiber3StateAt 8, mtFiber3StateAt 9, mtFiber3StateAt 10, mtFiber3StateAt 11, mtFiber3StateAt 12, mtFiber3StateAt 13, mtFiber3StateAt 14, mtFiber3StateAt 15]

theorem mtFiber3ReverseRow_1_ok :
    mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber3Chunk0_ok
  change (mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 0) &&
    mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber3ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber3StateAt 0) (mtFiber3StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber3StateAt 0) (mtFiber3StateAt 1)
    (mtFiber3RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber3Key mtFiber3Expected
        (mtFiber3RowAt 1) (by decide) mtFiber3ReverseRow_1_ok
      simpa [mtFiber3StateAt, mtFiber3RowAt, mtFiber3Rows, listGetD, directRow] using h)

theorem mtFiber3ReverseRow_2_ok :
    mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber3Chunk1_ok
  change (mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 2) &&
    mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber3ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber3StateAt 1) (mtFiber3StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber3StateAt 1) (mtFiber3StateAt 2)
    (mtFiber3RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber3Key mtFiber3Expected
        (mtFiber3RowAt 2) (by decide) mtFiber3ReverseRow_2_ok
      simpa [mtFiber3StateAt, mtFiber3RowAt, mtFiber3Rows, listGetD, directRow] using h)

theorem mtFiber3ReverseRow_3_ok :
    mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber3Chunk1_ok
  change (mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 2) &&
    mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber3ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber3StateAt 0) (mtFiber3StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber3StateAt 0) (mtFiber3StateAt 3)
    (mtFiber3RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber3Key mtFiber3Expected
        (mtFiber3RowAt 3) (by decide) mtFiber3ReverseRow_3_ok
      simpa [mtFiber3StateAt, mtFiber3RowAt, mtFiber3Rows, listGetD, directRow] using h)

theorem mtFiber3ReverseRow_4_ok :
    mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber3Chunk2_ok
  change (mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 4) &&
    mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber3ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber3StateAt 0) (mtFiber3StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber3StateAt 0) (mtFiber3StateAt 4)
    (mtFiber3RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber3Key mtFiber3Expected
        (mtFiber3RowAt 4) (by decide) mtFiber3ReverseRow_4_ok
      simpa [mtFiber3StateAt, mtFiber3RowAt, mtFiber3Rows, listGetD, directRow] using h)

theorem mtFiber3ReverseRow_5_ok :
    mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber3Chunk2_ok
  change (mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 4) &&
    mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber3ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber3StateAt 1) (mtFiber3StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber3StateAt 1) (mtFiber3StateAt 5)
    (mtFiber3RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber3Key mtFiber3Expected
        (mtFiber3RowAt 5) (by decide) mtFiber3ReverseRow_5_ok
      simpa [mtFiber3StateAt, mtFiber3RowAt, mtFiber3Rows, listGetD, directRow] using h)

theorem mtFiber3ReverseRow_6_ok :
    mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber3Chunk3_ok
  change (mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 6) &&
    mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber3ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber3StateAt 2) (mtFiber3StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber3StateAt 2) (mtFiber3StateAt 6)
    (mtFiber3RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber3Key mtFiber3Expected
        (mtFiber3RowAt 6) (by decide) mtFiber3ReverseRow_6_ok
      simpa [mtFiber3StateAt, mtFiber3RowAt, mtFiber3Rows, listGetD, directRow] using h)

theorem mtFiber3ReverseRow_7_ok :
    mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber3Chunk3_ok
  change (mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 6) &&
    mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber3ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber3StateAt 3) (mtFiber3StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber3StateAt 3) (mtFiber3StateAt 7)
    (mtFiber3RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber3Key mtFiber3Expected
        (mtFiber3RowAt 7) (by decide) mtFiber3ReverseRow_7_ok
      simpa [mtFiber3StateAt, mtFiber3RowAt, mtFiber3Rows, listGetD, directRow] using h)

theorem mtFiber3ReverseRow_8_ok :
    mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber3Chunk4_ok
  change (mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 8) &&
    mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber3ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber3StateAt 0) (mtFiber3StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber3StateAt 0) (mtFiber3StateAt 8)
    (mtFiber3RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber3Key mtFiber3Expected
        (mtFiber3RowAt 8) (by decide) mtFiber3ReverseRow_8_ok
      simpa [mtFiber3StateAt, mtFiber3RowAt, mtFiber3Rows, listGetD, directRow] using h)

theorem mtFiber3ReverseRow_9_ok :
    mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber3Chunk4_ok
  change (mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 8) &&
    mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber3ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber3StateAt 1) (mtFiber3StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber3StateAt 1) (mtFiber3StateAt 9)
    (mtFiber3RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber3Key mtFiber3Expected
        (mtFiber3RowAt 9) (by decide) mtFiber3ReverseRow_9_ok
      simpa [mtFiber3StateAt, mtFiber3RowAt, mtFiber3Rows, listGetD, directRow] using h)

theorem mtFiber3ReverseRow_10_ok :
    mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber3Chunk5_ok
  change (mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 10) &&
    mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber3ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber3StateAt 2) (mtFiber3StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber3StateAt 2) (mtFiber3StateAt 10)
    (mtFiber3RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber3Key mtFiber3Expected
        (mtFiber3RowAt 10) (by decide) mtFiber3ReverseRow_10_ok
      simpa [mtFiber3StateAt, mtFiber3RowAt, mtFiber3Rows, listGetD, directRow] using h)

theorem mtFiber3ReverseRow_11_ok :
    mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber3Chunk5_ok
  change (mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 10) &&
    mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber3ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber3StateAt 3) (mtFiber3StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber3StateAt 3) (mtFiber3StateAt 11)
    (mtFiber3RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber3Key mtFiber3Expected
        (mtFiber3RowAt 11) (by decide) mtFiber3ReverseRow_11_ok
      simpa [mtFiber3StateAt, mtFiber3RowAt, mtFiber3Rows, listGetD, directRow] using h)

theorem mtFiber3ReverseRow_12_ok :
    mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber3Chunk6_ok
  change (mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 12) &&
    mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber3ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber3StateAt 4) (mtFiber3StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber3StateAt 4) (mtFiber3StateAt 12)
    (mtFiber3RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber3Key mtFiber3Expected
        (mtFiber3RowAt 12) (by decide) mtFiber3ReverseRow_12_ok
      simpa [mtFiber3StateAt, mtFiber3RowAt, mtFiber3Rows, listGetD, directRow] using h)

theorem mtFiber3ReverseRow_13_ok :
    mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber3Chunk6_ok
  change (mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 12) &&
    mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber3ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber3StateAt 5) (mtFiber3StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber3StateAt 5) (mtFiber3StateAt 13)
    (mtFiber3RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber3Key mtFiber3Expected
        (mtFiber3RowAt 13) (by decide) mtFiber3ReverseRow_13_ok
      simpa [mtFiber3StateAt, mtFiber3RowAt, mtFiber3Rows, listGetD, directRow] using h)

theorem mtFiber3ReverseRow_14_ok :
    mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber3Chunk7_ok
  change (mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 14) &&
    mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber3ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber3StateAt 6) (mtFiber3StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber3StateAt 6) (mtFiber3StateAt 14)
    (mtFiber3RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber3Key mtFiber3Expected
        (mtFiber3RowAt 14) (by decide) mtFiber3ReverseRow_14_ok
      simpa [mtFiber3StateAt, mtFiber3RowAt, mtFiber3Rows, listGetD, directRow] using h)

theorem mtFiber3ReverseRow_15_ok :
    mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber3Chunk7_ok
  change (mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 14) &&
    mtRowReverseValid mtFiber3Key mtFiber3Expected (mtFiber3RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber3ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber3StateAt 7) (mtFiber3StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber3StateAt 7) (mtFiber3StateAt 15)
    (mtFiber3RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber3Key mtFiber3Expected
        (mtFiber3RowAt 15) (by decide) mtFiber3ReverseRow_15_ok
      simpa [mtFiber3StateAt, mtFiber3RowAt, mtFiber3Rows, listGetD, directRow] using h)

theorem mtFiber3State0_in_close :
    mtFiber3StateAt 0 ∈ closeChainFiber mtWord mtFiber3DirectStates mtFiber3DirectStates.length [mtFiber3StateAt 0] := by
  change mtFiber3StateAt 0 ∈ closeChainFiber mtWord mtFiber3DirectStates 16 [mtFiber3StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber3DirectStates 0 16 [mtFiber3StateAt 0] (mtFiber3StateAt 0) (by simp [closeChainFiber])

theorem mtFiber3State1_in_close :
    mtFiber3StateAt 1 ∈ closeChainFiber mtWord mtFiber3DirectStates mtFiber3DirectStates.length [mtFiber3StateAt 0] := by
  have h0 : mtFiber3StateAt 0 ∈ closeChainFiber mtWord mtFiber3DirectStates 0 [mtFiber3StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber3StateAt 1 ∈ closeChainFiber mtWord mtFiber3DirectStates 1 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 0 [mtFiber3StateAt 0]
      (mtFiber3StateAt 0) (mtFiber3StateAt 1) (by decide) h0 (by decide)
      mtFiber3ReverseSingleStep1
  change mtFiber3StateAt 1 ∈ closeChainFiber mtWord mtFiber3DirectStates (1 + 15) [mtFiber3StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber3DirectStates 1 15 [mtFiber3StateAt 0] (mtFiber3StateAt 1) h1

theorem mtFiber3State2_in_close :
    mtFiber3StateAt 2 ∈ closeChainFiber mtWord mtFiber3DirectStates mtFiber3DirectStates.length [mtFiber3StateAt 0] := by
  have h0 : mtFiber3StateAt 0 ∈ closeChainFiber mtWord mtFiber3DirectStates 0 [mtFiber3StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber3StateAt 1 ∈ closeChainFiber mtWord mtFiber3DirectStates 1 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 0 [mtFiber3StateAt 0]
      (mtFiber3StateAt 0) (mtFiber3StateAt 1) (by decide) h0 (by decide)
      mtFiber3ReverseSingleStep1
  have h2 : mtFiber3StateAt 2 ∈ closeChainFiber mtWord mtFiber3DirectStates 2 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 1 [mtFiber3StateAt 0]
      (mtFiber3StateAt 1) (mtFiber3StateAt 2) (by decide) h1 (by decide)
      mtFiber3ReverseSingleStep2
  change mtFiber3StateAt 2 ∈ closeChainFiber mtWord mtFiber3DirectStates (2 + 14) [mtFiber3StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber3DirectStates 2 14 [mtFiber3StateAt 0] (mtFiber3StateAt 2) h2

theorem mtFiber3State3_in_close :
    mtFiber3StateAt 3 ∈ closeChainFiber mtWord mtFiber3DirectStates mtFiber3DirectStates.length [mtFiber3StateAt 0] := by
  have h0 : mtFiber3StateAt 0 ∈ closeChainFiber mtWord mtFiber3DirectStates 0 [mtFiber3StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber3StateAt 3 ∈ closeChainFiber mtWord mtFiber3DirectStates 1 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 0 [mtFiber3StateAt 0]
      (mtFiber3StateAt 0) (mtFiber3StateAt 3) (by decide) h0 (by decide)
      mtFiber3ReverseSingleStep3
  change mtFiber3StateAt 3 ∈ closeChainFiber mtWord mtFiber3DirectStates (1 + 15) [mtFiber3StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber3DirectStates 1 15 [mtFiber3StateAt 0] (mtFiber3StateAt 3) h1

theorem mtFiber3State4_in_close :
    mtFiber3StateAt 4 ∈ closeChainFiber mtWord mtFiber3DirectStates mtFiber3DirectStates.length [mtFiber3StateAt 0] := by
  have h0 : mtFiber3StateAt 0 ∈ closeChainFiber mtWord mtFiber3DirectStates 0 [mtFiber3StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber3StateAt 4 ∈ closeChainFiber mtWord mtFiber3DirectStates 1 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 0 [mtFiber3StateAt 0]
      (mtFiber3StateAt 0) (mtFiber3StateAt 4) (by decide) h0 (by decide)
      mtFiber3ReverseSingleStep4
  change mtFiber3StateAt 4 ∈ closeChainFiber mtWord mtFiber3DirectStates (1 + 15) [mtFiber3StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber3DirectStates 1 15 [mtFiber3StateAt 0] (mtFiber3StateAt 4) h1

theorem mtFiber3State5_in_close :
    mtFiber3StateAt 5 ∈ closeChainFiber mtWord mtFiber3DirectStates mtFiber3DirectStates.length [mtFiber3StateAt 0] := by
  have h0 : mtFiber3StateAt 0 ∈ closeChainFiber mtWord mtFiber3DirectStates 0 [mtFiber3StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber3StateAt 1 ∈ closeChainFiber mtWord mtFiber3DirectStates 1 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 0 [mtFiber3StateAt 0]
      (mtFiber3StateAt 0) (mtFiber3StateAt 1) (by decide) h0 (by decide)
      mtFiber3ReverseSingleStep1
  have h2 : mtFiber3StateAt 5 ∈ closeChainFiber mtWord mtFiber3DirectStates 2 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 1 [mtFiber3StateAt 0]
      (mtFiber3StateAt 1) (mtFiber3StateAt 5) (by decide) h1 (by decide)
      mtFiber3ReverseSingleStep5
  change mtFiber3StateAt 5 ∈ closeChainFiber mtWord mtFiber3DirectStates (2 + 14) [mtFiber3StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber3DirectStates 2 14 [mtFiber3StateAt 0] (mtFiber3StateAt 5) h2

theorem mtFiber3State6_in_close :
    mtFiber3StateAt 6 ∈ closeChainFiber mtWord mtFiber3DirectStates mtFiber3DirectStates.length [mtFiber3StateAt 0] := by
  have h0 : mtFiber3StateAt 0 ∈ closeChainFiber mtWord mtFiber3DirectStates 0 [mtFiber3StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber3StateAt 1 ∈ closeChainFiber mtWord mtFiber3DirectStates 1 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 0 [mtFiber3StateAt 0]
      (mtFiber3StateAt 0) (mtFiber3StateAt 1) (by decide) h0 (by decide)
      mtFiber3ReverseSingleStep1
  have h2 : mtFiber3StateAt 2 ∈ closeChainFiber mtWord mtFiber3DirectStates 2 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 1 [mtFiber3StateAt 0]
      (mtFiber3StateAt 1) (mtFiber3StateAt 2) (by decide) h1 (by decide)
      mtFiber3ReverseSingleStep2
  have h3 : mtFiber3StateAt 6 ∈ closeChainFiber mtWord mtFiber3DirectStates 3 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 2 [mtFiber3StateAt 0]
      (mtFiber3StateAt 2) (mtFiber3StateAt 6) (by decide) h2 (by decide)
      mtFiber3ReverseSingleStep6
  change mtFiber3StateAt 6 ∈ closeChainFiber mtWord mtFiber3DirectStates (3 + 13) [mtFiber3StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber3DirectStates 3 13 [mtFiber3StateAt 0] (mtFiber3StateAt 6) h3

theorem mtFiber3State7_in_close :
    mtFiber3StateAt 7 ∈ closeChainFiber mtWord mtFiber3DirectStates mtFiber3DirectStates.length [mtFiber3StateAt 0] := by
  have h0 : mtFiber3StateAt 0 ∈ closeChainFiber mtWord mtFiber3DirectStates 0 [mtFiber3StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber3StateAt 3 ∈ closeChainFiber mtWord mtFiber3DirectStates 1 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 0 [mtFiber3StateAt 0]
      (mtFiber3StateAt 0) (mtFiber3StateAt 3) (by decide) h0 (by decide)
      mtFiber3ReverseSingleStep3
  have h2 : mtFiber3StateAt 7 ∈ closeChainFiber mtWord mtFiber3DirectStates 2 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 1 [mtFiber3StateAt 0]
      (mtFiber3StateAt 3) (mtFiber3StateAt 7) (by decide) h1 (by decide)
      mtFiber3ReverseSingleStep7
  change mtFiber3StateAt 7 ∈ closeChainFiber mtWord mtFiber3DirectStates (2 + 14) [mtFiber3StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber3DirectStates 2 14 [mtFiber3StateAt 0] (mtFiber3StateAt 7) h2

theorem mtFiber3State8_in_close :
    mtFiber3StateAt 8 ∈ closeChainFiber mtWord mtFiber3DirectStates mtFiber3DirectStates.length [mtFiber3StateAt 0] := by
  have h0 : mtFiber3StateAt 0 ∈ closeChainFiber mtWord mtFiber3DirectStates 0 [mtFiber3StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber3StateAt 8 ∈ closeChainFiber mtWord mtFiber3DirectStates 1 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 0 [mtFiber3StateAt 0]
      (mtFiber3StateAt 0) (mtFiber3StateAt 8) (by decide) h0 (by decide)
      mtFiber3ReverseSingleStep8
  change mtFiber3StateAt 8 ∈ closeChainFiber mtWord mtFiber3DirectStates (1 + 15) [mtFiber3StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber3DirectStates 1 15 [mtFiber3StateAt 0] (mtFiber3StateAt 8) h1

theorem mtFiber3State9_in_close :
    mtFiber3StateAt 9 ∈ closeChainFiber mtWord mtFiber3DirectStates mtFiber3DirectStates.length [mtFiber3StateAt 0] := by
  have h0 : mtFiber3StateAt 0 ∈ closeChainFiber mtWord mtFiber3DirectStates 0 [mtFiber3StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber3StateAt 1 ∈ closeChainFiber mtWord mtFiber3DirectStates 1 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 0 [mtFiber3StateAt 0]
      (mtFiber3StateAt 0) (mtFiber3StateAt 1) (by decide) h0 (by decide)
      mtFiber3ReverseSingleStep1
  have h2 : mtFiber3StateAt 9 ∈ closeChainFiber mtWord mtFiber3DirectStates 2 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 1 [mtFiber3StateAt 0]
      (mtFiber3StateAt 1) (mtFiber3StateAt 9) (by decide) h1 (by decide)
      mtFiber3ReverseSingleStep9
  change mtFiber3StateAt 9 ∈ closeChainFiber mtWord mtFiber3DirectStates (2 + 14) [mtFiber3StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber3DirectStates 2 14 [mtFiber3StateAt 0] (mtFiber3StateAt 9) h2

theorem mtFiber3State10_in_close :
    mtFiber3StateAt 10 ∈ closeChainFiber mtWord mtFiber3DirectStates mtFiber3DirectStates.length [mtFiber3StateAt 0] := by
  have h0 : mtFiber3StateAt 0 ∈ closeChainFiber mtWord mtFiber3DirectStates 0 [mtFiber3StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber3StateAt 1 ∈ closeChainFiber mtWord mtFiber3DirectStates 1 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 0 [mtFiber3StateAt 0]
      (mtFiber3StateAt 0) (mtFiber3StateAt 1) (by decide) h0 (by decide)
      mtFiber3ReverseSingleStep1
  have h2 : mtFiber3StateAt 2 ∈ closeChainFiber mtWord mtFiber3DirectStates 2 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 1 [mtFiber3StateAt 0]
      (mtFiber3StateAt 1) (mtFiber3StateAt 2) (by decide) h1 (by decide)
      mtFiber3ReverseSingleStep2
  have h3 : mtFiber3StateAt 10 ∈ closeChainFiber mtWord mtFiber3DirectStates 3 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 2 [mtFiber3StateAt 0]
      (mtFiber3StateAt 2) (mtFiber3StateAt 10) (by decide) h2 (by decide)
      mtFiber3ReverseSingleStep10
  change mtFiber3StateAt 10 ∈ closeChainFiber mtWord mtFiber3DirectStates (3 + 13) [mtFiber3StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber3DirectStates 3 13 [mtFiber3StateAt 0] (mtFiber3StateAt 10) h3

theorem mtFiber3State11_in_close :
    mtFiber3StateAt 11 ∈ closeChainFiber mtWord mtFiber3DirectStates mtFiber3DirectStates.length [mtFiber3StateAt 0] := by
  have h0 : mtFiber3StateAt 0 ∈ closeChainFiber mtWord mtFiber3DirectStates 0 [mtFiber3StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber3StateAt 3 ∈ closeChainFiber mtWord mtFiber3DirectStates 1 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 0 [mtFiber3StateAt 0]
      (mtFiber3StateAt 0) (mtFiber3StateAt 3) (by decide) h0 (by decide)
      mtFiber3ReverseSingleStep3
  have h2 : mtFiber3StateAt 11 ∈ closeChainFiber mtWord mtFiber3DirectStates 2 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 1 [mtFiber3StateAt 0]
      (mtFiber3StateAt 3) (mtFiber3StateAt 11) (by decide) h1 (by decide)
      mtFiber3ReverseSingleStep11
  change mtFiber3StateAt 11 ∈ closeChainFiber mtWord mtFiber3DirectStates (2 + 14) [mtFiber3StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber3DirectStates 2 14 [mtFiber3StateAt 0] (mtFiber3StateAt 11) h2

theorem mtFiber3State12_in_close :
    mtFiber3StateAt 12 ∈ closeChainFiber mtWord mtFiber3DirectStates mtFiber3DirectStates.length [mtFiber3StateAt 0] := by
  have h0 : mtFiber3StateAt 0 ∈ closeChainFiber mtWord mtFiber3DirectStates 0 [mtFiber3StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber3StateAt 4 ∈ closeChainFiber mtWord mtFiber3DirectStates 1 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 0 [mtFiber3StateAt 0]
      (mtFiber3StateAt 0) (mtFiber3StateAt 4) (by decide) h0 (by decide)
      mtFiber3ReverseSingleStep4
  have h2 : mtFiber3StateAt 12 ∈ closeChainFiber mtWord mtFiber3DirectStates 2 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 1 [mtFiber3StateAt 0]
      (mtFiber3StateAt 4) (mtFiber3StateAt 12) (by decide) h1 (by decide)
      mtFiber3ReverseSingleStep12
  change mtFiber3StateAt 12 ∈ closeChainFiber mtWord mtFiber3DirectStates (2 + 14) [mtFiber3StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber3DirectStates 2 14 [mtFiber3StateAt 0] (mtFiber3StateAt 12) h2

theorem mtFiber3State13_in_close :
    mtFiber3StateAt 13 ∈ closeChainFiber mtWord mtFiber3DirectStates mtFiber3DirectStates.length [mtFiber3StateAt 0] := by
  have h0 : mtFiber3StateAt 0 ∈ closeChainFiber mtWord mtFiber3DirectStates 0 [mtFiber3StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber3StateAt 1 ∈ closeChainFiber mtWord mtFiber3DirectStates 1 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 0 [mtFiber3StateAt 0]
      (mtFiber3StateAt 0) (mtFiber3StateAt 1) (by decide) h0 (by decide)
      mtFiber3ReverseSingleStep1
  have h2 : mtFiber3StateAt 5 ∈ closeChainFiber mtWord mtFiber3DirectStates 2 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 1 [mtFiber3StateAt 0]
      (mtFiber3StateAt 1) (mtFiber3StateAt 5) (by decide) h1 (by decide)
      mtFiber3ReverseSingleStep5
  have h3 : mtFiber3StateAt 13 ∈ closeChainFiber mtWord mtFiber3DirectStates 3 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 2 [mtFiber3StateAt 0]
      (mtFiber3StateAt 5) (mtFiber3StateAt 13) (by decide) h2 (by decide)
      mtFiber3ReverseSingleStep13
  change mtFiber3StateAt 13 ∈ closeChainFiber mtWord mtFiber3DirectStates (3 + 13) [mtFiber3StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber3DirectStates 3 13 [mtFiber3StateAt 0] (mtFiber3StateAt 13) h3

theorem mtFiber3State14_in_close :
    mtFiber3StateAt 14 ∈ closeChainFiber mtWord mtFiber3DirectStates mtFiber3DirectStates.length [mtFiber3StateAt 0] := by
  have h0 : mtFiber3StateAt 0 ∈ closeChainFiber mtWord mtFiber3DirectStates 0 [mtFiber3StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber3StateAt 1 ∈ closeChainFiber mtWord mtFiber3DirectStates 1 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 0 [mtFiber3StateAt 0]
      (mtFiber3StateAt 0) (mtFiber3StateAt 1) (by decide) h0 (by decide)
      mtFiber3ReverseSingleStep1
  have h2 : mtFiber3StateAt 2 ∈ closeChainFiber mtWord mtFiber3DirectStates 2 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 1 [mtFiber3StateAt 0]
      (mtFiber3StateAt 1) (mtFiber3StateAt 2) (by decide) h1 (by decide)
      mtFiber3ReverseSingleStep2
  have h3 : mtFiber3StateAt 6 ∈ closeChainFiber mtWord mtFiber3DirectStates 3 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 2 [mtFiber3StateAt 0]
      (mtFiber3StateAt 2) (mtFiber3StateAt 6) (by decide) h2 (by decide)
      mtFiber3ReverseSingleStep6
  have h4 : mtFiber3StateAt 14 ∈ closeChainFiber mtWord mtFiber3DirectStates 4 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 3 [mtFiber3StateAt 0]
      (mtFiber3StateAt 6) (mtFiber3StateAt 14) (by decide) h3 (by decide)
      mtFiber3ReverseSingleStep14
  change mtFiber3StateAt 14 ∈ closeChainFiber mtWord mtFiber3DirectStates (4 + 12) [mtFiber3StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber3DirectStates 4 12 [mtFiber3StateAt 0] (mtFiber3StateAt 14) h4

theorem mtFiber3State15_in_close :
    mtFiber3StateAt 15 ∈ closeChainFiber mtWord mtFiber3DirectStates mtFiber3DirectStates.length [mtFiber3StateAt 0] := by
  have h0 : mtFiber3StateAt 0 ∈ closeChainFiber mtWord mtFiber3DirectStates 0 [mtFiber3StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber3StateAt 3 ∈ closeChainFiber mtWord mtFiber3DirectStates 1 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 0 [mtFiber3StateAt 0]
      (mtFiber3StateAt 0) (mtFiber3StateAt 3) (by decide) h0 (by decide)
      mtFiber3ReverseSingleStep3
  have h2 : mtFiber3StateAt 7 ∈ closeChainFiber mtWord mtFiber3DirectStates 2 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 1 [mtFiber3StateAt 0]
      (mtFiber3StateAt 3) (mtFiber3StateAt 7) (by decide) h1 (by decide)
      mtFiber3ReverseSingleStep7
  have h3 : mtFiber3StateAt 15 ∈ closeChainFiber mtWord mtFiber3DirectStates 3 [mtFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber3DirectStates 2 [mtFiber3StateAt 0]
      (mtFiber3StateAt 7) (mtFiber3StateAt 15) (by decide) h2 (by decide)
      mtFiber3ReverseSingleStep15
  change mtFiber3StateAt 15 ∈ closeChainFiber mtWord mtFiber3DirectStates (3 + 13) [mtFiber3StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber3DirectStates 3 13 [mtFiber3StateAt 0] (mtFiber3StateAt 15) h3

theorem mtFiber3DirectConnected :
    chainFiberConnected mtWord mtFiber3DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber3DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber3State0_in_close
  · subst state
    exact mtFiber3State1_in_close
  · subst state
    exact mtFiber3State2_in_close
  · subst state
    exact mtFiber3State3_in_close
  · subst state
    exact mtFiber3State4_in_close
  · subst state
    exact mtFiber3State5_in_close
  · subst state
    exact mtFiber3State6_in_close
  · subst state
    exact mtFiber3State7_in_close
  · subst state
    exact mtFiber3State8_in_close
  · subst state
    exact mtFiber3State9_in_close
  · subst state
    exact mtFiber3State10_in_close
  · subst state
    exact mtFiber3State11_in_close
  · subst state
    exact mtFiber3State12_in_close
  · subst state
    exact mtFiber3State13_in_close
  · subst state
    exact mtFiber3State14_in_close
  · subst state
    exact mtFiber3State15_in_close
  · cases h
def mtFiber6StateAt (i : Nat) : List TauState :=
  directStates (mtFiber6RowAt i).sourceLeft (mtFiber6RowAt i).sourceRight

def mtFiber6DirectStates : List (List TauState) :=
  [mtFiber6StateAt 0, mtFiber6StateAt 1, mtFiber6StateAt 2, mtFiber6StateAt 3, mtFiber6StateAt 4, mtFiber6StateAt 5, mtFiber6StateAt 6, mtFiber6StateAt 7, mtFiber6StateAt 8, mtFiber6StateAt 9, mtFiber6StateAt 10, mtFiber6StateAt 11, mtFiber6StateAt 12, mtFiber6StateAt 13, mtFiber6StateAt 14, mtFiber6StateAt 15]

theorem mtFiber6ReverseRow_1_ok :
    mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber6Chunk0_ok
  change (mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 0) &&
    mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber6ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber6StateAt 0) (mtFiber6StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber6StateAt 0) (mtFiber6StateAt 1)
    (mtFiber6RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber6Key mtFiber6Expected
        (mtFiber6RowAt 1) (by decide) mtFiber6ReverseRow_1_ok
      simpa [mtFiber6StateAt, mtFiber6RowAt, mtFiber6Rows, listGetD, directRow] using h)

theorem mtFiber6ReverseRow_2_ok :
    mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber6Chunk1_ok
  change (mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 2) &&
    mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber6ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber6StateAt 0) (mtFiber6StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber6StateAt 0) (mtFiber6StateAt 2)
    (mtFiber6RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber6Key mtFiber6Expected
        (mtFiber6RowAt 2) (by decide) mtFiber6ReverseRow_2_ok
      simpa [mtFiber6StateAt, mtFiber6RowAt, mtFiber6Rows, listGetD, directRow] using h)

theorem mtFiber6ReverseRow_3_ok :
    mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber6Chunk1_ok
  change (mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 2) &&
    mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber6ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber6StateAt 1) (mtFiber6StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber6StateAt 1) (mtFiber6StateAt 3)
    (mtFiber6RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber6Key mtFiber6Expected
        (mtFiber6RowAt 3) (by decide) mtFiber6ReverseRow_3_ok
      simpa [mtFiber6StateAt, mtFiber6RowAt, mtFiber6Rows, listGetD, directRow] using h)

theorem mtFiber6ReverseRow_4_ok :
    mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber6Chunk2_ok
  change (mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 4) &&
    mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber6ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber6StateAt 0) (mtFiber6StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber6StateAt 0) (mtFiber6StateAt 4)
    (mtFiber6RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber6Key mtFiber6Expected
        (mtFiber6RowAt 4) (by decide) mtFiber6ReverseRow_4_ok
      simpa [mtFiber6StateAt, mtFiber6RowAt, mtFiber6Rows, listGetD, directRow] using h)

theorem mtFiber6ReverseRow_5_ok :
    mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber6Chunk2_ok
  change (mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 4) &&
    mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber6ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber6StateAt 1) (mtFiber6StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber6StateAt 1) (mtFiber6StateAt 5)
    (mtFiber6RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber6Key mtFiber6Expected
        (mtFiber6RowAt 5) (by decide) mtFiber6ReverseRow_5_ok
      simpa [mtFiber6StateAt, mtFiber6RowAt, mtFiber6Rows, listGetD, directRow] using h)

theorem mtFiber6ReverseRow_6_ok :
    mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber6Chunk3_ok
  change (mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 6) &&
    mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber6ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber6StateAt 2) (mtFiber6StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber6StateAt 2) (mtFiber6StateAt 6)
    (mtFiber6RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber6Key mtFiber6Expected
        (mtFiber6RowAt 6) (by decide) mtFiber6ReverseRow_6_ok
      simpa [mtFiber6StateAt, mtFiber6RowAt, mtFiber6Rows, listGetD, directRow] using h)

theorem mtFiber6ReverseRow_7_ok :
    mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber6Chunk3_ok
  change (mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 6) &&
    mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber6ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber6StateAt 3) (mtFiber6StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber6StateAt 3) (mtFiber6StateAt 7)
    (mtFiber6RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber6Key mtFiber6Expected
        (mtFiber6RowAt 7) (by decide) mtFiber6ReverseRow_7_ok
      simpa [mtFiber6StateAt, mtFiber6RowAt, mtFiber6Rows, listGetD, directRow] using h)

theorem mtFiber6ReverseRow_8_ok :
    mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber6Chunk4_ok
  change (mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 8) &&
    mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber6ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber6StateAt 0) (mtFiber6StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber6StateAt 0) (mtFiber6StateAt 8)
    (mtFiber6RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber6Key mtFiber6Expected
        (mtFiber6RowAt 8) (by decide) mtFiber6ReverseRow_8_ok
      simpa [mtFiber6StateAt, mtFiber6RowAt, mtFiber6Rows, listGetD, directRow] using h)

theorem mtFiber6ReverseRow_9_ok :
    mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber6Chunk4_ok
  change (mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 8) &&
    mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber6ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber6StateAt 1) (mtFiber6StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber6StateAt 1) (mtFiber6StateAt 9)
    (mtFiber6RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber6Key mtFiber6Expected
        (mtFiber6RowAt 9) (by decide) mtFiber6ReverseRow_9_ok
      simpa [mtFiber6StateAt, mtFiber6RowAt, mtFiber6Rows, listGetD, directRow] using h)

theorem mtFiber6ReverseRow_10_ok :
    mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber6Chunk5_ok
  change (mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 10) &&
    mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber6ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber6StateAt 2) (mtFiber6StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber6StateAt 2) (mtFiber6StateAt 10)
    (mtFiber6RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber6Key mtFiber6Expected
        (mtFiber6RowAt 10) (by decide) mtFiber6ReverseRow_10_ok
      simpa [mtFiber6StateAt, mtFiber6RowAt, mtFiber6Rows, listGetD, directRow] using h)

theorem mtFiber6ReverseRow_11_ok :
    mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber6Chunk5_ok
  change (mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 10) &&
    mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber6ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber6StateAt 3) (mtFiber6StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber6StateAt 3) (mtFiber6StateAt 11)
    (mtFiber6RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber6Key mtFiber6Expected
        (mtFiber6RowAt 11) (by decide) mtFiber6ReverseRow_11_ok
      simpa [mtFiber6StateAt, mtFiber6RowAt, mtFiber6Rows, listGetD, directRow] using h)

theorem mtFiber6ReverseRow_12_ok :
    mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber6Chunk6_ok
  change (mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 12) &&
    mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber6ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber6StateAt 4) (mtFiber6StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber6StateAt 4) (mtFiber6StateAt 12)
    (mtFiber6RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber6Key mtFiber6Expected
        (mtFiber6RowAt 12) (by decide) mtFiber6ReverseRow_12_ok
      simpa [mtFiber6StateAt, mtFiber6RowAt, mtFiber6Rows, listGetD, directRow] using h)

theorem mtFiber6ReverseRow_13_ok :
    mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber6Chunk6_ok
  change (mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 12) &&
    mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber6ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber6StateAt 5) (mtFiber6StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber6StateAt 5) (mtFiber6StateAt 13)
    (mtFiber6RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber6Key mtFiber6Expected
        (mtFiber6RowAt 13) (by decide) mtFiber6ReverseRow_13_ok
      simpa [mtFiber6StateAt, mtFiber6RowAt, mtFiber6Rows, listGetD, directRow] using h)

theorem mtFiber6ReverseRow_14_ok :
    mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber6Chunk7_ok
  change (mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 14) &&
    mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber6ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber6StateAt 6) (mtFiber6StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber6StateAt 6) (mtFiber6StateAt 14)
    (mtFiber6RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber6Key mtFiber6Expected
        (mtFiber6RowAt 14) (by decide) mtFiber6ReverseRow_14_ok
      simpa [mtFiber6StateAt, mtFiber6RowAt, mtFiber6Rows, listGetD, directRow] using h)

theorem mtFiber6ReverseRow_15_ok :
    mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber6Chunk7_ok
  change (mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 14) &&
    mtRowReverseValid mtFiber6Key mtFiber6Expected (mtFiber6RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber6ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber6StateAt 7) (mtFiber6StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber6StateAt 7) (mtFiber6StateAt 15)
    (mtFiber6RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber6Key mtFiber6Expected
        (mtFiber6RowAt 15) (by decide) mtFiber6ReverseRow_15_ok
      simpa [mtFiber6StateAt, mtFiber6RowAt, mtFiber6Rows, listGetD, directRow] using h)

theorem mtFiber6State0_in_close :
    mtFiber6StateAt 0 ∈ closeChainFiber mtWord mtFiber6DirectStates mtFiber6DirectStates.length [mtFiber6StateAt 0] := by
  change mtFiber6StateAt 0 ∈ closeChainFiber mtWord mtFiber6DirectStates 16 [mtFiber6StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber6DirectStates 0 16 [mtFiber6StateAt 0] (mtFiber6StateAt 0) (by simp [closeChainFiber])

theorem mtFiber6State1_in_close :
    mtFiber6StateAt 1 ∈ closeChainFiber mtWord mtFiber6DirectStates mtFiber6DirectStates.length [mtFiber6StateAt 0] := by
  have h0 : mtFiber6StateAt 0 ∈ closeChainFiber mtWord mtFiber6DirectStates 0 [mtFiber6StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber6StateAt 1 ∈ closeChainFiber mtWord mtFiber6DirectStates 1 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 0 [mtFiber6StateAt 0]
      (mtFiber6StateAt 0) (mtFiber6StateAt 1) (by decide) h0 (by decide)
      mtFiber6ReverseSingleStep1
  change mtFiber6StateAt 1 ∈ closeChainFiber mtWord mtFiber6DirectStates (1 + 15) [mtFiber6StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber6DirectStates 1 15 [mtFiber6StateAt 0] (mtFiber6StateAt 1) h1

theorem mtFiber6State2_in_close :
    mtFiber6StateAt 2 ∈ closeChainFiber mtWord mtFiber6DirectStates mtFiber6DirectStates.length [mtFiber6StateAt 0] := by
  have h0 : mtFiber6StateAt 0 ∈ closeChainFiber mtWord mtFiber6DirectStates 0 [mtFiber6StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber6StateAt 2 ∈ closeChainFiber mtWord mtFiber6DirectStates 1 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 0 [mtFiber6StateAt 0]
      (mtFiber6StateAt 0) (mtFiber6StateAt 2) (by decide) h0 (by decide)
      mtFiber6ReverseSingleStep2
  change mtFiber6StateAt 2 ∈ closeChainFiber mtWord mtFiber6DirectStates (1 + 15) [mtFiber6StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber6DirectStates 1 15 [mtFiber6StateAt 0] (mtFiber6StateAt 2) h1

theorem mtFiber6State3_in_close :
    mtFiber6StateAt 3 ∈ closeChainFiber mtWord mtFiber6DirectStates mtFiber6DirectStates.length [mtFiber6StateAt 0] := by
  have h0 : mtFiber6StateAt 0 ∈ closeChainFiber mtWord mtFiber6DirectStates 0 [mtFiber6StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber6StateAt 1 ∈ closeChainFiber mtWord mtFiber6DirectStates 1 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 0 [mtFiber6StateAt 0]
      (mtFiber6StateAt 0) (mtFiber6StateAt 1) (by decide) h0 (by decide)
      mtFiber6ReverseSingleStep1
  have h2 : mtFiber6StateAt 3 ∈ closeChainFiber mtWord mtFiber6DirectStates 2 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 1 [mtFiber6StateAt 0]
      (mtFiber6StateAt 1) (mtFiber6StateAt 3) (by decide) h1 (by decide)
      mtFiber6ReverseSingleStep3
  change mtFiber6StateAt 3 ∈ closeChainFiber mtWord mtFiber6DirectStates (2 + 14) [mtFiber6StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber6DirectStates 2 14 [mtFiber6StateAt 0] (mtFiber6StateAt 3) h2

theorem mtFiber6State4_in_close :
    mtFiber6StateAt 4 ∈ closeChainFiber mtWord mtFiber6DirectStates mtFiber6DirectStates.length [mtFiber6StateAt 0] := by
  have h0 : mtFiber6StateAt 0 ∈ closeChainFiber mtWord mtFiber6DirectStates 0 [mtFiber6StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber6StateAt 4 ∈ closeChainFiber mtWord mtFiber6DirectStates 1 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 0 [mtFiber6StateAt 0]
      (mtFiber6StateAt 0) (mtFiber6StateAt 4) (by decide) h0 (by decide)
      mtFiber6ReverseSingleStep4
  change mtFiber6StateAt 4 ∈ closeChainFiber mtWord mtFiber6DirectStates (1 + 15) [mtFiber6StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber6DirectStates 1 15 [mtFiber6StateAt 0] (mtFiber6StateAt 4) h1

theorem mtFiber6State5_in_close :
    mtFiber6StateAt 5 ∈ closeChainFiber mtWord mtFiber6DirectStates mtFiber6DirectStates.length [mtFiber6StateAt 0] := by
  have h0 : mtFiber6StateAt 0 ∈ closeChainFiber mtWord mtFiber6DirectStates 0 [mtFiber6StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber6StateAt 1 ∈ closeChainFiber mtWord mtFiber6DirectStates 1 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 0 [mtFiber6StateAt 0]
      (mtFiber6StateAt 0) (mtFiber6StateAt 1) (by decide) h0 (by decide)
      mtFiber6ReverseSingleStep1
  have h2 : mtFiber6StateAt 5 ∈ closeChainFiber mtWord mtFiber6DirectStates 2 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 1 [mtFiber6StateAt 0]
      (mtFiber6StateAt 1) (mtFiber6StateAt 5) (by decide) h1 (by decide)
      mtFiber6ReverseSingleStep5
  change mtFiber6StateAt 5 ∈ closeChainFiber mtWord mtFiber6DirectStates (2 + 14) [mtFiber6StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber6DirectStates 2 14 [mtFiber6StateAt 0] (mtFiber6StateAt 5) h2

theorem mtFiber6State6_in_close :
    mtFiber6StateAt 6 ∈ closeChainFiber mtWord mtFiber6DirectStates mtFiber6DirectStates.length [mtFiber6StateAt 0] := by
  have h0 : mtFiber6StateAt 0 ∈ closeChainFiber mtWord mtFiber6DirectStates 0 [mtFiber6StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber6StateAt 2 ∈ closeChainFiber mtWord mtFiber6DirectStates 1 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 0 [mtFiber6StateAt 0]
      (mtFiber6StateAt 0) (mtFiber6StateAt 2) (by decide) h0 (by decide)
      mtFiber6ReverseSingleStep2
  have h2 : mtFiber6StateAt 6 ∈ closeChainFiber mtWord mtFiber6DirectStates 2 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 1 [mtFiber6StateAt 0]
      (mtFiber6StateAt 2) (mtFiber6StateAt 6) (by decide) h1 (by decide)
      mtFiber6ReverseSingleStep6
  change mtFiber6StateAt 6 ∈ closeChainFiber mtWord mtFiber6DirectStates (2 + 14) [mtFiber6StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber6DirectStates 2 14 [mtFiber6StateAt 0] (mtFiber6StateAt 6) h2

theorem mtFiber6State7_in_close :
    mtFiber6StateAt 7 ∈ closeChainFiber mtWord mtFiber6DirectStates mtFiber6DirectStates.length [mtFiber6StateAt 0] := by
  have h0 : mtFiber6StateAt 0 ∈ closeChainFiber mtWord mtFiber6DirectStates 0 [mtFiber6StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber6StateAt 1 ∈ closeChainFiber mtWord mtFiber6DirectStates 1 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 0 [mtFiber6StateAt 0]
      (mtFiber6StateAt 0) (mtFiber6StateAt 1) (by decide) h0 (by decide)
      mtFiber6ReverseSingleStep1
  have h2 : mtFiber6StateAt 3 ∈ closeChainFiber mtWord mtFiber6DirectStates 2 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 1 [mtFiber6StateAt 0]
      (mtFiber6StateAt 1) (mtFiber6StateAt 3) (by decide) h1 (by decide)
      mtFiber6ReverseSingleStep3
  have h3 : mtFiber6StateAt 7 ∈ closeChainFiber mtWord mtFiber6DirectStates 3 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 2 [mtFiber6StateAt 0]
      (mtFiber6StateAt 3) (mtFiber6StateAt 7) (by decide) h2 (by decide)
      mtFiber6ReverseSingleStep7
  change mtFiber6StateAt 7 ∈ closeChainFiber mtWord mtFiber6DirectStates (3 + 13) [mtFiber6StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber6DirectStates 3 13 [mtFiber6StateAt 0] (mtFiber6StateAt 7) h3

theorem mtFiber6State8_in_close :
    mtFiber6StateAt 8 ∈ closeChainFiber mtWord mtFiber6DirectStates mtFiber6DirectStates.length [mtFiber6StateAt 0] := by
  have h0 : mtFiber6StateAt 0 ∈ closeChainFiber mtWord mtFiber6DirectStates 0 [mtFiber6StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber6StateAt 8 ∈ closeChainFiber mtWord mtFiber6DirectStates 1 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 0 [mtFiber6StateAt 0]
      (mtFiber6StateAt 0) (mtFiber6StateAt 8) (by decide) h0 (by decide)
      mtFiber6ReverseSingleStep8
  change mtFiber6StateAt 8 ∈ closeChainFiber mtWord mtFiber6DirectStates (1 + 15) [mtFiber6StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber6DirectStates 1 15 [mtFiber6StateAt 0] (mtFiber6StateAt 8) h1

theorem mtFiber6State9_in_close :
    mtFiber6StateAt 9 ∈ closeChainFiber mtWord mtFiber6DirectStates mtFiber6DirectStates.length [mtFiber6StateAt 0] := by
  have h0 : mtFiber6StateAt 0 ∈ closeChainFiber mtWord mtFiber6DirectStates 0 [mtFiber6StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber6StateAt 1 ∈ closeChainFiber mtWord mtFiber6DirectStates 1 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 0 [mtFiber6StateAt 0]
      (mtFiber6StateAt 0) (mtFiber6StateAt 1) (by decide) h0 (by decide)
      mtFiber6ReverseSingleStep1
  have h2 : mtFiber6StateAt 9 ∈ closeChainFiber mtWord mtFiber6DirectStates 2 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 1 [mtFiber6StateAt 0]
      (mtFiber6StateAt 1) (mtFiber6StateAt 9) (by decide) h1 (by decide)
      mtFiber6ReverseSingleStep9
  change mtFiber6StateAt 9 ∈ closeChainFiber mtWord mtFiber6DirectStates (2 + 14) [mtFiber6StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber6DirectStates 2 14 [mtFiber6StateAt 0] (mtFiber6StateAt 9) h2

theorem mtFiber6State10_in_close :
    mtFiber6StateAt 10 ∈ closeChainFiber mtWord mtFiber6DirectStates mtFiber6DirectStates.length [mtFiber6StateAt 0] := by
  have h0 : mtFiber6StateAt 0 ∈ closeChainFiber mtWord mtFiber6DirectStates 0 [mtFiber6StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber6StateAt 2 ∈ closeChainFiber mtWord mtFiber6DirectStates 1 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 0 [mtFiber6StateAt 0]
      (mtFiber6StateAt 0) (mtFiber6StateAt 2) (by decide) h0 (by decide)
      mtFiber6ReverseSingleStep2
  have h2 : mtFiber6StateAt 10 ∈ closeChainFiber mtWord mtFiber6DirectStates 2 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 1 [mtFiber6StateAt 0]
      (mtFiber6StateAt 2) (mtFiber6StateAt 10) (by decide) h1 (by decide)
      mtFiber6ReverseSingleStep10
  change mtFiber6StateAt 10 ∈ closeChainFiber mtWord mtFiber6DirectStates (2 + 14) [mtFiber6StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber6DirectStates 2 14 [mtFiber6StateAt 0] (mtFiber6StateAt 10) h2

theorem mtFiber6State11_in_close :
    mtFiber6StateAt 11 ∈ closeChainFiber mtWord mtFiber6DirectStates mtFiber6DirectStates.length [mtFiber6StateAt 0] := by
  have h0 : mtFiber6StateAt 0 ∈ closeChainFiber mtWord mtFiber6DirectStates 0 [mtFiber6StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber6StateAt 1 ∈ closeChainFiber mtWord mtFiber6DirectStates 1 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 0 [mtFiber6StateAt 0]
      (mtFiber6StateAt 0) (mtFiber6StateAt 1) (by decide) h0 (by decide)
      mtFiber6ReverseSingleStep1
  have h2 : mtFiber6StateAt 3 ∈ closeChainFiber mtWord mtFiber6DirectStates 2 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 1 [mtFiber6StateAt 0]
      (mtFiber6StateAt 1) (mtFiber6StateAt 3) (by decide) h1 (by decide)
      mtFiber6ReverseSingleStep3
  have h3 : mtFiber6StateAt 11 ∈ closeChainFiber mtWord mtFiber6DirectStates 3 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 2 [mtFiber6StateAt 0]
      (mtFiber6StateAt 3) (mtFiber6StateAt 11) (by decide) h2 (by decide)
      mtFiber6ReverseSingleStep11
  change mtFiber6StateAt 11 ∈ closeChainFiber mtWord mtFiber6DirectStates (3 + 13) [mtFiber6StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber6DirectStates 3 13 [mtFiber6StateAt 0] (mtFiber6StateAt 11) h3

theorem mtFiber6State12_in_close :
    mtFiber6StateAt 12 ∈ closeChainFiber mtWord mtFiber6DirectStates mtFiber6DirectStates.length [mtFiber6StateAt 0] := by
  have h0 : mtFiber6StateAt 0 ∈ closeChainFiber mtWord mtFiber6DirectStates 0 [mtFiber6StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber6StateAt 4 ∈ closeChainFiber mtWord mtFiber6DirectStates 1 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 0 [mtFiber6StateAt 0]
      (mtFiber6StateAt 0) (mtFiber6StateAt 4) (by decide) h0 (by decide)
      mtFiber6ReverseSingleStep4
  have h2 : mtFiber6StateAt 12 ∈ closeChainFiber mtWord mtFiber6DirectStates 2 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 1 [mtFiber6StateAt 0]
      (mtFiber6StateAt 4) (mtFiber6StateAt 12) (by decide) h1 (by decide)
      mtFiber6ReverseSingleStep12
  change mtFiber6StateAt 12 ∈ closeChainFiber mtWord mtFiber6DirectStates (2 + 14) [mtFiber6StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber6DirectStates 2 14 [mtFiber6StateAt 0] (mtFiber6StateAt 12) h2

theorem mtFiber6State13_in_close :
    mtFiber6StateAt 13 ∈ closeChainFiber mtWord mtFiber6DirectStates mtFiber6DirectStates.length [mtFiber6StateAt 0] := by
  have h0 : mtFiber6StateAt 0 ∈ closeChainFiber mtWord mtFiber6DirectStates 0 [mtFiber6StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber6StateAt 1 ∈ closeChainFiber mtWord mtFiber6DirectStates 1 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 0 [mtFiber6StateAt 0]
      (mtFiber6StateAt 0) (mtFiber6StateAt 1) (by decide) h0 (by decide)
      mtFiber6ReverseSingleStep1
  have h2 : mtFiber6StateAt 5 ∈ closeChainFiber mtWord mtFiber6DirectStates 2 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 1 [mtFiber6StateAt 0]
      (mtFiber6StateAt 1) (mtFiber6StateAt 5) (by decide) h1 (by decide)
      mtFiber6ReverseSingleStep5
  have h3 : mtFiber6StateAt 13 ∈ closeChainFiber mtWord mtFiber6DirectStates 3 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 2 [mtFiber6StateAt 0]
      (mtFiber6StateAt 5) (mtFiber6StateAt 13) (by decide) h2 (by decide)
      mtFiber6ReverseSingleStep13
  change mtFiber6StateAt 13 ∈ closeChainFiber mtWord mtFiber6DirectStates (3 + 13) [mtFiber6StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber6DirectStates 3 13 [mtFiber6StateAt 0] (mtFiber6StateAt 13) h3

theorem mtFiber6State14_in_close :
    mtFiber6StateAt 14 ∈ closeChainFiber mtWord mtFiber6DirectStates mtFiber6DirectStates.length [mtFiber6StateAt 0] := by
  have h0 : mtFiber6StateAt 0 ∈ closeChainFiber mtWord mtFiber6DirectStates 0 [mtFiber6StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber6StateAt 2 ∈ closeChainFiber mtWord mtFiber6DirectStates 1 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 0 [mtFiber6StateAt 0]
      (mtFiber6StateAt 0) (mtFiber6StateAt 2) (by decide) h0 (by decide)
      mtFiber6ReverseSingleStep2
  have h2 : mtFiber6StateAt 6 ∈ closeChainFiber mtWord mtFiber6DirectStates 2 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 1 [mtFiber6StateAt 0]
      (mtFiber6StateAt 2) (mtFiber6StateAt 6) (by decide) h1 (by decide)
      mtFiber6ReverseSingleStep6
  have h3 : mtFiber6StateAt 14 ∈ closeChainFiber mtWord mtFiber6DirectStates 3 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 2 [mtFiber6StateAt 0]
      (mtFiber6StateAt 6) (mtFiber6StateAt 14) (by decide) h2 (by decide)
      mtFiber6ReverseSingleStep14
  change mtFiber6StateAt 14 ∈ closeChainFiber mtWord mtFiber6DirectStates (3 + 13) [mtFiber6StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber6DirectStates 3 13 [mtFiber6StateAt 0] (mtFiber6StateAt 14) h3

theorem mtFiber6State15_in_close :
    mtFiber6StateAt 15 ∈ closeChainFiber mtWord mtFiber6DirectStates mtFiber6DirectStates.length [mtFiber6StateAt 0] := by
  have h0 : mtFiber6StateAt 0 ∈ closeChainFiber mtWord mtFiber6DirectStates 0 [mtFiber6StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber6StateAt 1 ∈ closeChainFiber mtWord mtFiber6DirectStates 1 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 0 [mtFiber6StateAt 0]
      (mtFiber6StateAt 0) (mtFiber6StateAt 1) (by decide) h0 (by decide)
      mtFiber6ReverseSingleStep1
  have h2 : mtFiber6StateAt 3 ∈ closeChainFiber mtWord mtFiber6DirectStates 2 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 1 [mtFiber6StateAt 0]
      (mtFiber6StateAt 1) (mtFiber6StateAt 3) (by decide) h1 (by decide)
      mtFiber6ReverseSingleStep3
  have h3 : mtFiber6StateAt 7 ∈ closeChainFiber mtWord mtFiber6DirectStates 3 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 2 [mtFiber6StateAt 0]
      (mtFiber6StateAt 3) (mtFiber6StateAt 7) (by decide) h2 (by decide)
      mtFiber6ReverseSingleStep7
  have h4 : mtFiber6StateAt 15 ∈ closeChainFiber mtWord mtFiber6DirectStates 4 [mtFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber6DirectStates 3 [mtFiber6StateAt 0]
      (mtFiber6StateAt 7) (mtFiber6StateAt 15) (by decide) h3 (by decide)
      mtFiber6ReverseSingleStep15
  change mtFiber6StateAt 15 ∈ closeChainFiber mtWord mtFiber6DirectStates (4 + 12) [mtFiber6StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber6DirectStates 4 12 [mtFiber6StateAt 0] (mtFiber6StateAt 15) h4

theorem mtFiber6DirectConnected :
    chainFiberConnected mtWord mtFiber6DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber6DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber6State0_in_close
  · subst state
    exact mtFiber6State1_in_close
  · subst state
    exact mtFiber6State2_in_close
  · subst state
    exact mtFiber6State3_in_close
  · subst state
    exact mtFiber6State4_in_close
  · subst state
    exact mtFiber6State5_in_close
  · subst state
    exact mtFiber6State6_in_close
  · subst state
    exact mtFiber6State7_in_close
  · subst state
    exact mtFiber6State8_in_close
  · subst state
    exact mtFiber6State9_in_close
  · subst state
    exact mtFiber6State10_in_close
  · subst state
    exact mtFiber6State11_in_close
  · subst state
    exact mtFiber6State12_in_close
  · subst state
    exact mtFiber6State13_in_close
  · subst state
    exact mtFiber6State14_in_close
  · subst state
    exact mtFiber6State15_in_close
  · cases h
def mtFiber9StateAt (i : Nat) : List TauState :=
  directStates (mtFiber9RowAt i).sourceLeft (mtFiber9RowAt i).sourceRight

def mtFiber9DirectStates : List (List TauState) :=
  [mtFiber9StateAt 0, mtFiber9StateAt 1, mtFiber9StateAt 2, mtFiber9StateAt 3, mtFiber9StateAt 4, mtFiber9StateAt 5, mtFiber9StateAt 6, mtFiber9StateAt 7, mtFiber9StateAt 8, mtFiber9StateAt 9, mtFiber9StateAt 10, mtFiber9StateAt 11, mtFiber9StateAt 12, mtFiber9StateAt 13, mtFiber9StateAt 14, mtFiber9StateAt 15]

theorem mtFiber9ReverseRow_1_ok :
    mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber9Chunk0_ok
  change (mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 0) &&
    mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber9ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber9StateAt 0) (mtFiber9StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber9StateAt 0) (mtFiber9StateAt 1)
    (mtFiber9RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber9Key mtFiber9Expected
        (mtFiber9RowAt 1) (by decide) mtFiber9ReverseRow_1_ok
      simpa [mtFiber9StateAt, mtFiber9RowAt, mtFiber9Rows, listGetD, directRow] using h)

theorem mtFiber9ReverseRow_2_ok :
    mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber9Chunk1_ok
  change (mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 2) &&
    mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber9ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber9StateAt 1) (mtFiber9StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber9StateAt 1) (mtFiber9StateAt 2)
    (mtFiber9RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber9Key mtFiber9Expected
        (mtFiber9RowAt 2) (by decide) mtFiber9ReverseRow_2_ok
      simpa [mtFiber9StateAt, mtFiber9RowAt, mtFiber9Rows, listGetD, directRow] using h)

theorem mtFiber9ReverseRow_3_ok :
    mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber9Chunk1_ok
  change (mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 2) &&
    mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber9ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber9StateAt 0) (mtFiber9StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber9StateAt 0) (mtFiber9StateAt 3)
    (mtFiber9RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber9Key mtFiber9Expected
        (mtFiber9RowAt 3) (by decide) mtFiber9ReverseRow_3_ok
      simpa [mtFiber9StateAt, mtFiber9RowAt, mtFiber9Rows, listGetD, directRow] using h)

theorem mtFiber9ReverseRow_4_ok :
    mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber9Chunk2_ok
  change (mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 4) &&
    mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber9ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber9StateAt 0) (mtFiber9StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber9StateAt 0) (mtFiber9StateAt 4)
    (mtFiber9RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber9Key mtFiber9Expected
        (mtFiber9RowAt 4) (by decide) mtFiber9ReverseRow_4_ok
      simpa [mtFiber9StateAt, mtFiber9RowAt, mtFiber9Rows, listGetD, directRow] using h)

theorem mtFiber9ReverseRow_5_ok :
    mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber9Chunk2_ok
  change (mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 4) &&
    mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber9ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber9StateAt 1) (mtFiber9StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber9StateAt 1) (mtFiber9StateAt 5)
    (mtFiber9RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber9Key mtFiber9Expected
        (mtFiber9RowAt 5) (by decide) mtFiber9ReverseRow_5_ok
      simpa [mtFiber9StateAt, mtFiber9RowAt, mtFiber9Rows, listGetD, directRow] using h)

theorem mtFiber9ReverseRow_6_ok :
    mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber9Chunk3_ok
  change (mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 6) &&
    mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber9ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber9StateAt 2) (mtFiber9StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber9StateAt 2) (mtFiber9StateAt 6)
    (mtFiber9RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber9Key mtFiber9Expected
        (mtFiber9RowAt 6) (by decide) mtFiber9ReverseRow_6_ok
      simpa [mtFiber9StateAt, mtFiber9RowAt, mtFiber9Rows, listGetD, directRow] using h)

theorem mtFiber9ReverseRow_7_ok :
    mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber9Chunk3_ok
  change (mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 6) &&
    mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber9ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber9StateAt 3) (mtFiber9StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber9StateAt 3) (mtFiber9StateAt 7)
    (mtFiber9RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber9Key mtFiber9Expected
        (mtFiber9RowAt 7) (by decide) mtFiber9ReverseRow_7_ok
      simpa [mtFiber9StateAt, mtFiber9RowAt, mtFiber9Rows, listGetD, directRow] using h)

theorem mtFiber9ReverseRow_8_ok :
    mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber9Chunk4_ok
  change (mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 8) &&
    mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber9ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber9StateAt 0) (mtFiber9StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber9StateAt 0) (mtFiber9StateAt 8)
    (mtFiber9RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber9Key mtFiber9Expected
        (mtFiber9RowAt 8) (by decide) mtFiber9ReverseRow_8_ok
      simpa [mtFiber9StateAt, mtFiber9RowAt, mtFiber9Rows, listGetD, directRow] using h)

theorem mtFiber9ReverseRow_9_ok :
    mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber9Chunk4_ok
  change (mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 8) &&
    mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber9ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber9StateAt 1) (mtFiber9StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber9StateAt 1) (mtFiber9StateAt 9)
    (mtFiber9RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber9Key mtFiber9Expected
        (mtFiber9RowAt 9) (by decide) mtFiber9ReverseRow_9_ok
      simpa [mtFiber9StateAt, mtFiber9RowAt, mtFiber9Rows, listGetD, directRow] using h)

theorem mtFiber9ReverseRow_10_ok :
    mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber9Chunk5_ok
  change (mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 10) &&
    mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber9ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber9StateAt 2) (mtFiber9StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber9StateAt 2) (mtFiber9StateAt 10)
    (mtFiber9RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber9Key mtFiber9Expected
        (mtFiber9RowAt 10) (by decide) mtFiber9ReverseRow_10_ok
      simpa [mtFiber9StateAt, mtFiber9RowAt, mtFiber9Rows, listGetD, directRow] using h)

theorem mtFiber9ReverseRow_11_ok :
    mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber9Chunk5_ok
  change (mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 10) &&
    mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber9ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber9StateAt 3) (mtFiber9StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber9StateAt 3) (mtFiber9StateAt 11)
    (mtFiber9RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber9Key mtFiber9Expected
        (mtFiber9RowAt 11) (by decide) mtFiber9ReverseRow_11_ok
      simpa [mtFiber9StateAt, mtFiber9RowAt, mtFiber9Rows, listGetD, directRow] using h)

theorem mtFiber9ReverseRow_12_ok :
    mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber9Chunk6_ok
  change (mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 12) &&
    mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber9ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber9StateAt 4) (mtFiber9StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber9StateAt 4) (mtFiber9StateAt 12)
    (mtFiber9RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber9Key mtFiber9Expected
        (mtFiber9RowAt 12) (by decide) mtFiber9ReverseRow_12_ok
      simpa [mtFiber9StateAt, mtFiber9RowAt, mtFiber9Rows, listGetD, directRow] using h)

theorem mtFiber9ReverseRow_13_ok :
    mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber9Chunk6_ok
  change (mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 12) &&
    mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber9ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber9StateAt 5) (mtFiber9StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber9StateAt 5) (mtFiber9StateAt 13)
    (mtFiber9RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber9Key mtFiber9Expected
        (mtFiber9RowAt 13) (by decide) mtFiber9ReverseRow_13_ok
      simpa [mtFiber9StateAt, mtFiber9RowAt, mtFiber9Rows, listGetD, directRow] using h)

theorem mtFiber9ReverseRow_14_ok :
    mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber9Chunk7_ok
  change (mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 14) &&
    mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber9ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber9StateAt 6) (mtFiber9StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber9StateAt 6) (mtFiber9StateAt 14)
    (mtFiber9RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber9Key mtFiber9Expected
        (mtFiber9RowAt 14) (by decide) mtFiber9ReverseRow_14_ok
      simpa [mtFiber9StateAt, mtFiber9RowAt, mtFiber9Rows, listGetD, directRow] using h)

theorem mtFiber9ReverseRow_15_ok :
    mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber9Chunk7_ok
  change (mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 14) &&
    mtRowReverseValid mtFiber9Key mtFiber9Expected (mtFiber9RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber9ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber9StateAt 7) (mtFiber9StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber9StateAt 7) (mtFiber9StateAt 15)
    (mtFiber9RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber9Key mtFiber9Expected
        (mtFiber9RowAt 15) (by decide) mtFiber9ReverseRow_15_ok
      simpa [mtFiber9StateAt, mtFiber9RowAt, mtFiber9Rows, listGetD, directRow] using h)

theorem mtFiber9State0_in_close :
    mtFiber9StateAt 0 ∈ closeChainFiber mtWord mtFiber9DirectStates mtFiber9DirectStates.length [mtFiber9StateAt 0] := by
  change mtFiber9StateAt 0 ∈ closeChainFiber mtWord mtFiber9DirectStates 16 [mtFiber9StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber9DirectStates 0 16 [mtFiber9StateAt 0] (mtFiber9StateAt 0) (by simp [closeChainFiber])

theorem mtFiber9State1_in_close :
    mtFiber9StateAt 1 ∈ closeChainFiber mtWord mtFiber9DirectStates mtFiber9DirectStates.length [mtFiber9StateAt 0] := by
  have h0 : mtFiber9StateAt 0 ∈ closeChainFiber mtWord mtFiber9DirectStates 0 [mtFiber9StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber9StateAt 1 ∈ closeChainFiber mtWord mtFiber9DirectStates 1 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 0 [mtFiber9StateAt 0]
      (mtFiber9StateAt 0) (mtFiber9StateAt 1) (by decide) h0 (by decide)
      mtFiber9ReverseSingleStep1
  change mtFiber9StateAt 1 ∈ closeChainFiber mtWord mtFiber9DirectStates (1 + 15) [mtFiber9StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber9DirectStates 1 15 [mtFiber9StateAt 0] (mtFiber9StateAt 1) h1

theorem mtFiber9State2_in_close :
    mtFiber9StateAt 2 ∈ closeChainFiber mtWord mtFiber9DirectStates mtFiber9DirectStates.length [mtFiber9StateAt 0] := by
  have h0 : mtFiber9StateAt 0 ∈ closeChainFiber mtWord mtFiber9DirectStates 0 [mtFiber9StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber9StateAt 1 ∈ closeChainFiber mtWord mtFiber9DirectStates 1 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 0 [mtFiber9StateAt 0]
      (mtFiber9StateAt 0) (mtFiber9StateAt 1) (by decide) h0 (by decide)
      mtFiber9ReverseSingleStep1
  have h2 : mtFiber9StateAt 2 ∈ closeChainFiber mtWord mtFiber9DirectStates 2 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 1 [mtFiber9StateAt 0]
      (mtFiber9StateAt 1) (mtFiber9StateAt 2) (by decide) h1 (by decide)
      mtFiber9ReverseSingleStep2
  change mtFiber9StateAt 2 ∈ closeChainFiber mtWord mtFiber9DirectStates (2 + 14) [mtFiber9StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber9DirectStates 2 14 [mtFiber9StateAt 0] (mtFiber9StateAt 2) h2

theorem mtFiber9State3_in_close :
    mtFiber9StateAt 3 ∈ closeChainFiber mtWord mtFiber9DirectStates mtFiber9DirectStates.length [mtFiber9StateAt 0] := by
  have h0 : mtFiber9StateAt 0 ∈ closeChainFiber mtWord mtFiber9DirectStates 0 [mtFiber9StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber9StateAt 3 ∈ closeChainFiber mtWord mtFiber9DirectStates 1 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 0 [mtFiber9StateAt 0]
      (mtFiber9StateAt 0) (mtFiber9StateAt 3) (by decide) h0 (by decide)
      mtFiber9ReverseSingleStep3
  change mtFiber9StateAt 3 ∈ closeChainFiber mtWord mtFiber9DirectStates (1 + 15) [mtFiber9StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber9DirectStates 1 15 [mtFiber9StateAt 0] (mtFiber9StateAt 3) h1

theorem mtFiber9State4_in_close :
    mtFiber9StateAt 4 ∈ closeChainFiber mtWord mtFiber9DirectStates mtFiber9DirectStates.length [mtFiber9StateAt 0] := by
  have h0 : mtFiber9StateAt 0 ∈ closeChainFiber mtWord mtFiber9DirectStates 0 [mtFiber9StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber9StateAt 4 ∈ closeChainFiber mtWord mtFiber9DirectStates 1 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 0 [mtFiber9StateAt 0]
      (mtFiber9StateAt 0) (mtFiber9StateAt 4) (by decide) h0 (by decide)
      mtFiber9ReverseSingleStep4
  change mtFiber9StateAt 4 ∈ closeChainFiber mtWord mtFiber9DirectStates (1 + 15) [mtFiber9StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber9DirectStates 1 15 [mtFiber9StateAt 0] (mtFiber9StateAt 4) h1

theorem mtFiber9State5_in_close :
    mtFiber9StateAt 5 ∈ closeChainFiber mtWord mtFiber9DirectStates mtFiber9DirectStates.length [mtFiber9StateAt 0] := by
  have h0 : mtFiber9StateAt 0 ∈ closeChainFiber mtWord mtFiber9DirectStates 0 [mtFiber9StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber9StateAt 1 ∈ closeChainFiber mtWord mtFiber9DirectStates 1 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 0 [mtFiber9StateAt 0]
      (mtFiber9StateAt 0) (mtFiber9StateAt 1) (by decide) h0 (by decide)
      mtFiber9ReverseSingleStep1
  have h2 : mtFiber9StateAt 5 ∈ closeChainFiber mtWord mtFiber9DirectStates 2 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 1 [mtFiber9StateAt 0]
      (mtFiber9StateAt 1) (mtFiber9StateAt 5) (by decide) h1 (by decide)
      mtFiber9ReverseSingleStep5
  change mtFiber9StateAt 5 ∈ closeChainFiber mtWord mtFiber9DirectStates (2 + 14) [mtFiber9StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber9DirectStates 2 14 [mtFiber9StateAt 0] (mtFiber9StateAt 5) h2

theorem mtFiber9State6_in_close :
    mtFiber9StateAt 6 ∈ closeChainFiber mtWord mtFiber9DirectStates mtFiber9DirectStates.length [mtFiber9StateAt 0] := by
  have h0 : mtFiber9StateAt 0 ∈ closeChainFiber mtWord mtFiber9DirectStates 0 [mtFiber9StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber9StateAt 1 ∈ closeChainFiber mtWord mtFiber9DirectStates 1 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 0 [mtFiber9StateAt 0]
      (mtFiber9StateAt 0) (mtFiber9StateAt 1) (by decide) h0 (by decide)
      mtFiber9ReverseSingleStep1
  have h2 : mtFiber9StateAt 2 ∈ closeChainFiber mtWord mtFiber9DirectStates 2 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 1 [mtFiber9StateAt 0]
      (mtFiber9StateAt 1) (mtFiber9StateAt 2) (by decide) h1 (by decide)
      mtFiber9ReverseSingleStep2
  have h3 : mtFiber9StateAt 6 ∈ closeChainFiber mtWord mtFiber9DirectStates 3 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 2 [mtFiber9StateAt 0]
      (mtFiber9StateAt 2) (mtFiber9StateAt 6) (by decide) h2 (by decide)
      mtFiber9ReverseSingleStep6
  change mtFiber9StateAt 6 ∈ closeChainFiber mtWord mtFiber9DirectStates (3 + 13) [mtFiber9StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber9DirectStates 3 13 [mtFiber9StateAt 0] (mtFiber9StateAt 6) h3

theorem mtFiber9State7_in_close :
    mtFiber9StateAt 7 ∈ closeChainFiber mtWord mtFiber9DirectStates mtFiber9DirectStates.length [mtFiber9StateAt 0] := by
  have h0 : mtFiber9StateAt 0 ∈ closeChainFiber mtWord mtFiber9DirectStates 0 [mtFiber9StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber9StateAt 3 ∈ closeChainFiber mtWord mtFiber9DirectStates 1 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 0 [mtFiber9StateAt 0]
      (mtFiber9StateAt 0) (mtFiber9StateAt 3) (by decide) h0 (by decide)
      mtFiber9ReverseSingleStep3
  have h2 : mtFiber9StateAt 7 ∈ closeChainFiber mtWord mtFiber9DirectStates 2 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 1 [mtFiber9StateAt 0]
      (mtFiber9StateAt 3) (mtFiber9StateAt 7) (by decide) h1 (by decide)
      mtFiber9ReverseSingleStep7
  change mtFiber9StateAt 7 ∈ closeChainFiber mtWord mtFiber9DirectStates (2 + 14) [mtFiber9StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber9DirectStates 2 14 [mtFiber9StateAt 0] (mtFiber9StateAt 7) h2

theorem mtFiber9State8_in_close :
    mtFiber9StateAt 8 ∈ closeChainFiber mtWord mtFiber9DirectStates mtFiber9DirectStates.length [mtFiber9StateAt 0] := by
  have h0 : mtFiber9StateAt 0 ∈ closeChainFiber mtWord mtFiber9DirectStates 0 [mtFiber9StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber9StateAt 8 ∈ closeChainFiber mtWord mtFiber9DirectStates 1 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 0 [mtFiber9StateAt 0]
      (mtFiber9StateAt 0) (mtFiber9StateAt 8) (by decide) h0 (by decide)
      mtFiber9ReverseSingleStep8
  change mtFiber9StateAt 8 ∈ closeChainFiber mtWord mtFiber9DirectStates (1 + 15) [mtFiber9StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber9DirectStates 1 15 [mtFiber9StateAt 0] (mtFiber9StateAt 8) h1

theorem mtFiber9State9_in_close :
    mtFiber9StateAt 9 ∈ closeChainFiber mtWord mtFiber9DirectStates mtFiber9DirectStates.length [mtFiber9StateAt 0] := by
  have h0 : mtFiber9StateAt 0 ∈ closeChainFiber mtWord mtFiber9DirectStates 0 [mtFiber9StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber9StateAt 1 ∈ closeChainFiber mtWord mtFiber9DirectStates 1 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 0 [mtFiber9StateAt 0]
      (mtFiber9StateAt 0) (mtFiber9StateAt 1) (by decide) h0 (by decide)
      mtFiber9ReverseSingleStep1
  have h2 : mtFiber9StateAt 9 ∈ closeChainFiber mtWord mtFiber9DirectStates 2 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 1 [mtFiber9StateAt 0]
      (mtFiber9StateAt 1) (mtFiber9StateAt 9) (by decide) h1 (by decide)
      mtFiber9ReverseSingleStep9
  change mtFiber9StateAt 9 ∈ closeChainFiber mtWord mtFiber9DirectStates (2 + 14) [mtFiber9StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber9DirectStates 2 14 [mtFiber9StateAt 0] (mtFiber9StateAt 9) h2

theorem mtFiber9State10_in_close :
    mtFiber9StateAt 10 ∈ closeChainFiber mtWord mtFiber9DirectStates mtFiber9DirectStates.length [mtFiber9StateAt 0] := by
  have h0 : mtFiber9StateAt 0 ∈ closeChainFiber mtWord mtFiber9DirectStates 0 [mtFiber9StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber9StateAt 1 ∈ closeChainFiber mtWord mtFiber9DirectStates 1 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 0 [mtFiber9StateAt 0]
      (mtFiber9StateAt 0) (mtFiber9StateAt 1) (by decide) h0 (by decide)
      mtFiber9ReverseSingleStep1
  have h2 : mtFiber9StateAt 2 ∈ closeChainFiber mtWord mtFiber9DirectStates 2 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 1 [mtFiber9StateAt 0]
      (mtFiber9StateAt 1) (mtFiber9StateAt 2) (by decide) h1 (by decide)
      mtFiber9ReverseSingleStep2
  have h3 : mtFiber9StateAt 10 ∈ closeChainFiber mtWord mtFiber9DirectStates 3 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 2 [mtFiber9StateAt 0]
      (mtFiber9StateAt 2) (mtFiber9StateAt 10) (by decide) h2 (by decide)
      mtFiber9ReverseSingleStep10
  change mtFiber9StateAt 10 ∈ closeChainFiber mtWord mtFiber9DirectStates (3 + 13) [mtFiber9StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber9DirectStates 3 13 [mtFiber9StateAt 0] (mtFiber9StateAt 10) h3

theorem mtFiber9State11_in_close :
    mtFiber9StateAt 11 ∈ closeChainFiber mtWord mtFiber9DirectStates mtFiber9DirectStates.length [mtFiber9StateAt 0] := by
  have h0 : mtFiber9StateAt 0 ∈ closeChainFiber mtWord mtFiber9DirectStates 0 [mtFiber9StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber9StateAt 3 ∈ closeChainFiber mtWord mtFiber9DirectStates 1 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 0 [mtFiber9StateAt 0]
      (mtFiber9StateAt 0) (mtFiber9StateAt 3) (by decide) h0 (by decide)
      mtFiber9ReverseSingleStep3
  have h2 : mtFiber9StateAt 11 ∈ closeChainFiber mtWord mtFiber9DirectStates 2 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 1 [mtFiber9StateAt 0]
      (mtFiber9StateAt 3) (mtFiber9StateAt 11) (by decide) h1 (by decide)
      mtFiber9ReverseSingleStep11
  change mtFiber9StateAt 11 ∈ closeChainFiber mtWord mtFiber9DirectStates (2 + 14) [mtFiber9StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber9DirectStates 2 14 [mtFiber9StateAt 0] (mtFiber9StateAt 11) h2

theorem mtFiber9State12_in_close :
    mtFiber9StateAt 12 ∈ closeChainFiber mtWord mtFiber9DirectStates mtFiber9DirectStates.length [mtFiber9StateAt 0] := by
  have h0 : mtFiber9StateAt 0 ∈ closeChainFiber mtWord mtFiber9DirectStates 0 [mtFiber9StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber9StateAt 4 ∈ closeChainFiber mtWord mtFiber9DirectStates 1 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 0 [mtFiber9StateAt 0]
      (mtFiber9StateAt 0) (mtFiber9StateAt 4) (by decide) h0 (by decide)
      mtFiber9ReverseSingleStep4
  have h2 : mtFiber9StateAt 12 ∈ closeChainFiber mtWord mtFiber9DirectStates 2 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 1 [mtFiber9StateAt 0]
      (mtFiber9StateAt 4) (mtFiber9StateAt 12) (by decide) h1 (by decide)
      mtFiber9ReverseSingleStep12
  change mtFiber9StateAt 12 ∈ closeChainFiber mtWord mtFiber9DirectStates (2 + 14) [mtFiber9StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber9DirectStates 2 14 [mtFiber9StateAt 0] (mtFiber9StateAt 12) h2

theorem mtFiber9State13_in_close :
    mtFiber9StateAt 13 ∈ closeChainFiber mtWord mtFiber9DirectStates mtFiber9DirectStates.length [mtFiber9StateAt 0] := by
  have h0 : mtFiber9StateAt 0 ∈ closeChainFiber mtWord mtFiber9DirectStates 0 [mtFiber9StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber9StateAt 1 ∈ closeChainFiber mtWord mtFiber9DirectStates 1 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 0 [mtFiber9StateAt 0]
      (mtFiber9StateAt 0) (mtFiber9StateAt 1) (by decide) h0 (by decide)
      mtFiber9ReverseSingleStep1
  have h2 : mtFiber9StateAt 5 ∈ closeChainFiber mtWord mtFiber9DirectStates 2 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 1 [mtFiber9StateAt 0]
      (mtFiber9StateAt 1) (mtFiber9StateAt 5) (by decide) h1 (by decide)
      mtFiber9ReverseSingleStep5
  have h3 : mtFiber9StateAt 13 ∈ closeChainFiber mtWord mtFiber9DirectStates 3 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 2 [mtFiber9StateAt 0]
      (mtFiber9StateAt 5) (mtFiber9StateAt 13) (by decide) h2 (by decide)
      mtFiber9ReverseSingleStep13
  change mtFiber9StateAt 13 ∈ closeChainFiber mtWord mtFiber9DirectStates (3 + 13) [mtFiber9StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber9DirectStates 3 13 [mtFiber9StateAt 0] (mtFiber9StateAt 13) h3

theorem mtFiber9State14_in_close :
    mtFiber9StateAt 14 ∈ closeChainFiber mtWord mtFiber9DirectStates mtFiber9DirectStates.length [mtFiber9StateAt 0] := by
  have h0 : mtFiber9StateAt 0 ∈ closeChainFiber mtWord mtFiber9DirectStates 0 [mtFiber9StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber9StateAt 1 ∈ closeChainFiber mtWord mtFiber9DirectStates 1 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 0 [mtFiber9StateAt 0]
      (mtFiber9StateAt 0) (mtFiber9StateAt 1) (by decide) h0 (by decide)
      mtFiber9ReverseSingleStep1
  have h2 : mtFiber9StateAt 2 ∈ closeChainFiber mtWord mtFiber9DirectStates 2 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 1 [mtFiber9StateAt 0]
      (mtFiber9StateAt 1) (mtFiber9StateAt 2) (by decide) h1 (by decide)
      mtFiber9ReverseSingleStep2
  have h3 : mtFiber9StateAt 6 ∈ closeChainFiber mtWord mtFiber9DirectStates 3 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 2 [mtFiber9StateAt 0]
      (mtFiber9StateAt 2) (mtFiber9StateAt 6) (by decide) h2 (by decide)
      mtFiber9ReverseSingleStep6
  have h4 : mtFiber9StateAt 14 ∈ closeChainFiber mtWord mtFiber9DirectStates 4 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 3 [mtFiber9StateAt 0]
      (mtFiber9StateAt 6) (mtFiber9StateAt 14) (by decide) h3 (by decide)
      mtFiber9ReverseSingleStep14
  change mtFiber9StateAt 14 ∈ closeChainFiber mtWord mtFiber9DirectStates (4 + 12) [mtFiber9StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber9DirectStates 4 12 [mtFiber9StateAt 0] (mtFiber9StateAt 14) h4

theorem mtFiber9State15_in_close :
    mtFiber9StateAt 15 ∈ closeChainFiber mtWord mtFiber9DirectStates mtFiber9DirectStates.length [mtFiber9StateAt 0] := by
  have h0 : mtFiber9StateAt 0 ∈ closeChainFiber mtWord mtFiber9DirectStates 0 [mtFiber9StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber9StateAt 3 ∈ closeChainFiber mtWord mtFiber9DirectStates 1 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 0 [mtFiber9StateAt 0]
      (mtFiber9StateAt 0) (mtFiber9StateAt 3) (by decide) h0 (by decide)
      mtFiber9ReverseSingleStep3
  have h2 : mtFiber9StateAt 7 ∈ closeChainFiber mtWord mtFiber9DirectStates 2 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 1 [mtFiber9StateAt 0]
      (mtFiber9StateAt 3) (mtFiber9StateAt 7) (by decide) h1 (by decide)
      mtFiber9ReverseSingleStep7
  have h3 : mtFiber9StateAt 15 ∈ closeChainFiber mtWord mtFiber9DirectStates 3 [mtFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber9DirectStates 2 [mtFiber9StateAt 0]
      (mtFiber9StateAt 7) (mtFiber9StateAt 15) (by decide) h2 (by decide)
      mtFiber9ReverseSingleStep15
  change mtFiber9StateAt 15 ∈ closeChainFiber mtWord mtFiber9DirectStates (3 + 13) [mtFiber9StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber9DirectStates 3 13 [mtFiber9StateAt 0] (mtFiber9StateAt 15) h3

theorem mtFiber9DirectConnected :
    chainFiberConnected mtWord mtFiber9DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber9DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber9State0_in_close
  · subst state
    exact mtFiber9State1_in_close
  · subst state
    exact mtFiber9State2_in_close
  · subst state
    exact mtFiber9State3_in_close
  · subst state
    exact mtFiber9State4_in_close
  · subst state
    exact mtFiber9State5_in_close
  · subst state
    exact mtFiber9State6_in_close
  · subst state
    exact mtFiber9State7_in_close
  · subst state
    exact mtFiber9State8_in_close
  · subst state
    exact mtFiber9State9_in_close
  · subst state
    exact mtFiber9State10_in_close
  · subst state
    exact mtFiber9State11_in_close
  · subst state
    exact mtFiber9State12_in_close
  · subst state
    exact mtFiber9State13_in_close
  · subst state
    exact mtFiber9State14_in_close
  · subst state
    exact mtFiber9State15_in_close
  · cases h
def mtFiber16StateAt (i : Nat) : List TauState :=
  directStates (mtFiber16RowAt i).sourceLeft (mtFiber16RowAt i).sourceRight

def mtFiber16DirectStates : List (List TauState) :=
  [mtFiber16StateAt 0, mtFiber16StateAt 1, mtFiber16StateAt 2, mtFiber16StateAt 3, mtFiber16StateAt 4, mtFiber16StateAt 5, mtFiber16StateAt 6, mtFiber16StateAt 7, mtFiber16StateAt 8, mtFiber16StateAt 9, mtFiber16StateAt 10, mtFiber16StateAt 11, mtFiber16StateAt 12, mtFiber16StateAt 13, mtFiber16StateAt 14, mtFiber16StateAt 15]

theorem mtFiber16ReverseRow_1_ok :
    mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber16Chunk0_ok
  change (mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 0) &&
    mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber16ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber16StateAt 0) (mtFiber16StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber16StateAt 0) (mtFiber16StateAt 1)
    (mtFiber16RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber16Key mtFiber16Expected
        (mtFiber16RowAt 1) (by decide) mtFiber16ReverseRow_1_ok
      simpa [mtFiber16StateAt, mtFiber16RowAt, mtFiber16Rows, listGetD, directRow] using h)

theorem mtFiber16ReverseRow_2_ok :
    mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber16Chunk1_ok
  change (mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 2) &&
    mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber16ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber16StateAt 0) (mtFiber16StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber16StateAt 0) (mtFiber16StateAt 2)
    (mtFiber16RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber16Key mtFiber16Expected
        (mtFiber16RowAt 2) (by decide) mtFiber16ReverseRow_2_ok
      simpa [mtFiber16StateAt, mtFiber16RowAt, mtFiber16Rows, listGetD, directRow] using h)

theorem mtFiber16ReverseRow_3_ok :
    mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber16Chunk1_ok
  change (mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 2) &&
    mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber16ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber16StateAt 1) (mtFiber16StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber16StateAt 1) (mtFiber16StateAt 3)
    (mtFiber16RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber16Key mtFiber16Expected
        (mtFiber16RowAt 3) (by decide) mtFiber16ReverseRow_3_ok
      simpa [mtFiber16StateAt, mtFiber16RowAt, mtFiber16Rows, listGetD, directRow] using h)

theorem mtFiber16ReverseRow_4_ok :
    mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber16Chunk2_ok
  change (mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 4) &&
    mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber16ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber16StateAt 0) (mtFiber16StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber16StateAt 0) (mtFiber16StateAt 4)
    (mtFiber16RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber16Key mtFiber16Expected
        (mtFiber16RowAt 4) (by decide) mtFiber16ReverseRow_4_ok
      simpa [mtFiber16StateAt, mtFiber16RowAt, mtFiber16Rows, listGetD, directRow] using h)

theorem mtFiber16ReverseRow_5_ok :
    mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber16Chunk2_ok
  change (mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 4) &&
    mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber16ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber16StateAt 1) (mtFiber16StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber16StateAt 1) (mtFiber16StateAt 5)
    (mtFiber16RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber16Key mtFiber16Expected
        (mtFiber16RowAt 5) (by decide) mtFiber16ReverseRow_5_ok
      simpa [mtFiber16StateAt, mtFiber16RowAt, mtFiber16Rows, listGetD, directRow] using h)

theorem mtFiber16ReverseRow_6_ok :
    mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber16Chunk3_ok
  change (mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 6) &&
    mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber16ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber16StateAt 2) (mtFiber16StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber16StateAt 2) (mtFiber16StateAt 6)
    (mtFiber16RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber16Key mtFiber16Expected
        (mtFiber16RowAt 6) (by decide) mtFiber16ReverseRow_6_ok
      simpa [mtFiber16StateAt, mtFiber16RowAt, mtFiber16Rows, listGetD, directRow] using h)

theorem mtFiber16ReverseRow_7_ok :
    mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber16Chunk3_ok
  change (mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 6) &&
    mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber16ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber16StateAt 3) (mtFiber16StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber16StateAt 3) (mtFiber16StateAt 7)
    (mtFiber16RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber16Key mtFiber16Expected
        (mtFiber16RowAt 7) (by decide) mtFiber16ReverseRow_7_ok
      simpa [mtFiber16StateAt, mtFiber16RowAt, mtFiber16Rows, listGetD, directRow] using h)

theorem mtFiber16ReverseRow_8_ok :
    mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber16Chunk4_ok
  change (mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 8) &&
    mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber16ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber16StateAt 0) (mtFiber16StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber16StateAt 0) (mtFiber16StateAt 8)
    (mtFiber16RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber16Key mtFiber16Expected
        (mtFiber16RowAt 8) (by decide) mtFiber16ReverseRow_8_ok
      simpa [mtFiber16StateAt, mtFiber16RowAt, mtFiber16Rows, listGetD, directRow] using h)

theorem mtFiber16ReverseRow_9_ok :
    mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber16Chunk4_ok
  change (mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 8) &&
    mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber16ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber16StateAt 1) (mtFiber16StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber16StateAt 1) (mtFiber16StateAt 9)
    (mtFiber16RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber16Key mtFiber16Expected
        (mtFiber16RowAt 9) (by decide) mtFiber16ReverseRow_9_ok
      simpa [mtFiber16StateAt, mtFiber16RowAt, mtFiber16Rows, listGetD, directRow] using h)

theorem mtFiber16ReverseRow_10_ok :
    mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber16Chunk5_ok
  change (mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 10) &&
    mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber16ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber16StateAt 2) (mtFiber16StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber16StateAt 2) (mtFiber16StateAt 10)
    (mtFiber16RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber16Key mtFiber16Expected
        (mtFiber16RowAt 10) (by decide) mtFiber16ReverseRow_10_ok
      simpa [mtFiber16StateAt, mtFiber16RowAt, mtFiber16Rows, listGetD, directRow] using h)

theorem mtFiber16ReverseRow_11_ok :
    mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber16Chunk5_ok
  change (mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 10) &&
    mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber16ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber16StateAt 3) (mtFiber16StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber16StateAt 3) (mtFiber16StateAt 11)
    (mtFiber16RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber16Key mtFiber16Expected
        (mtFiber16RowAt 11) (by decide) mtFiber16ReverseRow_11_ok
      simpa [mtFiber16StateAt, mtFiber16RowAt, mtFiber16Rows, listGetD, directRow] using h)

theorem mtFiber16ReverseRow_12_ok :
    mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber16Chunk6_ok
  change (mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 12) &&
    mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber16ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber16StateAt 4) (mtFiber16StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber16StateAt 4) (mtFiber16StateAt 12)
    (mtFiber16RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber16Key mtFiber16Expected
        (mtFiber16RowAt 12) (by decide) mtFiber16ReverseRow_12_ok
      simpa [mtFiber16StateAt, mtFiber16RowAt, mtFiber16Rows, listGetD, directRow] using h)

theorem mtFiber16ReverseRow_13_ok :
    mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber16Chunk6_ok
  change (mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 12) &&
    mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber16ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber16StateAt 5) (mtFiber16StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber16StateAt 5) (mtFiber16StateAt 13)
    (mtFiber16RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber16Key mtFiber16Expected
        (mtFiber16RowAt 13) (by decide) mtFiber16ReverseRow_13_ok
      simpa [mtFiber16StateAt, mtFiber16RowAt, mtFiber16Rows, listGetD, directRow] using h)

theorem mtFiber16ReverseRow_14_ok :
    mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber16Chunk7_ok
  change (mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 14) &&
    mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber16ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber16StateAt 6) (mtFiber16StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber16StateAt 6) (mtFiber16StateAt 14)
    (mtFiber16RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber16Key mtFiber16Expected
        (mtFiber16RowAt 14) (by decide) mtFiber16ReverseRow_14_ok
      simpa [mtFiber16StateAt, mtFiber16RowAt, mtFiber16Rows, listGetD, directRow] using h)

theorem mtFiber16ReverseRow_15_ok :
    mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber16Chunk7_ok
  change (mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 14) &&
    mtRowReverseValid mtFiber16Key mtFiber16Expected (mtFiber16RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber16ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber16StateAt 7) (mtFiber16StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber16StateAt 7) (mtFiber16StateAt 15)
    (mtFiber16RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber16Key mtFiber16Expected
        (mtFiber16RowAt 15) (by decide) mtFiber16ReverseRow_15_ok
      simpa [mtFiber16StateAt, mtFiber16RowAt, mtFiber16Rows, listGetD, directRow] using h)

theorem mtFiber16State0_in_close :
    mtFiber16StateAt 0 ∈ closeChainFiber mtWord mtFiber16DirectStates mtFiber16DirectStates.length [mtFiber16StateAt 0] := by
  change mtFiber16StateAt 0 ∈ closeChainFiber mtWord mtFiber16DirectStates 16 [mtFiber16StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber16DirectStates 0 16 [mtFiber16StateAt 0] (mtFiber16StateAt 0) (by simp [closeChainFiber])

theorem mtFiber16State1_in_close :
    mtFiber16StateAt 1 ∈ closeChainFiber mtWord mtFiber16DirectStates mtFiber16DirectStates.length [mtFiber16StateAt 0] := by
  have h0 : mtFiber16StateAt 0 ∈ closeChainFiber mtWord mtFiber16DirectStates 0 [mtFiber16StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber16StateAt 1 ∈ closeChainFiber mtWord mtFiber16DirectStates 1 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 0 [mtFiber16StateAt 0]
      (mtFiber16StateAt 0) (mtFiber16StateAt 1) (by decide) h0 (by decide)
      mtFiber16ReverseSingleStep1
  change mtFiber16StateAt 1 ∈ closeChainFiber mtWord mtFiber16DirectStates (1 + 15) [mtFiber16StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber16DirectStates 1 15 [mtFiber16StateAt 0] (mtFiber16StateAt 1) h1

theorem mtFiber16State2_in_close :
    mtFiber16StateAt 2 ∈ closeChainFiber mtWord mtFiber16DirectStates mtFiber16DirectStates.length [mtFiber16StateAt 0] := by
  have h0 : mtFiber16StateAt 0 ∈ closeChainFiber mtWord mtFiber16DirectStates 0 [mtFiber16StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber16StateAt 2 ∈ closeChainFiber mtWord mtFiber16DirectStates 1 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 0 [mtFiber16StateAt 0]
      (mtFiber16StateAt 0) (mtFiber16StateAt 2) (by decide) h0 (by decide)
      mtFiber16ReverseSingleStep2
  change mtFiber16StateAt 2 ∈ closeChainFiber mtWord mtFiber16DirectStates (1 + 15) [mtFiber16StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber16DirectStates 1 15 [mtFiber16StateAt 0] (mtFiber16StateAt 2) h1

theorem mtFiber16State3_in_close :
    mtFiber16StateAt 3 ∈ closeChainFiber mtWord mtFiber16DirectStates mtFiber16DirectStates.length [mtFiber16StateAt 0] := by
  have h0 : mtFiber16StateAt 0 ∈ closeChainFiber mtWord mtFiber16DirectStates 0 [mtFiber16StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber16StateAt 1 ∈ closeChainFiber mtWord mtFiber16DirectStates 1 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 0 [mtFiber16StateAt 0]
      (mtFiber16StateAt 0) (mtFiber16StateAt 1) (by decide) h0 (by decide)
      mtFiber16ReverseSingleStep1
  have h2 : mtFiber16StateAt 3 ∈ closeChainFiber mtWord mtFiber16DirectStates 2 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 1 [mtFiber16StateAt 0]
      (mtFiber16StateAt 1) (mtFiber16StateAt 3) (by decide) h1 (by decide)
      mtFiber16ReverseSingleStep3
  change mtFiber16StateAt 3 ∈ closeChainFiber mtWord mtFiber16DirectStates (2 + 14) [mtFiber16StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber16DirectStates 2 14 [mtFiber16StateAt 0] (mtFiber16StateAt 3) h2

theorem mtFiber16State4_in_close :
    mtFiber16StateAt 4 ∈ closeChainFiber mtWord mtFiber16DirectStates mtFiber16DirectStates.length [mtFiber16StateAt 0] := by
  have h0 : mtFiber16StateAt 0 ∈ closeChainFiber mtWord mtFiber16DirectStates 0 [mtFiber16StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber16StateAt 4 ∈ closeChainFiber mtWord mtFiber16DirectStates 1 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 0 [mtFiber16StateAt 0]
      (mtFiber16StateAt 0) (mtFiber16StateAt 4) (by decide) h0 (by decide)
      mtFiber16ReverseSingleStep4
  change mtFiber16StateAt 4 ∈ closeChainFiber mtWord mtFiber16DirectStates (1 + 15) [mtFiber16StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber16DirectStates 1 15 [mtFiber16StateAt 0] (mtFiber16StateAt 4) h1

theorem mtFiber16State5_in_close :
    mtFiber16StateAt 5 ∈ closeChainFiber mtWord mtFiber16DirectStates mtFiber16DirectStates.length [mtFiber16StateAt 0] := by
  have h0 : mtFiber16StateAt 0 ∈ closeChainFiber mtWord mtFiber16DirectStates 0 [mtFiber16StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber16StateAt 1 ∈ closeChainFiber mtWord mtFiber16DirectStates 1 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 0 [mtFiber16StateAt 0]
      (mtFiber16StateAt 0) (mtFiber16StateAt 1) (by decide) h0 (by decide)
      mtFiber16ReverseSingleStep1
  have h2 : mtFiber16StateAt 5 ∈ closeChainFiber mtWord mtFiber16DirectStates 2 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 1 [mtFiber16StateAt 0]
      (mtFiber16StateAt 1) (mtFiber16StateAt 5) (by decide) h1 (by decide)
      mtFiber16ReverseSingleStep5
  change mtFiber16StateAt 5 ∈ closeChainFiber mtWord mtFiber16DirectStates (2 + 14) [mtFiber16StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber16DirectStates 2 14 [mtFiber16StateAt 0] (mtFiber16StateAt 5) h2

theorem mtFiber16State6_in_close :
    mtFiber16StateAt 6 ∈ closeChainFiber mtWord mtFiber16DirectStates mtFiber16DirectStates.length [mtFiber16StateAt 0] := by
  have h0 : mtFiber16StateAt 0 ∈ closeChainFiber mtWord mtFiber16DirectStates 0 [mtFiber16StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber16StateAt 2 ∈ closeChainFiber mtWord mtFiber16DirectStates 1 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 0 [mtFiber16StateAt 0]
      (mtFiber16StateAt 0) (mtFiber16StateAt 2) (by decide) h0 (by decide)
      mtFiber16ReverseSingleStep2
  have h2 : mtFiber16StateAt 6 ∈ closeChainFiber mtWord mtFiber16DirectStates 2 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 1 [mtFiber16StateAt 0]
      (mtFiber16StateAt 2) (mtFiber16StateAt 6) (by decide) h1 (by decide)
      mtFiber16ReverseSingleStep6
  change mtFiber16StateAt 6 ∈ closeChainFiber mtWord mtFiber16DirectStates (2 + 14) [mtFiber16StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber16DirectStates 2 14 [mtFiber16StateAt 0] (mtFiber16StateAt 6) h2

theorem mtFiber16State7_in_close :
    mtFiber16StateAt 7 ∈ closeChainFiber mtWord mtFiber16DirectStates mtFiber16DirectStates.length [mtFiber16StateAt 0] := by
  have h0 : mtFiber16StateAt 0 ∈ closeChainFiber mtWord mtFiber16DirectStates 0 [mtFiber16StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber16StateAt 1 ∈ closeChainFiber mtWord mtFiber16DirectStates 1 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 0 [mtFiber16StateAt 0]
      (mtFiber16StateAt 0) (mtFiber16StateAt 1) (by decide) h0 (by decide)
      mtFiber16ReverseSingleStep1
  have h2 : mtFiber16StateAt 3 ∈ closeChainFiber mtWord mtFiber16DirectStates 2 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 1 [mtFiber16StateAt 0]
      (mtFiber16StateAt 1) (mtFiber16StateAt 3) (by decide) h1 (by decide)
      mtFiber16ReverseSingleStep3
  have h3 : mtFiber16StateAt 7 ∈ closeChainFiber mtWord mtFiber16DirectStates 3 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 2 [mtFiber16StateAt 0]
      (mtFiber16StateAt 3) (mtFiber16StateAt 7) (by decide) h2 (by decide)
      mtFiber16ReverseSingleStep7
  change mtFiber16StateAt 7 ∈ closeChainFiber mtWord mtFiber16DirectStates (3 + 13) [mtFiber16StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber16DirectStates 3 13 [mtFiber16StateAt 0] (mtFiber16StateAt 7) h3

theorem mtFiber16State8_in_close :
    mtFiber16StateAt 8 ∈ closeChainFiber mtWord mtFiber16DirectStates mtFiber16DirectStates.length [mtFiber16StateAt 0] := by
  have h0 : mtFiber16StateAt 0 ∈ closeChainFiber mtWord mtFiber16DirectStates 0 [mtFiber16StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber16StateAt 8 ∈ closeChainFiber mtWord mtFiber16DirectStates 1 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 0 [mtFiber16StateAt 0]
      (mtFiber16StateAt 0) (mtFiber16StateAt 8) (by decide) h0 (by decide)
      mtFiber16ReverseSingleStep8
  change mtFiber16StateAt 8 ∈ closeChainFiber mtWord mtFiber16DirectStates (1 + 15) [mtFiber16StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber16DirectStates 1 15 [mtFiber16StateAt 0] (mtFiber16StateAt 8) h1

theorem mtFiber16State9_in_close :
    mtFiber16StateAt 9 ∈ closeChainFiber mtWord mtFiber16DirectStates mtFiber16DirectStates.length [mtFiber16StateAt 0] := by
  have h0 : mtFiber16StateAt 0 ∈ closeChainFiber mtWord mtFiber16DirectStates 0 [mtFiber16StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber16StateAt 1 ∈ closeChainFiber mtWord mtFiber16DirectStates 1 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 0 [mtFiber16StateAt 0]
      (mtFiber16StateAt 0) (mtFiber16StateAt 1) (by decide) h0 (by decide)
      mtFiber16ReverseSingleStep1
  have h2 : mtFiber16StateAt 9 ∈ closeChainFiber mtWord mtFiber16DirectStates 2 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 1 [mtFiber16StateAt 0]
      (mtFiber16StateAt 1) (mtFiber16StateAt 9) (by decide) h1 (by decide)
      mtFiber16ReverseSingleStep9
  change mtFiber16StateAt 9 ∈ closeChainFiber mtWord mtFiber16DirectStates (2 + 14) [mtFiber16StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber16DirectStates 2 14 [mtFiber16StateAt 0] (mtFiber16StateAt 9) h2

theorem mtFiber16State10_in_close :
    mtFiber16StateAt 10 ∈ closeChainFiber mtWord mtFiber16DirectStates mtFiber16DirectStates.length [mtFiber16StateAt 0] := by
  have h0 : mtFiber16StateAt 0 ∈ closeChainFiber mtWord mtFiber16DirectStates 0 [mtFiber16StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber16StateAt 2 ∈ closeChainFiber mtWord mtFiber16DirectStates 1 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 0 [mtFiber16StateAt 0]
      (mtFiber16StateAt 0) (mtFiber16StateAt 2) (by decide) h0 (by decide)
      mtFiber16ReverseSingleStep2
  have h2 : mtFiber16StateAt 10 ∈ closeChainFiber mtWord mtFiber16DirectStates 2 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 1 [mtFiber16StateAt 0]
      (mtFiber16StateAt 2) (mtFiber16StateAt 10) (by decide) h1 (by decide)
      mtFiber16ReverseSingleStep10
  change mtFiber16StateAt 10 ∈ closeChainFiber mtWord mtFiber16DirectStates (2 + 14) [mtFiber16StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber16DirectStates 2 14 [mtFiber16StateAt 0] (mtFiber16StateAt 10) h2

theorem mtFiber16State11_in_close :
    mtFiber16StateAt 11 ∈ closeChainFiber mtWord mtFiber16DirectStates mtFiber16DirectStates.length [mtFiber16StateAt 0] := by
  have h0 : mtFiber16StateAt 0 ∈ closeChainFiber mtWord mtFiber16DirectStates 0 [mtFiber16StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber16StateAt 1 ∈ closeChainFiber mtWord mtFiber16DirectStates 1 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 0 [mtFiber16StateAt 0]
      (mtFiber16StateAt 0) (mtFiber16StateAt 1) (by decide) h0 (by decide)
      mtFiber16ReverseSingleStep1
  have h2 : mtFiber16StateAt 3 ∈ closeChainFiber mtWord mtFiber16DirectStates 2 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 1 [mtFiber16StateAt 0]
      (mtFiber16StateAt 1) (mtFiber16StateAt 3) (by decide) h1 (by decide)
      mtFiber16ReverseSingleStep3
  have h3 : mtFiber16StateAt 11 ∈ closeChainFiber mtWord mtFiber16DirectStates 3 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 2 [mtFiber16StateAt 0]
      (mtFiber16StateAt 3) (mtFiber16StateAt 11) (by decide) h2 (by decide)
      mtFiber16ReverseSingleStep11
  change mtFiber16StateAt 11 ∈ closeChainFiber mtWord mtFiber16DirectStates (3 + 13) [mtFiber16StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber16DirectStates 3 13 [mtFiber16StateAt 0] (mtFiber16StateAt 11) h3

theorem mtFiber16State12_in_close :
    mtFiber16StateAt 12 ∈ closeChainFiber mtWord mtFiber16DirectStates mtFiber16DirectStates.length [mtFiber16StateAt 0] := by
  have h0 : mtFiber16StateAt 0 ∈ closeChainFiber mtWord mtFiber16DirectStates 0 [mtFiber16StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber16StateAt 4 ∈ closeChainFiber mtWord mtFiber16DirectStates 1 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 0 [mtFiber16StateAt 0]
      (mtFiber16StateAt 0) (mtFiber16StateAt 4) (by decide) h0 (by decide)
      mtFiber16ReverseSingleStep4
  have h2 : mtFiber16StateAt 12 ∈ closeChainFiber mtWord mtFiber16DirectStates 2 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 1 [mtFiber16StateAt 0]
      (mtFiber16StateAt 4) (mtFiber16StateAt 12) (by decide) h1 (by decide)
      mtFiber16ReverseSingleStep12
  change mtFiber16StateAt 12 ∈ closeChainFiber mtWord mtFiber16DirectStates (2 + 14) [mtFiber16StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber16DirectStates 2 14 [mtFiber16StateAt 0] (mtFiber16StateAt 12) h2

theorem mtFiber16State13_in_close :
    mtFiber16StateAt 13 ∈ closeChainFiber mtWord mtFiber16DirectStates mtFiber16DirectStates.length [mtFiber16StateAt 0] := by
  have h0 : mtFiber16StateAt 0 ∈ closeChainFiber mtWord mtFiber16DirectStates 0 [mtFiber16StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber16StateAt 1 ∈ closeChainFiber mtWord mtFiber16DirectStates 1 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 0 [mtFiber16StateAt 0]
      (mtFiber16StateAt 0) (mtFiber16StateAt 1) (by decide) h0 (by decide)
      mtFiber16ReverseSingleStep1
  have h2 : mtFiber16StateAt 5 ∈ closeChainFiber mtWord mtFiber16DirectStates 2 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 1 [mtFiber16StateAt 0]
      (mtFiber16StateAt 1) (mtFiber16StateAt 5) (by decide) h1 (by decide)
      mtFiber16ReverseSingleStep5
  have h3 : mtFiber16StateAt 13 ∈ closeChainFiber mtWord mtFiber16DirectStates 3 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 2 [mtFiber16StateAt 0]
      (mtFiber16StateAt 5) (mtFiber16StateAt 13) (by decide) h2 (by decide)
      mtFiber16ReverseSingleStep13
  change mtFiber16StateAt 13 ∈ closeChainFiber mtWord mtFiber16DirectStates (3 + 13) [mtFiber16StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber16DirectStates 3 13 [mtFiber16StateAt 0] (mtFiber16StateAt 13) h3

theorem mtFiber16State14_in_close :
    mtFiber16StateAt 14 ∈ closeChainFiber mtWord mtFiber16DirectStates mtFiber16DirectStates.length [mtFiber16StateAt 0] := by
  have h0 : mtFiber16StateAt 0 ∈ closeChainFiber mtWord mtFiber16DirectStates 0 [mtFiber16StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber16StateAt 2 ∈ closeChainFiber mtWord mtFiber16DirectStates 1 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 0 [mtFiber16StateAt 0]
      (mtFiber16StateAt 0) (mtFiber16StateAt 2) (by decide) h0 (by decide)
      mtFiber16ReverseSingleStep2
  have h2 : mtFiber16StateAt 6 ∈ closeChainFiber mtWord mtFiber16DirectStates 2 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 1 [mtFiber16StateAt 0]
      (mtFiber16StateAt 2) (mtFiber16StateAt 6) (by decide) h1 (by decide)
      mtFiber16ReverseSingleStep6
  have h3 : mtFiber16StateAt 14 ∈ closeChainFiber mtWord mtFiber16DirectStates 3 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 2 [mtFiber16StateAt 0]
      (mtFiber16StateAt 6) (mtFiber16StateAt 14) (by decide) h2 (by decide)
      mtFiber16ReverseSingleStep14
  change mtFiber16StateAt 14 ∈ closeChainFiber mtWord mtFiber16DirectStates (3 + 13) [mtFiber16StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber16DirectStates 3 13 [mtFiber16StateAt 0] (mtFiber16StateAt 14) h3

theorem mtFiber16State15_in_close :
    mtFiber16StateAt 15 ∈ closeChainFiber mtWord mtFiber16DirectStates mtFiber16DirectStates.length [mtFiber16StateAt 0] := by
  have h0 : mtFiber16StateAt 0 ∈ closeChainFiber mtWord mtFiber16DirectStates 0 [mtFiber16StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber16StateAt 1 ∈ closeChainFiber mtWord mtFiber16DirectStates 1 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 0 [mtFiber16StateAt 0]
      (mtFiber16StateAt 0) (mtFiber16StateAt 1) (by decide) h0 (by decide)
      mtFiber16ReverseSingleStep1
  have h2 : mtFiber16StateAt 3 ∈ closeChainFiber mtWord mtFiber16DirectStates 2 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 1 [mtFiber16StateAt 0]
      (mtFiber16StateAt 1) (mtFiber16StateAt 3) (by decide) h1 (by decide)
      mtFiber16ReverseSingleStep3
  have h3 : mtFiber16StateAt 7 ∈ closeChainFiber mtWord mtFiber16DirectStates 3 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 2 [mtFiber16StateAt 0]
      (mtFiber16StateAt 3) (mtFiber16StateAt 7) (by decide) h2 (by decide)
      mtFiber16ReverseSingleStep7
  have h4 : mtFiber16StateAt 15 ∈ closeChainFiber mtWord mtFiber16DirectStates 4 [mtFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber16DirectStates 3 [mtFiber16StateAt 0]
      (mtFiber16StateAt 7) (mtFiber16StateAt 15) (by decide) h3 (by decide)
      mtFiber16ReverseSingleStep15
  change mtFiber16StateAt 15 ∈ closeChainFiber mtWord mtFiber16DirectStates (4 + 12) [mtFiber16StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber16DirectStates 4 12 [mtFiber16StateAt 0] (mtFiber16StateAt 15) h4

theorem mtFiber16DirectConnected :
    chainFiberConnected mtWord mtFiber16DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber16DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber16State0_in_close
  · subst state
    exact mtFiber16State1_in_close
  · subst state
    exact mtFiber16State2_in_close
  · subst state
    exact mtFiber16State3_in_close
  · subst state
    exact mtFiber16State4_in_close
  · subst state
    exact mtFiber16State5_in_close
  · subst state
    exact mtFiber16State6_in_close
  · subst state
    exact mtFiber16State7_in_close
  · subst state
    exact mtFiber16State8_in_close
  · subst state
    exact mtFiber16State9_in_close
  · subst state
    exact mtFiber16State10_in_close
  · subst state
    exact mtFiber16State11_in_close
  · subst state
    exact mtFiber16State12_in_close
  · subst state
    exact mtFiber16State13_in_close
  · subst state
    exact mtFiber16State14_in_close
  · subst state
    exact mtFiber16State15_in_close
  · cases h
end GoertzelLemma818LengthTwoMTBridge

end Mettapedia.GraphTheory.FourColor
