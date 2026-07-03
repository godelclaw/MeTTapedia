import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for size-8 `mirror,mirror` length-two fibers, group 0

This module proves direct connectedness for generated `mirror,mirror` size-8 fibers from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMMBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorMirrorCertificate
open GoertzelLemma818MirrorMirrorReverseAudit

def mmFiber3StateAt (i : Nat) : List TauState :=
  directStates (mmFiber3RowAt i).sourceLeft (mmFiber3RowAt i).sourceRight

def mmFiber3DirectStates : List (List TauState) :=
  [mmFiber3StateAt 0, mmFiber3StateAt 1, mmFiber3StateAt 2, mmFiber3StateAt 3, mmFiber3StateAt 4, mmFiber3StateAt 5, mmFiber3StateAt 6, mmFiber3StateAt 7]

theorem mmFiber3ReverseRow_1_ok :
    mmRowReverseValid mmFiber3Key mmFiber3Expected (mmFiber3RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber3Chunk0_ok
  change (mmRowReverseValid mmFiber3Key mmFiber3Expected (mmFiber3RowAt 0) &&
    mmRowReverseValid mmFiber3Key mmFiber3Expected (mmFiber3RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber3ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber3StateAt 0) (mmFiber3StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber3StateAt 0) (mmFiber3StateAt 1)
    (mmFiber3RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber3Key mmFiber3Expected
        (mmFiber3RowAt 1) (by decide) mmFiber3ReverseRow_1_ok
      simpa [mmFiber3StateAt, mmFiber3RowAt, mmFiber3Rows, listGetD, directRow] using h)

theorem mmFiber3ReverseRow_2_ok :
    mmRowReverseValid mmFiber3Key mmFiber3Expected (mmFiber3RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber3Chunk1_ok
  change (mmRowReverseValid mmFiber3Key mmFiber3Expected (mmFiber3RowAt 2) &&
    mmRowReverseValid mmFiber3Key mmFiber3Expected (mmFiber3RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber3ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber3StateAt 1) (mmFiber3StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber3StateAt 1) (mmFiber3StateAt 2)
    (mmFiber3RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber3Key mmFiber3Expected
        (mmFiber3RowAt 2) (by decide) mmFiber3ReverseRow_2_ok
      simpa [mmFiber3StateAt, mmFiber3RowAt, mmFiber3Rows, listGetD, directRow] using h)

theorem mmFiber3ReverseRow_3_ok :
    mmRowReverseValid mmFiber3Key mmFiber3Expected (mmFiber3RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber3Chunk1_ok
  change (mmRowReverseValid mmFiber3Key mmFiber3Expected (mmFiber3RowAt 2) &&
    mmRowReverseValid mmFiber3Key mmFiber3Expected (mmFiber3RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber3ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber3StateAt 0) (mmFiber3StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber3StateAt 0) (mmFiber3StateAt 3)
    (mmFiber3RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber3Key mmFiber3Expected
        (mmFiber3RowAt 3) (by decide) mmFiber3ReverseRow_3_ok
      simpa [mmFiber3StateAt, mmFiber3RowAt, mmFiber3Rows, listGetD, directRow] using h)

theorem mmFiber3ReverseRow_4_ok :
    mmRowReverseValid mmFiber3Key mmFiber3Expected (mmFiber3RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber3Chunk2_ok
  change (mmRowReverseValid mmFiber3Key mmFiber3Expected (mmFiber3RowAt 4) &&
    mmRowReverseValid mmFiber3Key mmFiber3Expected (mmFiber3RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber3ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber3StateAt 0) (mmFiber3StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber3StateAt 0) (mmFiber3StateAt 4)
    (mmFiber3RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber3Key mmFiber3Expected
        (mmFiber3RowAt 4) (by decide) mmFiber3ReverseRow_4_ok
      simpa [mmFiber3StateAt, mmFiber3RowAt, mmFiber3Rows, listGetD, directRow] using h)

theorem mmFiber3ReverseRow_5_ok :
    mmRowReverseValid mmFiber3Key mmFiber3Expected (mmFiber3RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber3Chunk2_ok
  change (mmRowReverseValid mmFiber3Key mmFiber3Expected (mmFiber3RowAt 4) &&
    mmRowReverseValid mmFiber3Key mmFiber3Expected (mmFiber3RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber3ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber3StateAt 1) (mmFiber3StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber3StateAt 1) (mmFiber3StateAt 5)
    (mmFiber3RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber3Key mmFiber3Expected
        (mmFiber3RowAt 5) (by decide) mmFiber3ReverseRow_5_ok
      simpa [mmFiber3StateAt, mmFiber3RowAt, mmFiber3Rows, listGetD, directRow] using h)

theorem mmFiber3ReverseRow_6_ok :
    mmRowReverseValid mmFiber3Key mmFiber3Expected (mmFiber3RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber3Chunk3_ok
  change (mmRowReverseValid mmFiber3Key mmFiber3Expected (mmFiber3RowAt 6) &&
    mmRowReverseValid mmFiber3Key mmFiber3Expected (mmFiber3RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber3ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber3StateAt 2) (mmFiber3StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber3StateAt 2) (mmFiber3StateAt 6)
    (mmFiber3RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber3Key mmFiber3Expected
        (mmFiber3RowAt 6) (by decide) mmFiber3ReverseRow_6_ok
      simpa [mmFiber3StateAt, mmFiber3RowAt, mmFiber3Rows, listGetD, directRow] using h)

theorem mmFiber3ReverseRow_7_ok :
    mmRowReverseValid mmFiber3Key mmFiber3Expected (mmFiber3RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber3Chunk3_ok
  change (mmRowReverseValid mmFiber3Key mmFiber3Expected (mmFiber3RowAt 6) &&
    mmRowReverseValid mmFiber3Key mmFiber3Expected (mmFiber3RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber3ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber3StateAt 3) (mmFiber3StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber3StateAt 3) (mmFiber3StateAt 7)
    (mmFiber3RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber3Key mmFiber3Expected
        (mmFiber3RowAt 7) (by decide) mmFiber3ReverseRow_7_ok
      simpa [mmFiber3StateAt, mmFiber3RowAt, mmFiber3Rows, listGetD, directRow] using h)

theorem mmFiber3State0_in_close :
    mmFiber3StateAt 0 ∈ closeChainFiber mmWord mmFiber3DirectStates mmFiber3DirectStates.length [mmFiber3StateAt 0] := by
  change mmFiber3StateAt 0 ∈ closeChainFiber mmWord mmFiber3DirectStates 8 [mmFiber3StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber3DirectStates 0 8 [mmFiber3StateAt 0] (mmFiber3StateAt 0) (by simp [closeChainFiber])

theorem mmFiber3State1_in_close :
    mmFiber3StateAt 1 ∈ closeChainFiber mmWord mmFiber3DirectStates mmFiber3DirectStates.length [mmFiber3StateAt 0] := by
  have h0 : mmFiber3StateAt 0 ∈ closeChainFiber mmWord mmFiber3DirectStates 0 [mmFiber3StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber3StateAt 1 ∈ closeChainFiber mmWord mmFiber3DirectStates 1 [mmFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber3DirectStates 0 [mmFiber3StateAt 0]
      (mmFiber3StateAt 0) (mmFiber3StateAt 1) (by decide) h0 (by decide)
      mmFiber3ReverseSingleStep1
  change mmFiber3StateAt 1 ∈ closeChainFiber mmWord mmFiber3DirectStates (1 + 7) [mmFiber3StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber3DirectStates 1 7 [mmFiber3StateAt 0] (mmFiber3StateAt 1) h1

theorem mmFiber3State2_in_close :
    mmFiber3StateAt 2 ∈ closeChainFiber mmWord mmFiber3DirectStates mmFiber3DirectStates.length [mmFiber3StateAt 0] := by
  have h0 : mmFiber3StateAt 0 ∈ closeChainFiber mmWord mmFiber3DirectStates 0 [mmFiber3StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber3StateAt 1 ∈ closeChainFiber mmWord mmFiber3DirectStates 1 [mmFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber3DirectStates 0 [mmFiber3StateAt 0]
      (mmFiber3StateAt 0) (mmFiber3StateAt 1) (by decide) h0 (by decide)
      mmFiber3ReverseSingleStep1
  have h2 : mmFiber3StateAt 2 ∈ closeChainFiber mmWord mmFiber3DirectStates 2 [mmFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber3DirectStates 1 [mmFiber3StateAt 0]
      (mmFiber3StateAt 1) (mmFiber3StateAt 2) (by decide) h1 (by decide)
      mmFiber3ReverseSingleStep2
  change mmFiber3StateAt 2 ∈ closeChainFiber mmWord mmFiber3DirectStates (2 + 6) [mmFiber3StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber3DirectStates 2 6 [mmFiber3StateAt 0] (mmFiber3StateAt 2) h2

theorem mmFiber3State3_in_close :
    mmFiber3StateAt 3 ∈ closeChainFiber mmWord mmFiber3DirectStates mmFiber3DirectStates.length [mmFiber3StateAt 0] := by
  have h0 : mmFiber3StateAt 0 ∈ closeChainFiber mmWord mmFiber3DirectStates 0 [mmFiber3StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber3StateAt 3 ∈ closeChainFiber mmWord mmFiber3DirectStates 1 [mmFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber3DirectStates 0 [mmFiber3StateAt 0]
      (mmFiber3StateAt 0) (mmFiber3StateAt 3) (by decide) h0 (by decide)
      mmFiber3ReverseSingleStep3
  change mmFiber3StateAt 3 ∈ closeChainFiber mmWord mmFiber3DirectStates (1 + 7) [mmFiber3StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber3DirectStates 1 7 [mmFiber3StateAt 0] (mmFiber3StateAt 3) h1

theorem mmFiber3State4_in_close :
    mmFiber3StateAt 4 ∈ closeChainFiber mmWord mmFiber3DirectStates mmFiber3DirectStates.length [mmFiber3StateAt 0] := by
  have h0 : mmFiber3StateAt 0 ∈ closeChainFiber mmWord mmFiber3DirectStates 0 [mmFiber3StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber3StateAt 4 ∈ closeChainFiber mmWord mmFiber3DirectStates 1 [mmFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber3DirectStates 0 [mmFiber3StateAt 0]
      (mmFiber3StateAt 0) (mmFiber3StateAt 4) (by decide) h0 (by decide)
      mmFiber3ReverseSingleStep4
  change mmFiber3StateAt 4 ∈ closeChainFiber mmWord mmFiber3DirectStates (1 + 7) [mmFiber3StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber3DirectStates 1 7 [mmFiber3StateAt 0] (mmFiber3StateAt 4) h1

theorem mmFiber3State5_in_close :
    mmFiber3StateAt 5 ∈ closeChainFiber mmWord mmFiber3DirectStates mmFiber3DirectStates.length [mmFiber3StateAt 0] := by
  have h0 : mmFiber3StateAt 0 ∈ closeChainFiber mmWord mmFiber3DirectStates 0 [mmFiber3StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber3StateAt 1 ∈ closeChainFiber mmWord mmFiber3DirectStates 1 [mmFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber3DirectStates 0 [mmFiber3StateAt 0]
      (mmFiber3StateAt 0) (mmFiber3StateAt 1) (by decide) h0 (by decide)
      mmFiber3ReverseSingleStep1
  have h2 : mmFiber3StateAt 5 ∈ closeChainFiber mmWord mmFiber3DirectStates 2 [mmFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber3DirectStates 1 [mmFiber3StateAt 0]
      (mmFiber3StateAt 1) (mmFiber3StateAt 5) (by decide) h1 (by decide)
      mmFiber3ReverseSingleStep5
  change mmFiber3StateAt 5 ∈ closeChainFiber mmWord mmFiber3DirectStates (2 + 6) [mmFiber3StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber3DirectStates 2 6 [mmFiber3StateAt 0] (mmFiber3StateAt 5) h2

theorem mmFiber3State6_in_close :
    mmFiber3StateAt 6 ∈ closeChainFiber mmWord mmFiber3DirectStates mmFiber3DirectStates.length [mmFiber3StateAt 0] := by
  have h0 : mmFiber3StateAt 0 ∈ closeChainFiber mmWord mmFiber3DirectStates 0 [mmFiber3StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber3StateAt 1 ∈ closeChainFiber mmWord mmFiber3DirectStates 1 [mmFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber3DirectStates 0 [mmFiber3StateAt 0]
      (mmFiber3StateAt 0) (mmFiber3StateAt 1) (by decide) h0 (by decide)
      mmFiber3ReverseSingleStep1
  have h2 : mmFiber3StateAt 2 ∈ closeChainFiber mmWord mmFiber3DirectStates 2 [mmFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber3DirectStates 1 [mmFiber3StateAt 0]
      (mmFiber3StateAt 1) (mmFiber3StateAt 2) (by decide) h1 (by decide)
      mmFiber3ReverseSingleStep2
  have h3 : mmFiber3StateAt 6 ∈ closeChainFiber mmWord mmFiber3DirectStates 3 [mmFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber3DirectStates 2 [mmFiber3StateAt 0]
      (mmFiber3StateAt 2) (mmFiber3StateAt 6) (by decide) h2 (by decide)
      mmFiber3ReverseSingleStep6
  change mmFiber3StateAt 6 ∈ closeChainFiber mmWord mmFiber3DirectStates (3 + 5) [mmFiber3StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber3DirectStates 3 5 [mmFiber3StateAt 0] (mmFiber3StateAt 6) h3

theorem mmFiber3State7_in_close :
    mmFiber3StateAt 7 ∈ closeChainFiber mmWord mmFiber3DirectStates mmFiber3DirectStates.length [mmFiber3StateAt 0] := by
  have h0 : mmFiber3StateAt 0 ∈ closeChainFiber mmWord mmFiber3DirectStates 0 [mmFiber3StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber3StateAt 3 ∈ closeChainFiber mmWord mmFiber3DirectStates 1 [mmFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber3DirectStates 0 [mmFiber3StateAt 0]
      (mmFiber3StateAt 0) (mmFiber3StateAt 3) (by decide) h0 (by decide)
      mmFiber3ReverseSingleStep3
  have h2 : mmFiber3StateAt 7 ∈ closeChainFiber mmWord mmFiber3DirectStates 2 [mmFiber3StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber3DirectStates 1 [mmFiber3StateAt 0]
      (mmFiber3StateAt 3) (mmFiber3StateAt 7) (by decide) h1 (by decide)
      mmFiber3ReverseSingleStep7
  change mmFiber3StateAt 7 ∈ closeChainFiber mmWord mmFiber3DirectStates (2 + 6) [mmFiber3StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber3DirectStates 2 6 [mmFiber3StateAt 0] (mmFiber3StateAt 7) h2

theorem mmFiber3DirectConnected :
    chainFiberConnected mmWord mmFiber3DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber3DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber3State0_in_close
  · subst state
    exact mmFiber3State1_in_close
  · subst state
    exact mmFiber3State2_in_close
  · subst state
    exact mmFiber3State3_in_close
  · subst state
    exact mmFiber3State4_in_close
  · subst state
    exact mmFiber3State5_in_close
  · subst state
    exact mmFiber3State6_in_close
  · subst state
    exact mmFiber3State7_in_close
  · cases h
def mmFiber6StateAt (i : Nat) : List TauState :=
  directStates (mmFiber6RowAt i).sourceLeft (mmFiber6RowAt i).sourceRight

def mmFiber6DirectStates : List (List TauState) :=
  [mmFiber6StateAt 0, mmFiber6StateAt 1, mmFiber6StateAt 2, mmFiber6StateAt 3, mmFiber6StateAt 4, mmFiber6StateAt 5, mmFiber6StateAt 6, mmFiber6StateAt 7]

theorem mmFiber6ReverseRow_1_ok :
    mmRowReverseValid mmFiber6Key mmFiber6Expected (mmFiber6RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber6Chunk0_ok
  change (mmRowReverseValid mmFiber6Key mmFiber6Expected (mmFiber6RowAt 0) &&
    mmRowReverseValid mmFiber6Key mmFiber6Expected (mmFiber6RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber6ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber6StateAt 0) (mmFiber6StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber6StateAt 0) (mmFiber6StateAt 1)
    (mmFiber6RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber6Key mmFiber6Expected
        (mmFiber6RowAt 1) (by decide) mmFiber6ReverseRow_1_ok
      simpa [mmFiber6StateAt, mmFiber6RowAt, mmFiber6Rows, listGetD, directRow] using h)

theorem mmFiber6ReverseRow_2_ok :
    mmRowReverseValid mmFiber6Key mmFiber6Expected (mmFiber6RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber6Chunk1_ok
  change (mmRowReverseValid mmFiber6Key mmFiber6Expected (mmFiber6RowAt 2) &&
    mmRowReverseValid mmFiber6Key mmFiber6Expected (mmFiber6RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber6ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber6StateAt 0) (mmFiber6StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber6StateAt 0) (mmFiber6StateAt 2)
    (mmFiber6RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber6Key mmFiber6Expected
        (mmFiber6RowAt 2) (by decide) mmFiber6ReverseRow_2_ok
      simpa [mmFiber6StateAt, mmFiber6RowAt, mmFiber6Rows, listGetD, directRow] using h)

theorem mmFiber6ReverseRow_3_ok :
    mmRowReverseValid mmFiber6Key mmFiber6Expected (mmFiber6RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber6Chunk1_ok
  change (mmRowReverseValid mmFiber6Key mmFiber6Expected (mmFiber6RowAt 2) &&
    mmRowReverseValid mmFiber6Key mmFiber6Expected (mmFiber6RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber6ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber6StateAt 1) (mmFiber6StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber6StateAt 1) (mmFiber6StateAt 3)
    (mmFiber6RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber6Key mmFiber6Expected
        (mmFiber6RowAt 3) (by decide) mmFiber6ReverseRow_3_ok
      simpa [mmFiber6StateAt, mmFiber6RowAt, mmFiber6Rows, listGetD, directRow] using h)

theorem mmFiber6ReverseRow_4_ok :
    mmRowReverseValid mmFiber6Key mmFiber6Expected (mmFiber6RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber6Chunk2_ok
  change (mmRowReverseValid mmFiber6Key mmFiber6Expected (mmFiber6RowAt 4) &&
    mmRowReverseValid mmFiber6Key mmFiber6Expected (mmFiber6RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber6ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber6StateAt 0) (mmFiber6StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber6StateAt 0) (mmFiber6StateAt 4)
    (mmFiber6RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber6Key mmFiber6Expected
        (mmFiber6RowAt 4) (by decide) mmFiber6ReverseRow_4_ok
      simpa [mmFiber6StateAt, mmFiber6RowAt, mmFiber6Rows, listGetD, directRow] using h)

theorem mmFiber6ReverseRow_5_ok :
    mmRowReverseValid mmFiber6Key mmFiber6Expected (mmFiber6RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber6Chunk2_ok
  change (mmRowReverseValid mmFiber6Key mmFiber6Expected (mmFiber6RowAt 4) &&
    mmRowReverseValid mmFiber6Key mmFiber6Expected (mmFiber6RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber6ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber6StateAt 1) (mmFiber6StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber6StateAt 1) (mmFiber6StateAt 5)
    (mmFiber6RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber6Key mmFiber6Expected
        (mmFiber6RowAt 5) (by decide) mmFiber6ReverseRow_5_ok
      simpa [mmFiber6StateAt, mmFiber6RowAt, mmFiber6Rows, listGetD, directRow] using h)

theorem mmFiber6ReverseRow_6_ok :
    mmRowReverseValid mmFiber6Key mmFiber6Expected (mmFiber6RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber6Chunk3_ok
  change (mmRowReverseValid mmFiber6Key mmFiber6Expected (mmFiber6RowAt 6) &&
    mmRowReverseValid mmFiber6Key mmFiber6Expected (mmFiber6RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber6ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber6StateAt 2) (mmFiber6StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber6StateAt 2) (mmFiber6StateAt 6)
    (mmFiber6RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber6Key mmFiber6Expected
        (mmFiber6RowAt 6) (by decide) mmFiber6ReverseRow_6_ok
      simpa [mmFiber6StateAt, mmFiber6RowAt, mmFiber6Rows, listGetD, directRow] using h)

theorem mmFiber6ReverseRow_7_ok :
    mmRowReverseValid mmFiber6Key mmFiber6Expected (mmFiber6RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber6Chunk3_ok
  change (mmRowReverseValid mmFiber6Key mmFiber6Expected (mmFiber6RowAt 6) &&
    mmRowReverseValid mmFiber6Key mmFiber6Expected (mmFiber6RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber6ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber6StateAt 3) (mmFiber6StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber6StateAt 3) (mmFiber6StateAt 7)
    (mmFiber6RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber6Key mmFiber6Expected
        (mmFiber6RowAt 7) (by decide) mmFiber6ReverseRow_7_ok
      simpa [mmFiber6StateAt, mmFiber6RowAt, mmFiber6Rows, listGetD, directRow] using h)

theorem mmFiber6State0_in_close :
    mmFiber6StateAt 0 ∈ closeChainFiber mmWord mmFiber6DirectStates mmFiber6DirectStates.length [mmFiber6StateAt 0] := by
  change mmFiber6StateAt 0 ∈ closeChainFiber mmWord mmFiber6DirectStates 8 [mmFiber6StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber6DirectStates 0 8 [mmFiber6StateAt 0] (mmFiber6StateAt 0) (by simp [closeChainFiber])

theorem mmFiber6State1_in_close :
    mmFiber6StateAt 1 ∈ closeChainFiber mmWord mmFiber6DirectStates mmFiber6DirectStates.length [mmFiber6StateAt 0] := by
  have h0 : mmFiber6StateAt 0 ∈ closeChainFiber mmWord mmFiber6DirectStates 0 [mmFiber6StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber6StateAt 1 ∈ closeChainFiber mmWord mmFiber6DirectStates 1 [mmFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber6DirectStates 0 [mmFiber6StateAt 0]
      (mmFiber6StateAt 0) (mmFiber6StateAt 1) (by decide) h0 (by decide)
      mmFiber6ReverseSingleStep1
  change mmFiber6StateAt 1 ∈ closeChainFiber mmWord mmFiber6DirectStates (1 + 7) [mmFiber6StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber6DirectStates 1 7 [mmFiber6StateAt 0] (mmFiber6StateAt 1) h1

theorem mmFiber6State2_in_close :
    mmFiber6StateAt 2 ∈ closeChainFiber mmWord mmFiber6DirectStates mmFiber6DirectStates.length [mmFiber6StateAt 0] := by
  have h0 : mmFiber6StateAt 0 ∈ closeChainFiber mmWord mmFiber6DirectStates 0 [mmFiber6StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber6StateAt 2 ∈ closeChainFiber mmWord mmFiber6DirectStates 1 [mmFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber6DirectStates 0 [mmFiber6StateAt 0]
      (mmFiber6StateAt 0) (mmFiber6StateAt 2) (by decide) h0 (by decide)
      mmFiber6ReverseSingleStep2
  change mmFiber6StateAt 2 ∈ closeChainFiber mmWord mmFiber6DirectStates (1 + 7) [mmFiber6StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber6DirectStates 1 7 [mmFiber6StateAt 0] (mmFiber6StateAt 2) h1

theorem mmFiber6State3_in_close :
    mmFiber6StateAt 3 ∈ closeChainFiber mmWord mmFiber6DirectStates mmFiber6DirectStates.length [mmFiber6StateAt 0] := by
  have h0 : mmFiber6StateAt 0 ∈ closeChainFiber mmWord mmFiber6DirectStates 0 [mmFiber6StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber6StateAt 1 ∈ closeChainFiber mmWord mmFiber6DirectStates 1 [mmFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber6DirectStates 0 [mmFiber6StateAt 0]
      (mmFiber6StateAt 0) (mmFiber6StateAt 1) (by decide) h0 (by decide)
      mmFiber6ReverseSingleStep1
  have h2 : mmFiber6StateAt 3 ∈ closeChainFiber mmWord mmFiber6DirectStates 2 [mmFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber6DirectStates 1 [mmFiber6StateAt 0]
      (mmFiber6StateAt 1) (mmFiber6StateAt 3) (by decide) h1 (by decide)
      mmFiber6ReverseSingleStep3
  change mmFiber6StateAt 3 ∈ closeChainFiber mmWord mmFiber6DirectStates (2 + 6) [mmFiber6StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber6DirectStates 2 6 [mmFiber6StateAt 0] (mmFiber6StateAt 3) h2

theorem mmFiber6State4_in_close :
    mmFiber6StateAt 4 ∈ closeChainFiber mmWord mmFiber6DirectStates mmFiber6DirectStates.length [mmFiber6StateAt 0] := by
  have h0 : mmFiber6StateAt 0 ∈ closeChainFiber mmWord mmFiber6DirectStates 0 [mmFiber6StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber6StateAt 4 ∈ closeChainFiber mmWord mmFiber6DirectStates 1 [mmFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber6DirectStates 0 [mmFiber6StateAt 0]
      (mmFiber6StateAt 0) (mmFiber6StateAt 4) (by decide) h0 (by decide)
      mmFiber6ReverseSingleStep4
  change mmFiber6StateAt 4 ∈ closeChainFiber mmWord mmFiber6DirectStates (1 + 7) [mmFiber6StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber6DirectStates 1 7 [mmFiber6StateAt 0] (mmFiber6StateAt 4) h1

theorem mmFiber6State5_in_close :
    mmFiber6StateAt 5 ∈ closeChainFiber mmWord mmFiber6DirectStates mmFiber6DirectStates.length [mmFiber6StateAt 0] := by
  have h0 : mmFiber6StateAt 0 ∈ closeChainFiber mmWord mmFiber6DirectStates 0 [mmFiber6StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber6StateAt 1 ∈ closeChainFiber mmWord mmFiber6DirectStates 1 [mmFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber6DirectStates 0 [mmFiber6StateAt 0]
      (mmFiber6StateAt 0) (mmFiber6StateAt 1) (by decide) h0 (by decide)
      mmFiber6ReverseSingleStep1
  have h2 : mmFiber6StateAt 5 ∈ closeChainFiber mmWord mmFiber6DirectStates 2 [mmFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber6DirectStates 1 [mmFiber6StateAt 0]
      (mmFiber6StateAt 1) (mmFiber6StateAt 5) (by decide) h1 (by decide)
      mmFiber6ReverseSingleStep5
  change mmFiber6StateAt 5 ∈ closeChainFiber mmWord mmFiber6DirectStates (2 + 6) [mmFiber6StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber6DirectStates 2 6 [mmFiber6StateAt 0] (mmFiber6StateAt 5) h2

theorem mmFiber6State6_in_close :
    mmFiber6StateAt 6 ∈ closeChainFiber mmWord mmFiber6DirectStates mmFiber6DirectStates.length [mmFiber6StateAt 0] := by
  have h0 : mmFiber6StateAt 0 ∈ closeChainFiber mmWord mmFiber6DirectStates 0 [mmFiber6StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber6StateAt 2 ∈ closeChainFiber mmWord mmFiber6DirectStates 1 [mmFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber6DirectStates 0 [mmFiber6StateAt 0]
      (mmFiber6StateAt 0) (mmFiber6StateAt 2) (by decide) h0 (by decide)
      mmFiber6ReverseSingleStep2
  have h2 : mmFiber6StateAt 6 ∈ closeChainFiber mmWord mmFiber6DirectStates 2 [mmFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber6DirectStates 1 [mmFiber6StateAt 0]
      (mmFiber6StateAt 2) (mmFiber6StateAt 6) (by decide) h1 (by decide)
      mmFiber6ReverseSingleStep6
  change mmFiber6StateAt 6 ∈ closeChainFiber mmWord mmFiber6DirectStates (2 + 6) [mmFiber6StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber6DirectStates 2 6 [mmFiber6StateAt 0] (mmFiber6StateAt 6) h2

theorem mmFiber6State7_in_close :
    mmFiber6StateAt 7 ∈ closeChainFiber mmWord mmFiber6DirectStates mmFiber6DirectStates.length [mmFiber6StateAt 0] := by
  have h0 : mmFiber6StateAt 0 ∈ closeChainFiber mmWord mmFiber6DirectStates 0 [mmFiber6StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber6StateAt 1 ∈ closeChainFiber mmWord mmFiber6DirectStates 1 [mmFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber6DirectStates 0 [mmFiber6StateAt 0]
      (mmFiber6StateAt 0) (mmFiber6StateAt 1) (by decide) h0 (by decide)
      mmFiber6ReverseSingleStep1
  have h2 : mmFiber6StateAt 3 ∈ closeChainFiber mmWord mmFiber6DirectStates 2 [mmFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber6DirectStates 1 [mmFiber6StateAt 0]
      (mmFiber6StateAt 1) (mmFiber6StateAt 3) (by decide) h1 (by decide)
      mmFiber6ReverseSingleStep3
  have h3 : mmFiber6StateAt 7 ∈ closeChainFiber mmWord mmFiber6DirectStates 3 [mmFiber6StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber6DirectStates 2 [mmFiber6StateAt 0]
      (mmFiber6StateAt 3) (mmFiber6StateAt 7) (by decide) h2 (by decide)
      mmFiber6ReverseSingleStep7
  change mmFiber6StateAt 7 ∈ closeChainFiber mmWord mmFiber6DirectStates (3 + 5) [mmFiber6StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber6DirectStates 3 5 [mmFiber6StateAt 0] (mmFiber6StateAt 7) h3

theorem mmFiber6DirectConnected :
    chainFiberConnected mmWord mmFiber6DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber6DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber6State0_in_close
  · subst state
    exact mmFiber6State1_in_close
  · subst state
    exact mmFiber6State2_in_close
  · subst state
    exact mmFiber6State3_in_close
  · subst state
    exact mmFiber6State4_in_close
  · subst state
    exact mmFiber6State5_in_close
  · subst state
    exact mmFiber6State6_in_close
  · subst state
    exact mmFiber6State7_in_close
  · cases h
def mmFiber9StateAt (i : Nat) : List TauState :=
  directStates (mmFiber9RowAt i).sourceLeft (mmFiber9RowAt i).sourceRight

def mmFiber9DirectStates : List (List TauState) :=
  [mmFiber9StateAt 0, mmFiber9StateAt 1, mmFiber9StateAt 2, mmFiber9StateAt 3, mmFiber9StateAt 4, mmFiber9StateAt 5, mmFiber9StateAt 6, mmFiber9StateAt 7]

theorem mmFiber9ReverseRow_1_ok :
    mmRowReverseValid mmFiber9Key mmFiber9Expected (mmFiber9RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber9Chunk0_ok
  change (mmRowReverseValid mmFiber9Key mmFiber9Expected (mmFiber9RowAt 0) &&
    mmRowReverseValid mmFiber9Key mmFiber9Expected (mmFiber9RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber9ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber9StateAt 0) (mmFiber9StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber9StateAt 0) (mmFiber9StateAt 1)
    (mmFiber9RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber9Key mmFiber9Expected
        (mmFiber9RowAt 1) (by decide) mmFiber9ReverseRow_1_ok
      simpa [mmFiber9StateAt, mmFiber9RowAt, mmFiber9Rows, listGetD, directRow] using h)

theorem mmFiber9ReverseRow_2_ok :
    mmRowReverseValid mmFiber9Key mmFiber9Expected (mmFiber9RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber9Chunk1_ok
  change (mmRowReverseValid mmFiber9Key mmFiber9Expected (mmFiber9RowAt 2) &&
    mmRowReverseValid mmFiber9Key mmFiber9Expected (mmFiber9RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber9ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber9StateAt 1) (mmFiber9StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber9StateAt 1) (mmFiber9StateAt 2)
    (mmFiber9RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber9Key mmFiber9Expected
        (mmFiber9RowAt 2) (by decide) mmFiber9ReverseRow_2_ok
      simpa [mmFiber9StateAt, mmFiber9RowAt, mmFiber9Rows, listGetD, directRow] using h)

theorem mmFiber9ReverseRow_3_ok :
    mmRowReverseValid mmFiber9Key mmFiber9Expected (mmFiber9RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber9Chunk1_ok
  change (mmRowReverseValid mmFiber9Key mmFiber9Expected (mmFiber9RowAt 2) &&
    mmRowReverseValid mmFiber9Key mmFiber9Expected (mmFiber9RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber9ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber9StateAt 0) (mmFiber9StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber9StateAt 0) (mmFiber9StateAt 3)
    (mmFiber9RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber9Key mmFiber9Expected
        (mmFiber9RowAt 3) (by decide) mmFiber9ReverseRow_3_ok
      simpa [mmFiber9StateAt, mmFiber9RowAt, mmFiber9Rows, listGetD, directRow] using h)

theorem mmFiber9ReverseRow_4_ok :
    mmRowReverseValid mmFiber9Key mmFiber9Expected (mmFiber9RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber9Chunk2_ok
  change (mmRowReverseValid mmFiber9Key mmFiber9Expected (mmFiber9RowAt 4) &&
    mmRowReverseValid mmFiber9Key mmFiber9Expected (mmFiber9RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber9ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber9StateAt 0) (mmFiber9StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber9StateAt 0) (mmFiber9StateAt 4)
    (mmFiber9RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber9Key mmFiber9Expected
        (mmFiber9RowAt 4) (by decide) mmFiber9ReverseRow_4_ok
      simpa [mmFiber9StateAt, mmFiber9RowAt, mmFiber9Rows, listGetD, directRow] using h)

theorem mmFiber9ReverseRow_5_ok :
    mmRowReverseValid mmFiber9Key mmFiber9Expected (mmFiber9RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber9Chunk2_ok
  change (mmRowReverseValid mmFiber9Key mmFiber9Expected (mmFiber9RowAt 4) &&
    mmRowReverseValid mmFiber9Key mmFiber9Expected (mmFiber9RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber9ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber9StateAt 1) (mmFiber9StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber9StateAt 1) (mmFiber9StateAt 5)
    (mmFiber9RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber9Key mmFiber9Expected
        (mmFiber9RowAt 5) (by decide) mmFiber9ReverseRow_5_ok
      simpa [mmFiber9StateAt, mmFiber9RowAt, mmFiber9Rows, listGetD, directRow] using h)

theorem mmFiber9ReverseRow_6_ok :
    mmRowReverseValid mmFiber9Key mmFiber9Expected (mmFiber9RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber9Chunk3_ok
  change (mmRowReverseValid mmFiber9Key mmFiber9Expected (mmFiber9RowAt 6) &&
    mmRowReverseValid mmFiber9Key mmFiber9Expected (mmFiber9RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber9ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber9StateAt 2) (mmFiber9StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber9StateAt 2) (mmFiber9StateAt 6)
    (mmFiber9RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber9Key mmFiber9Expected
        (mmFiber9RowAt 6) (by decide) mmFiber9ReverseRow_6_ok
      simpa [mmFiber9StateAt, mmFiber9RowAt, mmFiber9Rows, listGetD, directRow] using h)

theorem mmFiber9ReverseRow_7_ok :
    mmRowReverseValid mmFiber9Key mmFiber9Expected (mmFiber9RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber9Chunk3_ok
  change (mmRowReverseValid mmFiber9Key mmFiber9Expected (mmFiber9RowAt 6) &&
    mmRowReverseValid mmFiber9Key mmFiber9Expected (mmFiber9RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber9ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber9StateAt 3) (mmFiber9StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber9StateAt 3) (mmFiber9StateAt 7)
    (mmFiber9RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber9Key mmFiber9Expected
        (mmFiber9RowAt 7) (by decide) mmFiber9ReverseRow_7_ok
      simpa [mmFiber9StateAt, mmFiber9RowAt, mmFiber9Rows, listGetD, directRow] using h)

theorem mmFiber9State0_in_close :
    mmFiber9StateAt 0 ∈ closeChainFiber mmWord mmFiber9DirectStates mmFiber9DirectStates.length [mmFiber9StateAt 0] := by
  change mmFiber9StateAt 0 ∈ closeChainFiber mmWord mmFiber9DirectStates 8 [mmFiber9StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber9DirectStates 0 8 [mmFiber9StateAt 0] (mmFiber9StateAt 0) (by simp [closeChainFiber])

theorem mmFiber9State1_in_close :
    mmFiber9StateAt 1 ∈ closeChainFiber mmWord mmFiber9DirectStates mmFiber9DirectStates.length [mmFiber9StateAt 0] := by
  have h0 : mmFiber9StateAt 0 ∈ closeChainFiber mmWord mmFiber9DirectStates 0 [mmFiber9StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber9StateAt 1 ∈ closeChainFiber mmWord mmFiber9DirectStates 1 [mmFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber9DirectStates 0 [mmFiber9StateAt 0]
      (mmFiber9StateAt 0) (mmFiber9StateAt 1) (by decide) h0 (by decide)
      mmFiber9ReverseSingleStep1
  change mmFiber9StateAt 1 ∈ closeChainFiber mmWord mmFiber9DirectStates (1 + 7) [mmFiber9StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber9DirectStates 1 7 [mmFiber9StateAt 0] (mmFiber9StateAt 1) h1

theorem mmFiber9State2_in_close :
    mmFiber9StateAt 2 ∈ closeChainFiber mmWord mmFiber9DirectStates mmFiber9DirectStates.length [mmFiber9StateAt 0] := by
  have h0 : mmFiber9StateAt 0 ∈ closeChainFiber mmWord mmFiber9DirectStates 0 [mmFiber9StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber9StateAt 1 ∈ closeChainFiber mmWord mmFiber9DirectStates 1 [mmFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber9DirectStates 0 [mmFiber9StateAt 0]
      (mmFiber9StateAt 0) (mmFiber9StateAt 1) (by decide) h0 (by decide)
      mmFiber9ReverseSingleStep1
  have h2 : mmFiber9StateAt 2 ∈ closeChainFiber mmWord mmFiber9DirectStates 2 [mmFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber9DirectStates 1 [mmFiber9StateAt 0]
      (mmFiber9StateAt 1) (mmFiber9StateAt 2) (by decide) h1 (by decide)
      mmFiber9ReverseSingleStep2
  change mmFiber9StateAt 2 ∈ closeChainFiber mmWord mmFiber9DirectStates (2 + 6) [mmFiber9StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber9DirectStates 2 6 [mmFiber9StateAt 0] (mmFiber9StateAt 2) h2

theorem mmFiber9State3_in_close :
    mmFiber9StateAt 3 ∈ closeChainFiber mmWord mmFiber9DirectStates mmFiber9DirectStates.length [mmFiber9StateAt 0] := by
  have h0 : mmFiber9StateAt 0 ∈ closeChainFiber mmWord mmFiber9DirectStates 0 [mmFiber9StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber9StateAt 3 ∈ closeChainFiber mmWord mmFiber9DirectStates 1 [mmFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber9DirectStates 0 [mmFiber9StateAt 0]
      (mmFiber9StateAt 0) (mmFiber9StateAt 3) (by decide) h0 (by decide)
      mmFiber9ReverseSingleStep3
  change mmFiber9StateAt 3 ∈ closeChainFiber mmWord mmFiber9DirectStates (1 + 7) [mmFiber9StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber9DirectStates 1 7 [mmFiber9StateAt 0] (mmFiber9StateAt 3) h1

theorem mmFiber9State4_in_close :
    mmFiber9StateAt 4 ∈ closeChainFiber mmWord mmFiber9DirectStates mmFiber9DirectStates.length [mmFiber9StateAt 0] := by
  have h0 : mmFiber9StateAt 0 ∈ closeChainFiber mmWord mmFiber9DirectStates 0 [mmFiber9StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber9StateAt 4 ∈ closeChainFiber mmWord mmFiber9DirectStates 1 [mmFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber9DirectStates 0 [mmFiber9StateAt 0]
      (mmFiber9StateAt 0) (mmFiber9StateAt 4) (by decide) h0 (by decide)
      mmFiber9ReverseSingleStep4
  change mmFiber9StateAt 4 ∈ closeChainFiber mmWord mmFiber9DirectStates (1 + 7) [mmFiber9StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber9DirectStates 1 7 [mmFiber9StateAt 0] (mmFiber9StateAt 4) h1

theorem mmFiber9State5_in_close :
    mmFiber9StateAt 5 ∈ closeChainFiber mmWord mmFiber9DirectStates mmFiber9DirectStates.length [mmFiber9StateAt 0] := by
  have h0 : mmFiber9StateAt 0 ∈ closeChainFiber mmWord mmFiber9DirectStates 0 [mmFiber9StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber9StateAt 1 ∈ closeChainFiber mmWord mmFiber9DirectStates 1 [mmFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber9DirectStates 0 [mmFiber9StateAt 0]
      (mmFiber9StateAt 0) (mmFiber9StateAt 1) (by decide) h0 (by decide)
      mmFiber9ReverseSingleStep1
  have h2 : mmFiber9StateAt 5 ∈ closeChainFiber mmWord mmFiber9DirectStates 2 [mmFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber9DirectStates 1 [mmFiber9StateAt 0]
      (mmFiber9StateAt 1) (mmFiber9StateAt 5) (by decide) h1 (by decide)
      mmFiber9ReverseSingleStep5
  change mmFiber9StateAt 5 ∈ closeChainFiber mmWord mmFiber9DirectStates (2 + 6) [mmFiber9StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber9DirectStates 2 6 [mmFiber9StateAt 0] (mmFiber9StateAt 5) h2

theorem mmFiber9State6_in_close :
    mmFiber9StateAt 6 ∈ closeChainFiber mmWord mmFiber9DirectStates mmFiber9DirectStates.length [mmFiber9StateAt 0] := by
  have h0 : mmFiber9StateAt 0 ∈ closeChainFiber mmWord mmFiber9DirectStates 0 [mmFiber9StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber9StateAt 1 ∈ closeChainFiber mmWord mmFiber9DirectStates 1 [mmFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber9DirectStates 0 [mmFiber9StateAt 0]
      (mmFiber9StateAt 0) (mmFiber9StateAt 1) (by decide) h0 (by decide)
      mmFiber9ReverseSingleStep1
  have h2 : mmFiber9StateAt 2 ∈ closeChainFiber mmWord mmFiber9DirectStates 2 [mmFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber9DirectStates 1 [mmFiber9StateAt 0]
      (mmFiber9StateAt 1) (mmFiber9StateAt 2) (by decide) h1 (by decide)
      mmFiber9ReverseSingleStep2
  have h3 : mmFiber9StateAt 6 ∈ closeChainFiber mmWord mmFiber9DirectStates 3 [mmFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber9DirectStates 2 [mmFiber9StateAt 0]
      (mmFiber9StateAt 2) (mmFiber9StateAt 6) (by decide) h2 (by decide)
      mmFiber9ReverseSingleStep6
  change mmFiber9StateAt 6 ∈ closeChainFiber mmWord mmFiber9DirectStates (3 + 5) [mmFiber9StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber9DirectStates 3 5 [mmFiber9StateAt 0] (mmFiber9StateAt 6) h3

theorem mmFiber9State7_in_close :
    mmFiber9StateAt 7 ∈ closeChainFiber mmWord mmFiber9DirectStates mmFiber9DirectStates.length [mmFiber9StateAt 0] := by
  have h0 : mmFiber9StateAt 0 ∈ closeChainFiber mmWord mmFiber9DirectStates 0 [mmFiber9StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber9StateAt 3 ∈ closeChainFiber mmWord mmFiber9DirectStates 1 [mmFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber9DirectStates 0 [mmFiber9StateAt 0]
      (mmFiber9StateAt 0) (mmFiber9StateAt 3) (by decide) h0 (by decide)
      mmFiber9ReverseSingleStep3
  have h2 : mmFiber9StateAt 7 ∈ closeChainFiber mmWord mmFiber9DirectStates 2 [mmFiber9StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber9DirectStates 1 [mmFiber9StateAt 0]
      (mmFiber9StateAt 3) (mmFiber9StateAt 7) (by decide) h1 (by decide)
      mmFiber9ReverseSingleStep7
  change mmFiber9StateAt 7 ∈ closeChainFiber mmWord mmFiber9DirectStates (2 + 6) [mmFiber9StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber9DirectStates 2 6 [mmFiber9StateAt 0] (mmFiber9StateAt 7) h2

theorem mmFiber9DirectConnected :
    chainFiberConnected mmWord mmFiber9DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber9DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber9State0_in_close
  · subst state
    exact mmFiber9State1_in_close
  · subst state
    exact mmFiber9State2_in_close
  · subst state
    exact mmFiber9State3_in_close
  · subst state
    exact mmFiber9State4_in_close
  · subst state
    exact mmFiber9State5_in_close
  · subst state
    exact mmFiber9State6_in_close
  · subst state
    exact mmFiber9State7_in_close
  · cases h
def mmFiber16StateAt (i : Nat) : List TauState :=
  directStates (mmFiber16RowAt i).sourceLeft (mmFiber16RowAt i).sourceRight

def mmFiber16DirectStates : List (List TauState) :=
  [mmFiber16StateAt 0, mmFiber16StateAt 1, mmFiber16StateAt 2, mmFiber16StateAt 3, mmFiber16StateAt 4, mmFiber16StateAt 5, mmFiber16StateAt 6, mmFiber16StateAt 7]

theorem mmFiber16ReverseRow_1_ok :
    mmRowReverseValid mmFiber16Key mmFiber16Expected (mmFiber16RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber16Chunk0_ok
  change (mmRowReverseValid mmFiber16Key mmFiber16Expected (mmFiber16RowAt 0) &&
    mmRowReverseValid mmFiber16Key mmFiber16Expected (mmFiber16RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber16ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber16StateAt 0) (mmFiber16StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber16StateAt 0) (mmFiber16StateAt 1)
    (mmFiber16RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber16Key mmFiber16Expected
        (mmFiber16RowAt 1) (by decide) mmFiber16ReverseRow_1_ok
      simpa [mmFiber16StateAt, mmFiber16RowAt, mmFiber16Rows, listGetD, directRow] using h)

theorem mmFiber16ReverseRow_2_ok :
    mmRowReverseValid mmFiber16Key mmFiber16Expected (mmFiber16RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber16Chunk1_ok
  change (mmRowReverseValid mmFiber16Key mmFiber16Expected (mmFiber16RowAt 2) &&
    mmRowReverseValid mmFiber16Key mmFiber16Expected (mmFiber16RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber16ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber16StateAt 0) (mmFiber16StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber16StateAt 0) (mmFiber16StateAt 2)
    (mmFiber16RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber16Key mmFiber16Expected
        (mmFiber16RowAt 2) (by decide) mmFiber16ReverseRow_2_ok
      simpa [mmFiber16StateAt, mmFiber16RowAt, mmFiber16Rows, listGetD, directRow] using h)

theorem mmFiber16ReverseRow_3_ok :
    mmRowReverseValid mmFiber16Key mmFiber16Expected (mmFiber16RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber16Chunk1_ok
  change (mmRowReverseValid mmFiber16Key mmFiber16Expected (mmFiber16RowAt 2) &&
    mmRowReverseValid mmFiber16Key mmFiber16Expected (mmFiber16RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber16ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber16StateAt 1) (mmFiber16StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber16StateAt 1) (mmFiber16StateAt 3)
    (mmFiber16RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber16Key mmFiber16Expected
        (mmFiber16RowAt 3) (by decide) mmFiber16ReverseRow_3_ok
      simpa [mmFiber16StateAt, mmFiber16RowAt, mmFiber16Rows, listGetD, directRow] using h)

theorem mmFiber16ReverseRow_4_ok :
    mmRowReverseValid mmFiber16Key mmFiber16Expected (mmFiber16RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber16Chunk2_ok
  change (mmRowReverseValid mmFiber16Key mmFiber16Expected (mmFiber16RowAt 4) &&
    mmRowReverseValid mmFiber16Key mmFiber16Expected (mmFiber16RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber16ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber16StateAt 0) (mmFiber16StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber16StateAt 0) (mmFiber16StateAt 4)
    (mmFiber16RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber16Key mmFiber16Expected
        (mmFiber16RowAt 4) (by decide) mmFiber16ReverseRow_4_ok
      simpa [mmFiber16StateAt, mmFiber16RowAt, mmFiber16Rows, listGetD, directRow] using h)

theorem mmFiber16ReverseRow_5_ok :
    mmRowReverseValid mmFiber16Key mmFiber16Expected (mmFiber16RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber16Chunk2_ok
  change (mmRowReverseValid mmFiber16Key mmFiber16Expected (mmFiber16RowAt 4) &&
    mmRowReverseValid mmFiber16Key mmFiber16Expected (mmFiber16RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber16ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber16StateAt 1) (mmFiber16StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber16StateAt 1) (mmFiber16StateAt 5)
    (mmFiber16RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber16Key mmFiber16Expected
        (mmFiber16RowAt 5) (by decide) mmFiber16ReverseRow_5_ok
      simpa [mmFiber16StateAt, mmFiber16RowAt, mmFiber16Rows, listGetD, directRow] using h)

theorem mmFiber16ReverseRow_6_ok :
    mmRowReverseValid mmFiber16Key mmFiber16Expected (mmFiber16RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber16Chunk3_ok
  change (mmRowReverseValid mmFiber16Key mmFiber16Expected (mmFiber16RowAt 6) &&
    mmRowReverseValid mmFiber16Key mmFiber16Expected (mmFiber16RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber16ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber16StateAt 2) (mmFiber16StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber16StateAt 2) (mmFiber16StateAt 6)
    (mmFiber16RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber16Key mmFiber16Expected
        (mmFiber16RowAt 6) (by decide) mmFiber16ReverseRow_6_ok
      simpa [mmFiber16StateAt, mmFiber16RowAt, mmFiber16Rows, listGetD, directRow] using h)

theorem mmFiber16ReverseRow_7_ok :
    mmRowReverseValid mmFiber16Key mmFiber16Expected (mmFiber16RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber16Chunk3_ok
  change (mmRowReverseValid mmFiber16Key mmFiber16Expected (mmFiber16RowAt 6) &&
    mmRowReverseValid mmFiber16Key mmFiber16Expected (mmFiber16RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber16ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber16StateAt 3) (mmFiber16StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber16StateAt 3) (mmFiber16StateAt 7)
    (mmFiber16RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber16Key mmFiber16Expected
        (mmFiber16RowAt 7) (by decide) mmFiber16ReverseRow_7_ok
      simpa [mmFiber16StateAt, mmFiber16RowAt, mmFiber16Rows, listGetD, directRow] using h)

theorem mmFiber16State0_in_close :
    mmFiber16StateAt 0 ∈ closeChainFiber mmWord mmFiber16DirectStates mmFiber16DirectStates.length [mmFiber16StateAt 0] := by
  change mmFiber16StateAt 0 ∈ closeChainFiber mmWord mmFiber16DirectStates 8 [mmFiber16StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber16DirectStates 0 8 [mmFiber16StateAt 0] (mmFiber16StateAt 0) (by simp [closeChainFiber])

theorem mmFiber16State1_in_close :
    mmFiber16StateAt 1 ∈ closeChainFiber mmWord mmFiber16DirectStates mmFiber16DirectStates.length [mmFiber16StateAt 0] := by
  have h0 : mmFiber16StateAt 0 ∈ closeChainFiber mmWord mmFiber16DirectStates 0 [mmFiber16StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber16StateAt 1 ∈ closeChainFiber mmWord mmFiber16DirectStates 1 [mmFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber16DirectStates 0 [mmFiber16StateAt 0]
      (mmFiber16StateAt 0) (mmFiber16StateAt 1) (by decide) h0 (by decide)
      mmFiber16ReverseSingleStep1
  change mmFiber16StateAt 1 ∈ closeChainFiber mmWord mmFiber16DirectStates (1 + 7) [mmFiber16StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber16DirectStates 1 7 [mmFiber16StateAt 0] (mmFiber16StateAt 1) h1

theorem mmFiber16State2_in_close :
    mmFiber16StateAt 2 ∈ closeChainFiber mmWord mmFiber16DirectStates mmFiber16DirectStates.length [mmFiber16StateAt 0] := by
  have h0 : mmFiber16StateAt 0 ∈ closeChainFiber mmWord mmFiber16DirectStates 0 [mmFiber16StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber16StateAt 2 ∈ closeChainFiber mmWord mmFiber16DirectStates 1 [mmFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber16DirectStates 0 [mmFiber16StateAt 0]
      (mmFiber16StateAt 0) (mmFiber16StateAt 2) (by decide) h0 (by decide)
      mmFiber16ReverseSingleStep2
  change mmFiber16StateAt 2 ∈ closeChainFiber mmWord mmFiber16DirectStates (1 + 7) [mmFiber16StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber16DirectStates 1 7 [mmFiber16StateAt 0] (mmFiber16StateAt 2) h1

theorem mmFiber16State3_in_close :
    mmFiber16StateAt 3 ∈ closeChainFiber mmWord mmFiber16DirectStates mmFiber16DirectStates.length [mmFiber16StateAt 0] := by
  have h0 : mmFiber16StateAt 0 ∈ closeChainFiber mmWord mmFiber16DirectStates 0 [mmFiber16StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber16StateAt 1 ∈ closeChainFiber mmWord mmFiber16DirectStates 1 [mmFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber16DirectStates 0 [mmFiber16StateAt 0]
      (mmFiber16StateAt 0) (mmFiber16StateAt 1) (by decide) h0 (by decide)
      mmFiber16ReverseSingleStep1
  have h2 : mmFiber16StateAt 3 ∈ closeChainFiber mmWord mmFiber16DirectStates 2 [mmFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber16DirectStates 1 [mmFiber16StateAt 0]
      (mmFiber16StateAt 1) (mmFiber16StateAt 3) (by decide) h1 (by decide)
      mmFiber16ReverseSingleStep3
  change mmFiber16StateAt 3 ∈ closeChainFiber mmWord mmFiber16DirectStates (2 + 6) [mmFiber16StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber16DirectStates 2 6 [mmFiber16StateAt 0] (mmFiber16StateAt 3) h2

theorem mmFiber16State4_in_close :
    mmFiber16StateAt 4 ∈ closeChainFiber mmWord mmFiber16DirectStates mmFiber16DirectStates.length [mmFiber16StateAt 0] := by
  have h0 : mmFiber16StateAt 0 ∈ closeChainFiber mmWord mmFiber16DirectStates 0 [mmFiber16StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber16StateAt 4 ∈ closeChainFiber mmWord mmFiber16DirectStates 1 [mmFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber16DirectStates 0 [mmFiber16StateAt 0]
      (mmFiber16StateAt 0) (mmFiber16StateAt 4) (by decide) h0 (by decide)
      mmFiber16ReverseSingleStep4
  change mmFiber16StateAt 4 ∈ closeChainFiber mmWord mmFiber16DirectStates (1 + 7) [mmFiber16StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber16DirectStates 1 7 [mmFiber16StateAt 0] (mmFiber16StateAt 4) h1

theorem mmFiber16State5_in_close :
    mmFiber16StateAt 5 ∈ closeChainFiber mmWord mmFiber16DirectStates mmFiber16DirectStates.length [mmFiber16StateAt 0] := by
  have h0 : mmFiber16StateAt 0 ∈ closeChainFiber mmWord mmFiber16DirectStates 0 [mmFiber16StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber16StateAt 1 ∈ closeChainFiber mmWord mmFiber16DirectStates 1 [mmFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber16DirectStates 0 [mmFiber16StateAt 0]
      (mmFiber16StateAt 0) (mmFiber16StateAt 1) (by decide) h0 (by decide)
      mmFiber16ReverseSingleStep1
  have h2 : mmFiber16StateAt 5 ∈ closeChainFiber mmWord mmFiber16DirectStates 2 [mmFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber16DirectStates 1 [mmFiber16StateAt 0]
      (mmFiber16StateAt 1) (mmFiber16StateAt 5) (by decide) h1 (by decide)
      mmFiber16ReverseSingleStep5
  change mmFiber16StateAt 5 ∈ closeChainFiber mmWord mmFiber16DirectStates (2 + 6) [mmFiber16StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber16DirectStates 2 6 [mmFiber16StateAt 0] (mmFiber16StateAt 5) h2

theorem mmFiber16State6_in_close :
    mmFiber16StateAt 6 ∈ closeChainFiber mmWord mmFiber16DirectStates mmFiber16DirectStates.length [mmFiber16StateAt 0] := by
  have h0 : mmFiber16StateAt 0 ∈ closeChainFiber mmWord mmFiber16DirectStates 0 [mmFiber16StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber16StateAt 2 ∈ closeChainFiber mmWord mmFiber16DirectStates 1 [mmFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber16DirectStates 0 [mmFiber16StateAt 0]
      (mmFiber16StateAt 0) (mmFiber16StateAt 2) (by decide) h0 (by decide)
      mmFiber16ReverseSingleStep2
  have h2 : mmFiber16StateAt 6 ∈ closeChainFiber mmWord mmFiber16DirectStates 2 [mmFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber16DirectStates 1 [mmFiber16StateAt 0]
      (mmFiber16StateAt 2) (mmFiber16StateAt 6) (by decide) h1 (by decide)
      mmFiber16ReverseSingleStep6
  change mmFiber16StateAt 6 ∈ closeChainFiber mmWord mmFiber16DirectStates (2 + 6) [mmFiber16StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber16DirectStates 2 6 [mmFiber16StateAt 0] (mmFiber16StateAt 6) h2

theorem mmFiber16State7_in_close :
    mmFiber16StateAt 7 ∈ closeChainFiber mmWord mmFiber16DirectStates mmFiber16DirectStates.length [mmFiber16StateAt 0] := by
  have h0 : mmFiber16StateAt 0 ∈ closeChainFiber mmWord mmFiber16DirectStates 0 [mmFiber16StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber16StateAt 1 ∈ closeChainFiber mmWord mmFiber16DirectStates 1 [mmFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber16DirectStates 0 [mmFiber16StateAt 0]
      (mmFiber16StateAt 0) (mmFiber16StateAt 1) (by decide) h0 (by decide)
      mmFiber16ReverseSingleStep1
  have h2 : mmFiber16StateAt 3 ∈ closeChainFiber mmWord mmFiber16DirectStates 2 [mmFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber16DirectStates 1 [mmFiber16StateAt 0]
      (mmFiber16StateAt 1) (mmFiber16StateAt 3) (by decide) h1 (by decide)
      mmFiber16ReverseSingleStep3
  have h3 : mmFiber16StateAt 7 ∈ closeChainFiber mmWord mmFiber16DirectStates 3 [mmFiber16StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber16DirectStates 2 [mmFiber16StateAt 0]
      (mmFiber16StateAt 3) (mmFiber16StateAt 7) (by decide) h2 (by decide)
      mmFiber16ReverseSingleStep7
  change mmFiber16StateAt 7 ∈ closeChainFiber mmWord mmFiber16DirectStates (3 + 5) [mmFiber16StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber16DirectStates 3 5 [mmFiber16StateAt 0] (mmFiber16StateAt 7) h3

theorem mmFiber16DirectConnected :
    chainFiberConnected mmWord mmFiber16DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber16DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber16State0_in_close
  · subst state
    exact mmFiber16State1_in_close
  · subst state
    exact mmFiber16State2_in_close
  · subst state
    exact mmFiber16State3_in_close
  · subst state
    exact mmFiber16State4_in_close
  · subst state
    exact mmFiber16State5_in_close
  · subst state
    exact mmFiber16State6_in_close
  · subst state
    exact mmFiber16State7_in_close
  · cases h
end GoertzelLemma818LengthTwoMMBridge

end Mettapedia.GraphTheory.FourColor
