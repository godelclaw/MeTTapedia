import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for size-8 `mirror,mirror` length-two fibers, group 3

This module proves direct connectedness for generated `mirror,mirror` size-8 fibers from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMMBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorMirrorCertificate
open GoertzelLemma818MirrorMirrorReverseAudit

def mmFiber43StateAt (i : Nat) : List TauState :=
  directStates (mmFiber43RowAt i).sourceLeft (mmFiber43RowAt i).sourceRight

def mmFiber43DirectStates : List (List TauState) :=
  [mmFiber43StateAt 0, mmFiber43StateAt 1, mmFiber43StateAt 2, mmFiber43StateAt 3, mmFiber43StateAt 4, mmFiber43StateAt 5, mmFiber43StateAt 6, mmFiber43StateAt 7]

theorem mmFiber43ReverseRow_1_ok :
    mmRowReverseValid mmFiber43Key mmFiber43Expected (mmFiber43RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber43Chunk0_ok
  change (mmRowReverseValid mmFiber43Key mmFiber43Expected (mmFiber43RowAt 0) &&
    mmRowReverseValid mmFiber43Key mmFiber43Expected (mmFiber43RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber43ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber43StateAt 0) (mmFiber43StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber43StateAt 0) (mmFiber43StateAt 1)
    (mmFiber43RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber43Key mmFiber43Expected
        (mmFiber43RowAt 1) (by decide) mmFiber43ReverseRow_1_ok
      simpa [mmFiber43StateAt, mmFiber43RowAt, mmFiber43Rows, listGetD, directRow] using h)

theorem mmFiber43ReverseRow_2_ok :
    mmRowReverseValid mmFiber43Key mmFiber43Expected (mmFiber43RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber43Chunk1_ok
  change (mmRowReverseValid mmFiber43Key mmFiber43Expected (mmFiber43RowAt 2) &&
    mmRowReverseValid mmFiber43Key mmFiber43Expected (mmFiber43RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber43ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber43StateAt 0) (mmFiber43StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber43StateAt 0) (mmFiber43StateAt 2)
    (mmFiber43RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber43Key mmFiber43Expected
        (mmFiber43RowAt 2) (by decide) mmFiber43ReverseRow_2_ok
      simpa [mmFiber43StateAt, mmFiber43RowAt, mmFiber43Rows, listGetD, directRow] using h)

theorem mmFiber43ReverseRow_3_ok :
    mmRowReverseValid mmFiber43Key mmFiber43Expected (mmFiber43RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber43Chunk1_ok
  change (mmRowReverseValid mmFiber43Key mmFiber43Expected (mmFiber43RowAt 2) &&
    mmRowReverseValid mmFiber43Key mmFiber43Expected (mmFiber43RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber43ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber43StateAt 1) (mmFiber43StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber43StateAt 1) (mmFiber43StateAt 3)
    (mmFiber43RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber43Key mmFiber43Expected
        (mmFiber43RowAt 3) (by decide) mmFiber43ReverseRow_3_ok
      simpa [mmFiber43StateAt, mmFiber43RowAt, mmFiber43Rows, listGetD, directRow] using h)

theorem mmFiber43ReverseRow_4_ok :
    mmRowReverseValid mmFiber43Key mmFiber43Expected (mmFiber43RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber43Chunk2_ok
  change (mmRowReverseValid mmFiber43Key mmFiber43Expected (mmFiber43RowAt 4) &&
    mmRowReverseValid mmFiber43Key mmFiber43Expected (mmFiber43RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber43ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber43StateAt 0) (mmFiber43StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber43StateAt 0) (mmFiber43StateAt 4)
    (mmFiber43RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber43Key mmFiber43Expected
        (mmFiber43RowAt 4) (by decide) mmFiber43ReverseRow_4_ok
      simpa [mmFiber43StateAt, mmFiber43RowAt, mmFiber43Rows, listGetD, directRow] using h)

theorem mmFiber43ReverseRow_5_ok :
    mmRowReverseValid mmFiber43Key mmFiber43Expected (mmFiber43RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber43Chunk2_ok
  change (mmRowReverseValid mmFiber43Key mmFiber43Expected (mmFiber43RowAt 4) &&
    mmRowReverseValid mmFiber43Key mmFiber43Expected (mmFiber43RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber43ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber43StateAt 1) (mmFiber43StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber43StateAt 1) (mmFiber43StateAt 5)
    (mmFiber43RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber43Key mmFiber43Expected
        (mmFiber43RowAt 5) (by decide) mmFiber43ReverseRow_5_ok
      simpa [mmFiber43StateAt, mmFiber43RowAt, mmFiber43Rows, listGetD, directRow] using h)

theorem mmFiber43ReverseRow_6_ok :
    mmRowReverseValid mmFiber43Key mmFiber43Expected (mmFiber43RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber43Chunk3_ok
  change (mmRowReverseValid mmFiber43Key mmFiber43Expected (mmFiber43RowAt 6) &&
    mmRowReverseValid mmFiber43Key mmFiber43Expected (mmFiber43RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber43ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber43StateAt 2) (mmFiber43StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber43StateAt 2) (mmFiber43StateAt 6)
    (mmFiber43RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber43Key mmFiber43Expected
        (mmFiber43RowAt 6) (by decide) mmFiber43ReverseRow_6_ok
      simpa [mmFiber43StateAt, mmFiber43RowAt, mmFiber43Rows, listGetD, directRow] using h)

theorem mmFiber43ReverseRow_7_ok :
    mmRowReverseValid mmFiber43Key mmFiber43Expected (mmFiber43RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber43Chunk3_ok
  change (mmRowReverseValid mmFiber43Key mmFiber43Expected (mmFiber43RowAt 6) &&
    mmRowReverseValid mmFiber43Key mmFiber43Expected (mmFiber43RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber43ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber43StateAt 3) (mmFiber43StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber43StateAt 3) (mmFiber43StateAt 7)
    (mmFiber43RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber43Key mmFiber43Expected
        (mmFiber43RowAt 7) (by decide) mmFiber43ReverseRow_7_ok
      simpa [mmFiber43StateAt, mmFiber43RowAt, mmFiber43Rows, listGetD, directRow] using h)

theorem mmFiber43State0_in_close :
    mmFiber43StateAt 0 ∈ closeChainFiber mmWord mmFiber43DirectStates mmFiber43DirectStates.length [mmFiber43StateAt 0] := by
  change mmFiber43StateAt 0 ∈ closeChainFiber mmWord mmFiber43DirectStates 8 [mmFiber43StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber43DirectStates 0 8 [mmFiber43StateAt 0] (mmFiber43StateAt 0) (by simp [closeChainFiber])

theorem mmFiber43State1_in_close :
    mmFiber43StateAt 1 ∈ closeChainFiber mmWord mmFiber43DirectStates mmFiber43DirectStates.length [mmFiber43StateAt 0] := by
  have h0 : mmFiber43StateAt 0 ∈ closeChainFiber mmWord mmFiber43DirectStates 0 [mmFiber43StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber43StateAt 1 ∈ closeChainFiber mmWord mmFiber43DirectStates 1 [mmFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber43DirectStates 0 [mmFiber43StateAt 0]
      (mmFiber43StateAt 0) (mmFiber43StateAt 1) (by decide) h0 (by decide)
      mmFiber43ReverseSingleStep1
  change mmFiber43StateAt 1 ∈ closeChainFiber mmWord mmFiber43DirectStates (1 + 7) [mmFiber43StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber43DirectStates 1 7 [mmFiber43StateAt 0] (mmFiber43StateAt 1) h1

theorem mmFiber43State2_in_close :
    mmFiber43StateAt 2 ∈ closeChainFiber mmWord mmFiber43DirectStates mmFiber43DirectStates.length [mmFiber43StateAt 0] := by
  have h0 : mmFiber43StateAt 0 ∈ closeChainFiber mmWord mmFiber43DirectStates 0 [mmFiber43StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber43StateAt 2 ∈ closeChainFiber mmWord mmFiber43DirectStates 1 [mmFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber43DirectStates 0 [mmFiber43StateAt 0]
      (mmFiber43StateAt 0) (mmFiber43StateAt 2) (by decide) h0 (by decide)
      mmFiber43ReverseSingleStep2
  change mmFiber43StateAt 2 ∈ closeChainFiber mmWord mmFiber43DirectStates (1 + 7) [mmFiber43StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber43DirectStates 1 7 [mmFiber43StateAt 0] (mmFiber43StateAt 2) h1

theorem mmFiber43State3_in_close :
    mmFiber43StateAt 3 ∈ closeChainFiber mmWord mmFiber43DirectStates mmFiber43DirectStates.length [mmFiber43StateAt 0] := by
  have h0 : mmFiber43StateAt 0 ∈ closeChainFiber mmWord mmFiber43DirectStates 0 [mmFiber43StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber43StateAt 1 ∈ closeChainFiber mmWord mmFiber43DirectStates 1 [mmFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber43DirectStates 0 [mmFiber43StateAt 0]
      (mmFiber43StateAt 0) (mmFiber43StateAt 1) (by decide) h0 (by decide)
      mmFiber43ReverseSingleStep1
  have h2 : mmFiber43StateAt 3 ∈ closeChainFiber mmWord mmFiber43DirectStates 2 [mmFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber43DirectStates 1 [mmFiber43StateAt 0]
      (mmFiber43StateAt 1) (mmFiber43StateAt 3) (by decide) h1 (by decide)
      mmFiber43ReverseSingleStep3
  change mmFiber43StateAt 3 ∈ closeChainFiber mmWord mmFiber43DirectStates (2 + 6) [mmFiber43StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber43DirectStates 2 6 [mmFiber43StateAt 0] (mmFiber43StateAt 3) h2

theorem mmFiber43State4_in_close :
    mmFiber43StateAt 4 ∈ closeChainFiber mmWord mmFiber43DirectStates mmFiber43DirectStates.length [mmFiber43StateAt 0] := by
  have h0 : mmFiber43StateAt 0 ∈ closeChainFiber mmWord mmFiber43DirectStates 0 [mmFiber43StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber43StateAt 4 ∈ closeChainFiber mmWord mmFiber43DirectStates 1 [mmFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber43DirectStates 0 [mmFiber43StateAt 0]
      (mmFiber43StateAt 0) (mmFiber43StateAt 4) (by decide) h0 (by decide)
      mmFiber43ReverseSingleStep4
  change mmFiber43StateAt 4 ∈ closeChainFiber mmWord mmFiber43DirectStates (1 + 7) [mmFiber43StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber43DirectStates 1 7 [mmFiber43StateAt 0] (mmFiber43StateAt 4) h1

theorem mmFiber43State5_in_close :
    mmFiber43StateAt 5 ∈ closeChainFiber mmWord mmFiber43DirectStates mmFiber43DirectStates.length [mmFiber43StateAt 0] := by
  have h0 : mmFiber43StateAt 0 ∈ closeChainFiber mmWord mmFiber43DirectStates 0 [mmFiber43StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber43StateAt 1 ∈ closeChainFiber mmWord mmFiber43DirectStates 1 [mmFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber43DirectStates 0 [mmFiber43StateAt 0]
      (mmFiber43StateAt 0) (mmFiber43StateAt 1) (by decide) h0 (by decide)
      mmFiber43ReverseSingleStep1
  have h2 : mmFiber43StateAt 5 ∈ closeChainFiber mmWord mmFiber43DirectStates 2 [mmFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber43DirectStates 1 [mmFiber43StateAt 0]
      (mmFiber43StateAt 1) (mmFiber43StateAt 5) (by decide) h1 (by decide)
      mmFiber43ReverseSingleStep5
  change mmFiber43StateAt 5 ∈ closeChainFiber mmWord mmFiber43DirectStates (2 + 6) [mmFiber43StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber43DirectStates 2 6 [mmFiber43StateAt 0] (mmFiber43StateAt 5) h2

theorem mmFiber43State6_in_close :
    mmFiber43StateAt 6 ∈ closeChainFiber mmWord mmFiber43DirectStates mmFiber43DirectStates.length [mmFiber43StateAt 0] := by
  have h0 : mmFiber43StateAt 0 ∈ closeChainFiber mmWord mmFiber43DirectStates 0 [mmFiber43StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber43StateAt 2 ∈ closeChainFiber mmWord mmFiber43DirectStates 1 [mmFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber43DirectStates 0 [mmFiber43StateAt 0]
      (mmFiber43StateAt 0) (mmFiber43StateAt 2) (by decide) h0 (by decide)
      mmFiber43ReverseSingleStep2
  have h2 : mmFiber43StateAt 6 ∈ closeChainFiber mmWord mmFiber43DirectStates 2 [mmFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber43DirectStates 1 [mmFiber43StateAt 0]
      (mmFiber43StateAt 2) (mmFiber43StateAt 6) (by decide) h1 (by decide)
      mmFiber43ReverseSingleStep6
  change mmFiber43StateAt 6 ∈ closeChainFiber mmWord mmFiber43DirectStates (2 + 6) [mmFiber43StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber43DirectStates 2 6 [mmFiber43StateAt 0] (mmFiber43StateAt 6) h2

theorem mmFiber43State7_in_close :
    mmFiber43StateAt 7 ∈ closeChainFiber mmWord mmFiber43DirectStates mmFiber43DirectStates.length [mmFiber43StateAt 0] := by
  have h0 : mmFiber43StateAt 0 ∈ closeChainFiber mmWord mmFiber43DirectStates 0 [mmFiber43StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber43StateAt 1 ∈ closeChainFiber mmWord mmFiber43DirectStates 1 [mmFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber43DirectStates 0 [mmFiber43StateAt 0]
      (mmFiber43StateAt 0) (mmFiber43StateAt 1) (by decide) h0 (by decide)
      mmFiber43ReverseSingleStep1
  have h2 : mmFiber43StateAt 3 ∈ closeChainFiber mmWord mmFiber43DirectStates 2 [mmFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber43DirectStates 1 [mmFiber43StateAt 0]
      (mmFiber43StateAt 1) (mmFiber43StateAt 3) (by decide) h1 (by decide)
      mmFiber43ReverseSingleStep3
  have h3 : mmFiber43StateAt 7 ∈ closeChainFiber mmWord mmFiber43DirectStates 3 [mmFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber43DirectStates 2 [mmFiber43StateAt 0]
      (mmFiber43StateAt 3) (mmFiber43StateAt 7) (by decide) h2 (by decide)
      mmFiber43ReverseSingleStep7
  change mmFiber43StateAt 7 ∈ closeChainFiber mmWord mmFiber43DirectStates (3 + 5) [mmFiber43StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber43DirectStates 3 5 [mmFiber43StateAt 0] (mmFiber43StateAt 7) h3

theorem mmFiber43DirectConnected :
    chainFiberConnected mmWord mmFiber43DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber43DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber43State0_in_close
  · subst state
    exact mmFiber43State1_in_close
  · subst state
    exact mmFiber43State2_in_close
  · subst state
    exact mmFiber43State3_in_close
  · subst state
    exact mmFiber43State4_in_close
  · subst state
    exact mmFiber43State5_in_close
  · subst state
    exact mmFiber43State6_in_close
  · subst state
    exact mmFiber43State7_in_close
  · cases h
def mmFiber45StateAt (i : Nat) : List TauState :=
  directStates (mmFiber45RowAt i).sourceLeft (mmFiber45RowAt i).sourceRight

def mmFiber45DirectStates : List (List TauState) :=
  [mmFiber45StateAt 0, mmFiber45StateAt 1, mmFiber45StateAt 2, mmFiber45StateAt 3, mmFiber45StateAt 4, mmFiber45StateAt 5, mmFiber45StateAt 6, mmFiber45StateAt 7]

theorem mmFiber45ReverseRow_1_ok :
    mmRowReverseValid mmFiber45Key mmFiber45Expected (mmFiber45RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber45Chunk0_ok
  change (mmRowReverseValid mmFiber45Key mmFiber45Expected (mmFiber45RowAt 0) &&
    mmRowReverseValid mmFiber45Key mmFiber45Expected (mmFiber45RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber45ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber45StateAt 0) (mmFiber45StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber45StateAt 0) (mmFiber45StateAt 1)
    (mmFiber45RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber45Key mmFiber45Expected
        (mmFiber45RowAt 1) (by decide) mmFiber45ReverseRow_1_ok
      simpa [mmFiber45StateAt, mmFiber45RowAt, mmFiber45Rows, listGetD, directRow] using h)

theorem mmFiber45ReverseRow_2_ok :
    mmRowReverseValid mmFiber45Key mmFiber45Expected (mmFiber45RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber45Chunk1_ok
  change (mmRowReverseValid mmFiber45Key mmFiber45Expected (mmFiber45RowAt 2) &&
    mmRowReverseValid mmFiber45Key mmFiber45Expected (mmFiber45RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber45ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber45StateAt 0) (mmFiber45StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber45StateAt 0) (mmFiber45StateAt 2)
    (mmFiber45RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber45Key mmFiber45Expected
        (mmFiber45RowAt 2) (by decide) mmFiber45ReverseRow_2_ok
      simpa [mmFiber45StateAt, mmFiber45RowAt, mmFiber45Rows, listGetD, directRow] using h)

theorem mmFiber45ReverseRow_3_ok :
    mmRowReverseValid mmFiber45Key mmFiber45Expected (mmFiber45RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber45Chunk1_ok
  change (mmRowReverseValid mmFiber45Key mmFiber45Expected (mmFiber45RowAt 2) &&
    mmRowReverseValid mmFiber45Key mmFiber45Expected (mmFiber45RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber45ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber45StateAt 1) (mmFiber45StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber45StateAt 1) (mmFiber45StateAt 3)
    (mmFiber45RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber45Key mmFiber45Expected
        (mmFiber45RowAt 3) (by decide) mmFiber45ReverseRow_3_ok
      simpa [mmFiber45StateAt, mmFiber45RowAt, mmFiber45Rows, listGetD, directRow] using h)

theorem mmFiber45ReverseRow_4_ok :
    mmRowReverseValid mmFiber45Key mmFiber45Expected (mmFiber45RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber45Chunk2_ok
  change (mmRowReverseValid mmFiber45Key mmFiber45Expected (mmFiber45RowAt 4) &&
    mmRowReverseValid mmFiber45Key mmFiber45Expected (mmFiber45RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber45ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber45StateAt 0) (mmFiber45StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber45StateAt 0) (mmFiber45StateAt 4)
    (mmFiber45RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber45Key mmFiber45Expected
        (mmFiber45RowAt 4) (by decide) mmFiber45ReverseRow_4_ok
      simpa [mmFiber45StateAt, mmFiber45RowAt, mmFiber45Rows, listGetD, directRow] using h)

theorem mmFiber45ReverseRow_5_ok :
    mmRowReverseValid mmFiber45Key mmFiber45Expected (mmFiber45RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber45Chunk2_ok
  change (mmRowReverseValid mmFiber45Key mmFiber45Expected (mmFiber45RowAt 4) &&
    mmRowReverseValid mmFiber45Key mmFiber45Expected (mmFiber45RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber45ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber45StateAt 1) (mmFiber45StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber45StateAt 1) (mmFiber45StateAt 5)
    (mmFiber45RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber45Key mmFiber45Expected
        (mmFiber45RowAt 5) (by decide) mmFiber45ReverseRow_5_ok
      simpa [mmFiber45StateAt, mmFiber45RowAt, mmFiber45Rows, listGetD, directRow] using h)

theorem mmFiber45ReverseRow_6_ok :
    mmRowReverseValid mmFiber45Key mmFiber45Expected (mmFiber45RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber45Chunk3_ok
  change (mmRowReverseValid mmFiber45Key mmFiber45Expected (mmFiber45RowAt 6) &&
    mmRowReverseValid mmFiber45Key mmFiber45Expected (mmFiber45RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber45ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber45StateAt 2) (mmFiber45StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber45StateAt 2) (mmFiber45StateAt 6)
    (mmFiber45RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber45Key mmFiber45Expected
        (mmFiber45RowAt 6) (by decide) mmFiber45ReverseRow_6_ok
      simpa [mmFiber45StateAt, mmFiber45RowAt, mmFiber45Rows, listGetD, directRow] using h)

theorem mmFiber45ReverseRow_7_ok :
    mmRowReverseValid mmFiber45Key mmFiber45Expected (mmFiber45RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber45Chunk3_ok
  change (mmRowReverseValid mmFiber45Key mmFiber45Expected (mmFiber45RowAt 6) &&
    mmRowReverseValid mmFiber45Key mmFiber45Expected (mmFiber45RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber45ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber45StateAt 3) (mmFiber45StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber45StateAt 3) (mmFiber45StateAt 7)
    (mmFiber45RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber45Key mmFiber45Expected
        (mmFiber45RowAt 7) (by decide) mmFiber45ReverseRow_7_ok
      simpa [mmFiber45StateAt, mmFiber45RowAt, mmFiber45Rows, listGetD, directRow] using h)

theorem mmFiber45State0_in_close :
    mmFiber45StateAt 0 ∈ closeChainFiber mmWord mmFiber45DirectStates mmFiber45DirectStates.length [mmFiber45StateAt 0] := by
  change mmFiber45StateAt 0 ∈ closeChainFiber mmWord mmFiber45DirectStates 8 [mmFiber45StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber45DirectStates 0 8 [mmFiber45StateAt 0] (mmFiber45StateAt 0) (by simp [closeChainFiber])

theorem mmFiber45State1_in_close :
    mmFiber45StateAt 1 ∈ closeChainFiber mmWord mmFiber45DirectStates mmFiber45DirectStates.length [mmFiber45StateAt 0] := by
  have h0 : mmFiber45StateAt 0 ∈ closeChainFiber mmWord mmFiber45DirectStates 0 [mmFiber45StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber45StateAt 1 ∈ closeChainFiber mmWord mmFiber45DirectStates 1 [mmFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber45DirectStates 0 [mmFiber45StateAt 0]
      (mmFiber45StateAt 0) (mmFiber45StateAt 1) (by decide) h0 (by decide)
      mmFiber45ReverseSingleStep1
  change mmFiber45StateAt 1 ∈ closeChainFiber mmWord mmFiber45DirectStates (1 + 7) [mmFiber45StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber45DirectStates 1 7 [mmFiber45StateAt 0] (mmFiber45StateAt 1) h1

theorem mmFiber45State2_in_close :
    mmFiber45StateAt 2 ∈ closeChainFiber mmWord mmFiber45DirectStates mmFiber45DirectStates.length [mmFiber45StateAt 0] := by
  have h0 : mmFiber45StateAt 0 ∈ closeChainFiber mmWord mmFiber45DirectStates 0 [mmFiber45StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber45StateAt 2 ∈ closeChainFiber mmWord mmFiber45DirectStates 1 [mmFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber45DirectStates 0 [mmFiber45StateAt 0]
      (mmFiber45StateAt 0) (mmFiber45StateAt 2) (by decide) h0 (by decide)
      mmFiber45ReverseSingleStep2
  change mmFiber45StateAt 2 ∈ closeChainFiber mmWord mmFiber45DirectStates (1 + 7) [mmFiber45StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber45DirectStates 1 7 [mmFiber45StateAt 0] (mmFiber45StateAt 2) h1

theorem mmFiber45State3_in_close :
    mmFiber45StateAt 3 ∈ closeChainFiber mmWord mmFiber45DirectStates mmFiber45DirectStates.length [mmFiber45StateAt 0] := by
  have h0 : mmFiber45StateAt 0 ∈ closeChainFiber mmWord mmFiber45DirectStates 0 [mmFiber45StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber45StateAt 1 ∈ closeChainFiber mmWord mmFiber45DirectStates 1 [mmFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber45DirectStates 0 [mmFiber45StateAt 0]
      (mmFiber45StateAt 0) (mmFiber45StateAt 1) (by decide) h0 (by decide)
      mmFiber45ReverseSingleStep1
  have h2 : mmFiber45StateAt 3 ∈ closeChainFiber mmWord mmFiber45DirectStates 2 [mmFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber45DirectStates 1 [mmFiber45StateAt 0]
      (mmFiber45StateAt 1) (mmFiber45StateAt 3) (by decide) h1 (by decide)
      mmFiber45ReverseSingleStep3
  change mmFiber45StateAt 3 ∈ closeChainFiber mmWord mmFiber45DirectStates (2 + 6) [mmFiber45StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber45DirectStates 2 6 [mmFiber45StateAt 0] (mmFiber45StateAt 3) h2

theorem mmFiber45State4_in_close :
    mmFiber45StateAt 4 ∈ closeChainFiber mmWord mmFiber45DirectStates mmFiber45DirectStates.length [mmFiber45StateAt 0] := by
  have h0 : mmFiber45StateAt 0 ∈ closeChainFiber mmWord mmFiber45DirectStates 0 [mmFiber45StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber45StateAt 4 ∈ closeChainFiber mmWord mmFiber45DirectStates 1 [mmFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber45DirectStates 0 [mmFiber45StateAt 0]
      (mmFiber45StateAt 0) (mmFiber45StateAt 4) (by decide) h0 (by decide)
      mmFiber45ReverseSingleStep4
  change mmFiber45StateAt 4 ∈ closeChainFiber mmWord mmFiber45DirectStates (1 + 7) [mmFiber45StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber45DirectStates 1 7 [mmFiber45StateAt 0] (mmFiber45StateAt 4) h1

theorem mmFiber45State5_in_close :
    mmFiber45StateAt 5 ∈ closeChainFiber mmWord mmFiber45DirectStates mmFiber45DirectStates.length [mmFiber45StateAt 0] := by
  have h0 : mmFiber45StateAt 0 ∈ closeChainFiber mmWord mmFiber45DirectStates 0 [mmFiber45StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber45StateAt 1 ∈ closeChainFiber mmWord mmFiber45DirectStates 1 [mmFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber45DirectStates 0 [mmFiber45StateAt 0]
      (mmFiber45StateAt 0) (mmFiber45StateAt 1) (by decide) h0 (by decide)
      mmFiber45ReverseSingleStep1
  have h2 : mmFiber45StateAt 5 ∈ closeChainFiber mmWord mmFiber45DirectStates 2 [mmFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber45DirectStates 1 [mmFiber45StateAt 0]
      (mmFiber45StateAt 1) (mmFiber45StateAt 5) (by decide) h1 (by decide)
      mmFiber45ReverseSingleStep5
  change mmFiber45StateAt 5 ∈ closeChainFiber mmWord mmFiber45DirectStates (2 + 6) [mmFiber45StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber45DirectStates 2 6 [mmFiber45StateAt 0] (mmFiber45StateAt 5) h2

theorem mmFiber45State6_in_close :
    mmFiber45StateAt 6 ∈ closeChainFiber mmWord mmFiber45DirectStates mmFiber45DirectStates.length [mmFiber45StateAt 0] := by
  have h0 : mmFiber45StateAt 0 ∈ closeChainFiber mmWord mmFiber45DirectStates 0 [mmFiber45StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber45StateAt 2 ∈ closeChainFiber mmWord mmFiber45DirectStates 1 [mmFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber45DirectStates 0 [mmFiber45StateAt 0]
      (mmFiber45StateAt 0) (mmFiber45StateAt 2) (by decide) h0 (by decide)
      mmFiber45ReverseSingleStep2
  have h2 : mmFiber45StateAt 6 ∈ closeChainFiber mmWord mmFiber45DirectStates 2 [mmFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber45DirectStates 1 [mmFiber45StateAt 0]
      (mmFiber45StateAt 2) (mmFiber45StateAt 6) (by decide) h1 (by decide)
      mmFiber45ReverseSingleStep6
  change mmFiber45StateAt 6 ∈ closeChainFiber mmWord mmFiber45DirectStates (2 + 6) [mmFiber45StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber45DirectStates 2 6 [mmFiber45StateAt 0] (mmFiber45StateAt 6) h2

theorem mmFiber45State7_in_close :
    mmFiber45StateAt 7 ∈ closeChainFiber mmWord mmFiber45DirectStates mmFiber45DirectStates.length [mmFiber45StateAt 0] := by
  have h0 : mmFiber45StateAt 0 ∈ closeChainFiber mmWord mmFiber45DirectStates 0 [mmFiber45StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber45StateAt 1 ∈ closeChainFiber mmWord mmFiber45DirectStates 1 [mmFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber45DirectStates 0 [mmFiber45StateAt 0]
      (mmFiber45StateAt 0) (mmFiber45StateAt 1) (by decide) h0 (by decide)
      mmFiber45ReverseSingleStep1
  have h2 : mmFiber45StateAt 3 ∈ closeChainFiber mmWord mmFiber45DirectStates 2 [mmFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber45DirectStates 1 [mmFiber45StateAt 0]
      (mmFiber45StateAt 1) (mmFiber45StateAt 3) (by decide) h1 (by decide)
      mmFiber45ReverseSingleStep3
  have h3 : mmFiber45StateAt 7 ∈ closeChainFiber mmWord mmFiber45DirectStates 3 [mmFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber45DirectStates 2 [mmFiber45StateAt 0]
      (mmFiber45StateAt 3) (mmFiber45StateAt 7) (by decide) h2 (by decide)
      mmFiber45ReverseSingleStep7
  change mmFiber45StateAt 7 ∈ closeChainFiber mmWord mmFiber45DirectStates (3 + 5) [mmFiber45StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber45DirectStates 3 5 [mmFiber45StateAt 0] (mmFiber45StateAt 7) h3

theorem mmFiber45DirectConnected :
    chainFiberConnected mmWord mmFiber45DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber45DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber45State0_in_close
  · subst state
    exact mmFiber45State1_in_close
  · subst state
    exact mmFiber45State2_in_close
  · subst state
    exact mmFiber45State3_in_close
  · subst state
    exact mmFiber45State4_in_close
  · subst state
    exact mmFiber45State5_in_close
  · subst state
    exact mmFiber45State6_in_close
  · subst state
    exact mmFiber45State7_in_close
  · cases h
def mmFiber47StateAt (i : Nat) : List TauState :=
  directStates (mmFiber47RowAt i).sourceLeft (mmFiber47RowAt i).sourceRight

def mmFiber47DirectStates : List (List TauState) :=
  [mmFiber47StateAt 0, mmFiber47StateAt 1, mmFiber47StateAt 2, mmFiber47StateAt 3, mmFiber47StateAt 4, mmFiber47StateAt 5, mmFiber47StateAt 6, mmFiber47StateAt 7]

theorem mmFiber47ReverseRow_1_ok :
    mmRowReverseValid mmFiber47Key mmFiber47Expected (mmFiber47RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber47Chunk0_ok
  change (mmRowReverseValid mmFiber47Key mmFiber47Expected (mmFiber47RowAt 0) &&
    mmRowReverseValid mmFiber47Key mmFiber47Expected (mmFiber47RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber47ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber47StateAt 0) (mmFiber47StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber47StateAt 0) (mmFiber47StateAt 1)
    (mmFiber47RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber47Key mmFiber47Expected
        (mmFiber47RowAt 1) (by decide) mmFiber47ReverseRow_1_ok
      simpa [mmFiber47StateAt, mmFiber47RowAt, mmFiber47Rows, listGetD, directRow] using h)

theorem mmFiber47ReverseRow_2_ok :
    mmRowReverseValid mmFiber47Key mmFiber47Expected (mmFiber47RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber47Chunk1_ok
  change (mmRowReverseValid mmFiber47Key mmFiber47Expected (mmFiber47RowAt 2) &&
    mmRowReverseValid mmFiber47Key mmFiber47Expected (mmFiber47RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber47ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber47StateAt 0) (mmFiber47StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber47StateAt 0) (mmFiber47StateAt 2)
    (mmFiber47RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber47Key mmFiber47Expected
        (mmFiber47RowAt 2) (by decide) mmFiber47ReverseRow_2_ok
      simpa [mmFiber47StateAt, mmFiber47RowAt, mmFiber47Rows, listGetD, directRow] using h)

theorem mmFiber47ReverseRow_3_ok :
    mmRowReverseValid mmFiber47Key mmFiber47Expected (mmFiber47RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber47Chunk1_ok
  change (mmRowReverseValid mmFiber47Key mmFiber47Expected (mmFiber47RowAt 2) &&
    mmRowReverseValid mmFiber47Key mmFiber47Expected (mmFiber47RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber47ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber47StateAt 1) (mmFiber47StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber47StateAt 1) (mmFiber47StateAt 3)
    (mmFiber47RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber47Key mmFiber47Expected
        (mmFiber47RowAt 3) (by decide) mmFiber47ReverseRow_3_ok
      simpa [mmFiber47StateAt, mmFiber47RowAt, mmFiber47Rows, listGetD, directRow] using h)

theorem mmFiber47ReverseRow_4_ok :
    mmRowReverseValid mmFiber47Key mmFiber47Expected (mmFiber47RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber47Chunk2_ok
  change (mmRowReverseValid mmFiber47Key mmFiber47Expected (mmFiber47RowAt 4) &&
    mmRowReverseValid mmFiber47Key mmFiber47Expected (mmFiber47RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber47ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber47StateAt 0) (mmFiber47StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber47StateAt 0) (mmFiber47StateAt 4)
    (mmFiber47RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber47Key mmFiber47Expected
        (mmFiber47RowAt 4) (by decide) mmFiber47ReverseRow_4_ok
      simpa [mmFiber47StateAt, mmFiber47RowAt, mmFiber47Rows, listGetD, directRow] using h)

theorem mmFiber47ReverseRow_5_ok :
    mmRowReverseValid mmFiber47Key mmFiber47Expected (mmFiber47RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber47Chunk2_ok
  change (mmRowReverseValid mmFiber47Key mmFiber47Expected (mmFiber47RowAt 4) &&
    mmRowReverseValid mmFiber47Key mmFiber47Expected (mmFiber47RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber47ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber47StateAt 1) (mmFiber47StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber47StateAt 1) (mmFiber47StateAt 5)
    (mmFiber47RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber47Key mmFiber47Expected
        (mmFiber47RowAt 5) (by decide) mmFiber47ReverseRow_5_ok
      simpa [mmFiber47StateAt, mmFiber47RowAt, mmFiber47Rows, listGetD, directRow] using h)

theorem mmFiber47ReverseRow_6_ok :
    mmRowReverseValid mmFiber47Key mmFiber47Expected (mmFiber47RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber47Chunk3_ok
  change (mmRowReverseValid mmFiber47Key mmFiber47Expected (mmFiber47RowAt 6) &&
    mmRowReverseValid mmFiber47Key mmFiber47Expected (mmFiber47RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber47ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber47StateAt 2) (mmFiber47StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber47StateAt 2) (mmFiber47StateAt 6)
    (mmFiber47RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber47Key mmFiber47Expected
        (mmFiber47RowAt 6) (by decide) mmFiber47ReverseRow_6_ok
      simpa [mmFiber47StateAt, mmFiber47RowAt, mmFiber47Rows, listGetD, directRow] using h)

theorem mmFiber47ReverseRow_7_ok :
    mmRowReverseValid mmFiber47Key mmFiber47Expected (mmFiber47RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber47Chunk3_ok
  change (mmRowReverseValid mmFiber47Key mmFiber47Expected (mmFiber47RowAt 6) &&
    mmRowReverseValid mmFiber47Key mmFiber47Expected (mmFiber47RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber47ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber47StateAt 3) (mmFiber47StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber47StateAt 3) (mmFiber47StateAt 7)
    (mmFiber47RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber47Key mmFiber47Expected
        (mmFiber47RowAt 7) (by decide) mmFiber47ReverseRow_7_ok
      simpa [mmFiber47StateAt, mmFiber47RowAt, mmFiber47Rows, listGetD, directRow] using h)

theorem mmFiber47State0_in_close :
    mmFiber47StateAt 0 ∈ closeChainFiber mmWord mmFiber47DirectStates mmFiber47DirectStates.length [mmFiber47StateAt 0] := by
  change mmFiber47StateAt 0 ∈ closeChainFiber mmWord mmFiber47DirectStates 8 [mmFiber47StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber47DirectStates 0 8 [mmFiber47StateAt 0] (mmFiber47StateAt 0) (by simp [closeChainFiber])

theorem mmFiber47State1_in_close :
    mmFiber47StateAt 1 ∈ closeChainFiber mmWord mmFiber47DirectStates mmFiber47DirectStates.length [mmFiber47StateAt 0] := by
  have h0 : mmFiber47StateAt 0 ∈ closeChainFiber mmWord mmFiber47DirectStates 0 [mmFiber47StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber47StateAt 1 ∈ closeChainFiber mmWord mmFiber47DirectStates 1 [mmFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber47DirectStates 0 [mmFiber47StateAt 0]
      (mmFiber47StateAt 0) (mmFiber47StateAt 1) (by decide) h0 (by decide)
      mmFiber47ReverseSingleStep1
  change mmFiber47StateAt 1 ∈ closeChainFiber mmWord mmFiber47DirectStates (1 + 7) [mmFiber47StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber47DirectStates 1 7 [mmFiber47StateAt 0] (mmFiber47StateAt 1) h1

theorem mmFiber47State2_in_close :
    mmFiber47StateAt 2 ∈ closeChainFiber mmWord mmFiber47DirectStates mmFiber47DirectStates.length [mmFiber47StateAt 0] := by
  have h0 : mmFiber47StateAt 0 ∈ closeChainFiber mmWord mmFiber47DirectStates 0 [mmFiber47StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber47StateAt 2 ∈ closeChainFiber mmWord mmFiber47DirectStates 1 [mmFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber47DirectStates 0 [mmFiber47StateAt 0]
      (mmFiber47StateAt 0) (mmFiber47StateAt 2) (by decide) h0 (by decide)
      mmFiber47ReverseSingleStep2
  change mmFiber47StateAt 2 ∈ closeChainFiber mmWord mmFiber47DirectStates (1 + 7) [mmFiber47StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber47DirectStates 1 7 [mmFiber47StateAt 0] (mmFiber47StateAt 2) h1

theorem mmFiber47State3_in_close :
    mmFiber47StateAt 3 ∈ closeChainFiber mmWord mmFiber47DirectStates mmFiber47DirectStates.length [mmFiber47StateAt 0] := by
  have h0 : mmFiber47StateAt 0 ∈ closeChainFiber mmWord mmFiber47DirectStates 0 [mmFiber47StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber47StateAt 1 ∈ closeChainFiber mmWord mmFiber47DirectStates 1 [mmFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber47DirectStates 0 [mmFiber47StateAt 0]
      (mmFiber47StateAt 0) (mmFiber47StateAt 1) (by decide) h0 (by decide)
      mmFiber47ReverseSingleStep1
  have h2 : mmFiber47StateAt 3 ∈ closeChainFiber mmWord mmFiber47DirectStates 2 [mmFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber47DirectStates 1 [mmFiber47StateAt 0]
      (mmFiber47StateAt 1) (mmFiber47StateAt 3) (by decide) h1 (by decide)
      mmFiber47ReverseSingleStep3
  change mmFiber47StateAt 3 ∈ closeChainFiber mmWord mmFiber47DirectStates (2 + 6) [mmFiber47StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber47DirectStates 2 6 [mmFiber47StateAt 0] (mmFiber47StateAt 3) h2

theorem mmFiber47State4_in_close :
    mmFiber47StateAt 4 ∈ closeChainFiber mmWord mmFiber47DirectStates mmFiber47DirectStates.length [mmFiber47StateAt 0] := by
  have h0 : mmFiber47StateAt 0 ∈ closeChainFiber mmWord mmFiber47DirectStates 0 [mmFiber47StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber47StateAt 4 ∈ closeChainFiber mmWord mmFiber47DirectStates 1 [mmFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber47DirectStates 0 [mmFiber47StateAt 0]
      (mmFiber47StateAt 0) (mmFiber47StateAt 4) (by decide) h0 (by decide)
      mmFiber47ReverseSingleStep4
  change mmFiber47StateAt 4 ∈ closeChainFiber mmWord mmFiber47DirectStates (1 + 7) [mmFiber47StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber47DirectStates 1 7 [mmFiber47StateAt 0] (mmFiber47StateAt 4) h1

theorem mmFiber47State5_in_close :
    mmFiber47StateAt 5 ∈ closeChainFiber mmWord mmFiber47DirectStates mmFiber47DirectStates.length [mmFiber47StateAt 0] := by
  have h0 : mmFiber47StateAt 0 ∈ closeChainFiber mmWord mmFiber47DirectStates 0 [mmFiber47StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber47StateAt 1 ∈ closeChainFiber mmWord mmFiber47DirectStates 1 [mmFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber47DirectStates 0 [mmFiber47StateAt 0]
      (mmFiber47StateAt 0) (mmFiber47StateAt 1) (by decide) h0 (by decide)
      mmFiber47ReverseSingleStep1
  have h2 : mmFiber47StateAt 5 ∈ closeChainFiber mmWord mmFiber47DirectStates 2 [mmFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber47DirectStates 1 [mmFiber47StateAt 0]
      (mmFiber47StateAt 1) (mmFiber47StateAt 5) (by decide) h1 (by decide)
      mmFiber47ReverseSingleStep5
  change mmFiber47StateAt 5 ∈ closeChainFiber mmWord mmFiber47DirectStates (2 + 6) [mmFiber47StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber47DirectStates 2 6 [mmFiber47StateAt 0] (mmFiber47StateAt 5) h2

theorem mmFiber47State6_in_close :
    mmFiber47StateAt 6 ∈ closeChainFiber mmWord mmFiber47DirectStates mmFiber47DirectStates.length [mmFiber47StateAt 0] := by
  have h0 : mmFiber47StateAt 0 ∈ closeChainFiber mmWord mmFiber47DirectStates 0 [mmFiber47StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber47StateAt 2 ∈ closeChainFiber mmWord mmFiber47DirectStates 1 [mmFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber47DirectStates 0 [mmFiber47StateAt 0]
      (mmFiber47StateAt 0) (mmFiber47StateAt 2) (by decide) h0 (by decide)
      mmFiber47ReverseSingleStep2
  have h2 : mmFiber47StateAt 6 ∈ closeChainFiber mmWord mmFiber47DirectStates 2 [mmFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber47DirectStates 1 [mmFiber47StateAt 0]
      (mmFiber47StateAt 2) (mmFiber47StateAt 6) (by decide) h1 (by decide)
      mmFiber47ReverseSingleStep6
  change mmFiber47StateAt 6 ∈ closeChainFiber mmWord mmFiber47DirectStates (2 + 6) [mmFiber47StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber47DirectStates 2 6 [mmFiber47StateAt 0] (mmFiber47StateAt 6) h2

theorem mmFiber47State7_in_close :
    mmFiber47StateAt 7 ∈ closeChainFiber mmWord mmFiber47DirectStates mmFiber47DirectStates.length [mmFiber47StateAt 0] := by
  have h0 : mmFiber47StateAt 0 ∈ closeChainFiber mmWord mmFiber47DirectStates 0 [mmFiber47StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber47StateAt 1 ∈ closeChainFiber mmWord mmFiber47DirectStates 1 [mmFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber47DirectStates 0 [mmFiber47StateAt 0]
      (mmFiber47StateAt 0) (mmFiber47StateAt 1) (by decide) h0 (by decide)
      mmFiber47ReverseSingleStep1
  have h2 : mmFiber47StateAt 3 ∈ closeChainFiber mmWord mmFiber47DirectStates 2 [mmFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber47DirectStates 1 [mmFiber47StateAt 0]
      (mmFiber47StateAt 1) (mmFiber47StateAt 3) (by decide) h1 (by decide)
      mmFiber47ReverseSingleStep3
  have h3 : mmFiber47StateAt 7 ∈ closeChainFiber mmWord mmFiber47DirectStates 3 [mmFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber47DirectStates 2 [mmFiber47StateAt 0]
      (mmFiber47StateAt 3) (mmFiber47StateAt 7) (by decide) h2 (by decide)
      mmFiber47ReverseSingleStep7
  change mmFiber47StateAt 7 ∈ closeChainFiber mmWord mmFiber47DirectStates (3 + 5) [mmFiber47StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber47DirectStates 3 5 [mmFiber47StateAt 0] (mmFiber47StateAt 7) h3

theorem mmFiber47DirectConnected :
    chainFiberConnected mmWord mmFiber47DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber47DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber47State0_in_close
  · subst state
    exact mmFiber47State1_in_close
  · subst state
    exact mmFiber47State2_in_close
  · subst state
    exact mmFiber47State3_in_close
  · subst state
    exact mmFiber47State4_in_close
  · subst state
    exact mmFiber47State5_in_close
  · subst state
    exact mmFiber47State6_in_close
  · subst state
    exact mmFiber47State7_in_close
  · cases h
def mmFiber49StateAt (i : Nat) : List TauState :=
  directStates (mmFiber49RowAt i).sourceLeft (mmFiber49RowAt i).sourceRight

def mmFiber49DirectStates : List (List TauState) :=
  [mmFiber49StateAt 0, mmFiber49StateAt 1, mmFiber49StateAt 2, mmFiber49StateAt 3, mmFiber49StateAt 4, mmFiber49StateAt 5, mmFiber49StateAt 6, mmFiber49StateAt 7]

theorem mmFiber49ReverseRow_1_ok :
    mmRowReverseValid mmFiber49Key mmFiber49Expected (mmFiber49RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber49Chunk0_ok
  change (mmRowReverseValid mmFiber49Key mmFiber49Expected (mmFiber49RowAt 0) &&
    mmRowReverseValid mmFiber49Key mmFiber49Expected (mmFiber49RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber49ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber49StateAt 0) (mmFiber49StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber49StateAt 0) (mmFiber49StateAt 1)
    (mmFiber49RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber49Key mmFiber49Expected
        (mmFiber49RowAt 1) (by decide) mmFiber49ReverseRow_1_ok
      simpa [mmFiber49StateAt, mmFiber49RowAt, mmFiber49Rows, listGetD, directRow] using h)

theorem mmFiber49ReverseRow_2_ok :
    mmRowReverseValid mmFiber49Key mmFiber49Expected (mmFiber49RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber49Chunk1_ok
  change (mmRowReverseValid mmFiber49Key mmFiber49Expected (mmFiber49RowAt 2) &&
    mmRowReverseValid mmFiber49Key mmFiber49Expected (mmFiber49RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber49ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber49StateAt 0) (mmFiber49StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber49StateAt 0) (mmFiber49StateAt 2)
    (mmFiber49RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber49Key mmFiber49Expected
        (mmFiber49RowAt 2) (by decide) mmFiber49ReverseRow_2_ok
      simpa [mmFiber49StateAt, mmFiber49RowAt, mmFiber49Rows, listGetD, directRow] using h)

theorem mmFiber49ReverseRow_3_ok :
    mmRowReverseValid mmFiber49Key mmFiber49Expected (mmFiber49RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber49Chunk1_ok
  change (mmRowReverseValid mmFiber49Key mmFiber49Expected (mmFiber49RowAt 2) &&
    mmRowReverseValid mmFiber49Key mmFiber49Expected (mmFiber49RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber49ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber49StateAt 1) (mmFiber49StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber49StateAt 1) (mmFiber49StateAt 3)
    (mmFiber49RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber49Key mmFiber49Expected
        (mmFiber49RowAt 3) (by decide) mmFiber49ReverseRow_3_ok
      simpa [mmFiber49StateAt, mmFiber49RowAt, mmFiber49Rows, listGetD, directRow] using h)

theorem mmFiber49ReverseRow_4_ok :
    mmRowReverseValid mmFiber49Key mmFiber49Expected (mmFiber49RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber49Chunk2_ok
  change (mmRowReverseValid mmFiber49Key mmFiber49Expected (mmFiber49RowAt 4) &&
    mmRowReverseValid mmFiber49Key mmFiber49Expected (mmFiber49RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber49ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber49StateAt 0) (mmFiber49StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber49StateAt 0) (mmFiber49StateAt 4)
    (mmFiber49RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber49Key mmFiber49Expected
        (mmFiber49RowAt 4) (by decide) mmFiber49ReverseRow_4_ok
      simpa [mmFiber49StateAt, mmFiber49RowAt, mmFiber49Rows, listGetD, directRow] using h)

theorem mmFiber49ReverseRow_5_ok :
    mmRowReverseValid mmFiber49Key mmFiber49Expected (mmFiber49RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber49Chunk2_ok
  change (mmRowReverseValid mmFiber49Key mmFiber49Expected (mmFiber49RowAt 4) &&
    mmRowReverseValid mmFiber49Key mmFiber49Expected (mmFiber49RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber49ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber49StateAt 1) (mmFiber49StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber49StateAt 1) (mmFiber49StateAt 5)
    (mmFiber49RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber49Key mmFiber49Expected
        (mmFiber49RowAt 5) (by decide) mmFiber49ReverseRow_5_ok
      simpa [mmFiber49StateAt, mmFiber49RowAt, mmFiber49Rows, listGetD, directRow] using h)

theorem mmFiber49ReverseRow_6_ok :
    mmRowReverseValid mmFiber49Key mmFiber49Expected (mmFiber49RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber49Chunk3_ok
  change (mmRowReverseValid mmFiber49Key mmFiber49Expected (mmFiber49RowAt 6) &&
    mmRowReverseValid mmFiber49Key mmFiber49Expected (mmFiber49RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber49ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber49StateAt 2) (mmFiber49StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber49StateAt 2) (mmFiber49StateAt 6)
    (mmFiber49RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber49Key mmFiber49Expected
        (mmFiber49RowAt 6) (by decide) mmFiber49ReverseRow_6_ok
      simpa [mmFiber49StateAt, mmFiber49RowAt, mmFiber49Rows, listGetD, directRow] using h)

theorem mmFiber49ReverseRow_7_ok :
    mmRowReverseValid mmFiber49Key mmFiber49Expected (mmFiber49RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber49Chunk3_ok
  change (mmRowReverseValid mmFiber49Key mmFiber49Expected (mmFiber49RowAt 6) &&
    mmRowReverseValid mmFiber49Key mmFiber49Expected (mmFiber49RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber49ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber49StateAt 3) (mmFiber49StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber49StateAt 3) (mmFiber49StateAt 7)
    (mmFiber49RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber49Key mmFiber49Expected
        (mmFiber49RowAt 7) (by decide) mmFiber49ReverseRow_7_ok
      simpa [mmFiber49StateAt, mmFiber49RowAt, mmFiber49Rows, listGetD, directRow] using h)

theorem mmFiber49State0_in_close :
    mmFiber49StateAt 0 ∈ closeChainFiber mmWord mmFiber49DirectStates mmFiber49DirectStates.length [mmFiber49StateAt 0] := by
  change mmFiber49StateAt 0 ∈ closeChainFiber mmWord mmFiber49DirectStates 8 [mmFiber49StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber49DirectStates 0 8 [mmFiber49StateAt 0] (mmFiber49StateAt 0) (by simp [closeChainFiber])

theorem mmFiber49State1_in_close :
    mmFiber49StateAt 1 ∈ closeChainFiber mmWord mmFiber49DirectStates mmFiber49DirectStates.length [mmFiber49StateAt 0] := by
  have h0 : mmFiber49StateAt 0 ∈ closeChainFiber mmWord mmFiber49DirectStates 0 [mmFiber49StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber49StateAt 1 ∈ closeChainFiber mmWord mmFiber49DirectStates 1 [mmFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber49DirectStates 0 [mmFiber49StateAt 0]
      (mmFiber49StateAt 0) (mmFiber49StateAt 1) (by decide) h0 (by decide)
      mmFiber49ReverseSingleStep1
  change mmFiber49StateAt 1 ∈ closeChainFiber mmWord mmFiber49DirectStates (1 + 7) [mmFiber49StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber49DirectStates 1 7 [mmFiber49StateAt 0] (mmFiber49StateAt 1) h1

theorem mmFiber49State2_in_close :
    mmFiber49StateAt 2 ∈ closeChainFiber mmWord mmFiber49DirectStates mmFiber49DirectStates.length [mmFiber49StateAt 0] := by
  have h0 : mmFiber49StateAt 0 ∈ closeChainFiber mmWord mmFiber49DirectStates 0 [mmFiber49StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber49StateAt 2 ∈ closeChainFiber mmWord mmFiber49DirectStates 1 [mmFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber49DirectStates 0 [mmFiber49StateAt 0]
      (mmFiber49StateAt 0) (mmFiber49StateAt 2) (by decide) h0 (by decide)
      mmFiber49ReverseSingleStep2
  change mmFiber49StateAt 2 ∈ closeChainFiber mmWord mmFiber49DirectStates (1 + 7) [mmFiber49StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber49DirectStates 1 7 [mmFiber49StateAt 0] (mmFiber49StateAt 2) h1

theorem mmFiber49State3_in_close :
    mmFiber49StateAt 3 ∈ closeChainFiber mmWord mmFiber49DirectStates mmFiber49DirectStates.length [mmFiber49StateAt 0] := by
  have h0 : mmFiber49StateAt 0 ∈ closeChainFiber mmWord mmFiber49DirectStates 0 [mmFiber49StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber49StateAt 1 ∈ closeChainFiber mmWord mmFiber49DirectStates 1 [mmFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber49DirectStates 0 [mmFiber49StateAt 0]
      (mmFiber49StateAt 0) (mmFiber49StateAt 1) (by decide) h0 (by decide)
      mmFiber49ReverseSingleStep1
  have h2 : mmFiber49StateAt 3 ∈ closeChainFiber mmWord mmFiber49DirectStates 2 [mmFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber49DirectStates 1 [mmFiber49StateAt 0]
      (mmFiber49StateAt 1) (mmFiber49StateAt 3) (by decide) h1 (by decide)
      mmFiber49ReverseSingleStep3
  change mmFiber49StateAt 3 ∈ closeChainFiber mmWord mmFiber49DirectStates (2 + 6) [mmFiber49StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber49DirectStates 2 6 [mmFiber49StateAt 0] (mmFiber49StateAt 3) h2

theorem mmFiber49State4_in_close :
    mmFiber49StateAt 4 ∈ closeChainFiber mmWord mmFiber49DirectStates mmFiber49DirectStates.length [mmFiber49StateAt 0] := by
  have h0 : mmFiber49StateAt 0 ∈ closeChainFiber mmWord mmFiber49DirectStates 0 [mmFiber49StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber49StateAt 4 ∈ closeChainFiber mmWord mmFiber49DirectStates 1 [mmFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber49DirectStates 0 [mmFiber49StateAt 0]
      (mmFiber49StateAt 0) (mmFiber49StateAt 4) (by decide) h0 (by decide)
      mmFiber49ReverseSingleStep4
  change mmFiber49StateAt 4 ∈ closeChainFiber mmWord mmFiber49DirectStates (1 + 7) [mmFiber49StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber49DirectStates 1 7 [mmFiber49StateAt 0] (mmFiber49StateAt 4) h1

theorem mmFiber49State5_in_close :
    mmFiber49StateAt 5 ∈ closeChainFiber mmWord mmFiber49DirectStates mmFiber49DirectStates.length [mmFiber49StateAt 0] := by
  have h0 : mmFiber49StateAt 0 ∈ closeChainFiber mmWord mmFiber49DirectStates 0 [mmFiber49StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber49StateAt 1 ∈ closeChainFiber mmWord mmFiber49DirectStates 1 [mmFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber49DirectStates 0 [mmFiber49StateAt 0]
      (mmFiber49StateAt 0) (mmFiber49StateAt 1) (by decide) h0 (by decide)
      mmFiber49ReverseSingleStep1
  have h2 : mmFiber49StateAt 5 ∈ closeChainFiber mmWord mmFiber49DirectStates 2 [mmFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber49DirectStates 1 [mmFiber49StateAt 0]
      (mmFiber49StateAt 1) (mmFiber49StateAt 5) (by decide) h1 (by decide)
      mmFiber49ReverseSingleStep5
  change mmFiber49StateAt 5 ∈ closeChainFiber mmWord mmFiber49DirectStates (2 + 6) [mmFiber49StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber49DirectStates 2 6 [mmFiber49StateAt 0] (mmFiber49StateAt 5) h2

theorem mmFiber49State6_in_close :
    mmFiber49StateAt 6 ∈ closeChainFiber mmWord mmFiber49DirectStates mmFiber49DirectStates.length [mmFiber49StateAt 0] := by
  have h0 : mmFiber49StateAt 0 ∈ closeChainFiber mmWord mmFiber49DirectStates 0 [mmFiber49StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber49StateAt 2 ∈ closeChainFiber mmWord mmFiber49DirectStates 1 [mmFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber49DirectStates 0 [mmFiber49StateAt 0]
      (mmFiber49StateAt 0) (mmFiber49StateAt 2) (by decide) h0 (by decide)
      mmFiber49ReverseSingleStep2
  have h2 : mmFiber49StateAt 6 ∈ closeChainFiber mmWord mmFiber49DirectStates 2 [mmFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber49DirectStates 1 [mmFiber49StateAt 0]
      (mmFiber49StateAt 2) (mmFiber49StateAt 6) (by decide) h1 (by decide)
      mmFiber49ReverseSingleStep6
  change mmFiber49StateAt 6 ∈ closeChainFiber mmWord mmFiber49DirectStates (2 + 6) [mmFiber49StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber49DirectStates 2 6 [mmFiber49StateAt 0] (mmFiber49StateAt 6) h2

theorem mmFiber49State7_in_close :
    mmFiber49StateAt 7 ∈ closeChainFiber mmWord mmFiber49DirectStates mmFiber49DirectStates.length [mmFiber49StateAt 0] := by
  have h0 : mmFiber49StateAt 0 ∈ closeChainFiber mmWord mmFiber49DirectStates 0 [mmFiber49StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber49StateAt 1 ∈ closeChainFiber mmWord mmFiber49DirectStates 1 [mmFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber49DirectStates 0 [mmFiber49StateAt 0]
      (mmFiber49StateAt 0) (mmFiber49StateAt 1) (by decide) h0 (by decide)
      mmFiber49ReverseSingleStep1
  have h2 : mmFiber49StateAt 3 ∈ closeChainFiber mmWord mmFiber49DirectStates 2 [mmFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber49DirectStates 1 [mmFiber49StateAt 0]
      (mmFiber49StateAt 1) (mmFiber49StateAt 3) (by decide) h1 (by decide)
      mmFiber49ReverseSingleStep3
  have h3 : mmFiber49StateAt 7 ∈ closeChainFiber mmWord mmFiber49DirectStates 3 [mmFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber49DirectStates 2 [mmFiber49StateAt 0]
      (mmFiber49StateAt 3) (mmFiber49StateAt 7) (by decide) h2 (by decide)
      mmFiber49ReverseSingleStep7
  change mmFiber49StateAt 7 ∈ closeChainFiber mmWord mmFiber49DirectStates (3 + 5) [mmFiber49StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber49DirectStates 3 5 [mmFiber49StateAt 0] (mmFiber49StateAt 7) h3

theorem mmFiber49DirectConnected :
    chainFiberConnected mmWord mmFiber49DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber49DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber49State0_in_close
  · subst state
    exact mmFiber49State1_in_close
  · subst state
    exact mmFiber49State2_in_close
  · subst state
    exact mmFiber49State3_in_close
  · subst state
    exact mmFiber49State4_in_close
  · subst state
    exact mmFiber49State5_in_close
  · subst state
    exact mmFiber49State6_in_close
  · subst state
    exact mmFiber49State7_in_close
  · cases h
end GoertzelLemma818LengthTwoMMBridge

end Mettapedia.GraphTheory.FourColor
