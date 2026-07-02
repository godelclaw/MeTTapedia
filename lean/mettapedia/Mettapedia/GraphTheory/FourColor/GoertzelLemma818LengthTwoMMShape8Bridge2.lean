import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for size-8 `mirror,mirror` length-two fibers, group 2

This module proves direct connectedness for generated `mirror,mirror` size-8 fibers from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMMBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorMirrorCertificate
open GoertzelLemma818MirrorMirrorReverseAudit

def mmFiber31StateAt (i : Nat) : List TauState :=
  directStates (mmFiber31RowAt i).sourceLeft (mmFiber31RowAt i).sourceRight

def mmFiber31DirectStates : List (List TauState) :=
  [mmFiber31StateAt 0, mmFiber31StateAt 1, mmFiber31StateAt 2, mmFiber31StateAt 3, mmFiber31StateAt 4, mmFiber31StateAt 5, mmFiber31StateAt 6, mmFiber31StateAt 7]

theorem mmFiber31ReverseRow_1_ok :
    mmRowReverseValid mmFiber31Key mmFiber31Expected (mmFiber31RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber31Chunk0_ok
  change (mmRowReverseValid mmFiber31Key mmFiber31Expected (mmFiber31RowAt 0) &&
    mmRowReverseValid mmFiber31Key mmFiber31Expected (mmFiber31RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber31ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber31StateAt 0) (mmFiber31StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber31StateAt 0) (mmFiber31StateAt 1)
    (mmFiber31RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber31Key mmFiber31Expected
        (mmFiber31RowAt 1) (by decide) mmFiber31ReverseRow_1_ok
      simpa [mmFiber31StateAt, mmFiber31RowAt, mmFiber31Rows, listGetD, directRow] using h)

theorem mmFiber31ReverseRow_2_ok :
    mmRowReverseValid mmFiber31Key mmFiber31Expected (mmFiber31RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber31Chunk1_ok
  change (mmRowReverseValid mmFiber31Key mmFiber31Expected (mmFiber31RowAt 2) &&
    mmRowReverseValid mmFiber31Key mmFiber31Expected (mmFiber31RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber31ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber31StateAt 0) (mmFiber31StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber31StateAt 0) (mmFiber31StateAt 2)
    (mmFiber31RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber31Key mmFiber31Expected
        (mmFiber31RowAt 2) (by decide) mmFiber31ReverseRow_2_ok
      simpa [mmFiber31StateAt, mmFiber31RowAt, mmFiber31Rows, listGetD, directRow] using h)

theorem mmFiber31ReverseRow_3_ok :
    mmRowReverseValid mmFiber31Key mmFiber31Expected (mmFiber31RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber31Chunk1_ok
  change (mmRowReverseValid mmFiber31Key mmFiber31Expected (mmFiber31RowAt 2) &&
    mmRowReverseValid mmFiber31Key mmFiber31Expected (mmFiber31RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber31ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber31StateAt 1) (mmFiber31StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber31StateAt 1) (mmFiber31StateAt 3)
    (mmFiber31RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber31Key mmFiber31Expected
        (mmFiber31RowAt 3) (by decide) mmFiber31ReverseRow_3_ok
      simpa [mmFiber31StateAt, mmFiber31RowAt, mmFiber31Rows, listGetD, directRow] using h)

theorem mmFiber31ReverseRow_4_ok :
    mmRowReverseValid mmFiber31Key mmFiber31Expected (mmFiber31RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber31Chunk2_ok
  change (mmRowReverseValid mmFiber31Key mmFiber31Expected (mmFiber31RowAt 4) &&
    mmRowReverseValid mmFiber31Key mmFiber31Expected (mmFiber31RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber31ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber31StateAt 0) (mmFiber31StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber31StateAt 0) (mmFiber31StateAt 4)
    (mmFiber31RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber31Key mmFiber31Expected
        (mmFiber31RowAt 4) (by decide) mmFiber31ReverseRow_4_ok
      simpa [mmFiber31StateAt, mmFiber31RowAt, mmFiber31Rows, listGetD, directRow] using h)

theorem mmFiber31ReverseRow_5_ok :
    mmRowReverseValid mmFiber31Key mmFiber31Expected (mmFiber31RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber31Chunk2_ok
  change (mmRowReverseValid mmFiber31Key mmFiber31Expected (mmFiber31RowAt 4) &&
    mmRowReverseValid mmFiber31Key mmFiber31Expected (mmFiber31RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber31ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber31StateAt 1) (mmFiber31StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber31StateAt 1) (mmFiber31StateAt 5)
    (mmFiber31RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber31Key mmFiber31Expected
        (mmFiber31RowAt 5) (by decide) mmFiber31ReverseRow_5_ok
      simpa [mmFiber31StateAt, mmFiber31RowAt, mmFiber31Rows, listGetD, directRow] using h)

theorem mmFiber31ReverseRow_6_ok :
    mmRowReverseValid mmFiber31Key mmFiber31Expected (mmFiber31RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber31Chunk3_ok
  change (mmRowReverseValid mmFiber31Key mmFiber31Expected (mmFiber31RowAt 6) &&
    mmRowReverseValid mmFiber31Key mmFiber31Expected (mmFiber31RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber31ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber31StateAt 2) (mmFiber31StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber31StateAt 2) (mmFiber31StateAt 6)
    (mmFiber31RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber31Key mmFiber31Expected
        (mmFiber31RowAt 6) (by decide) mmFiber31ReverseRow_6_ok
      simpa [mmFiber31StateAt, mmFiber31RowAt, mmFiber31Rows, listGetD, directRow] using h)

theorem mmFiber31ReverseRow_7_ok :
    mmRowReverseValid mmFiber31Key mmFiber31Expected (mmFiber31RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber31Chunk3_ok
  change (mmRowReverseValid mmFiber31Key mmFiber31Expected (mmFiber31RowAt 6) &&
    mmRowReverseValid mmFiber31Key mmFiber31Expected (mmFiber31RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber31ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber31StateAt 3) (mmFiber31StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber31StateAt 3) (mmFiber31StateAt 7)
    (mmFiber31RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber31Key mmFiber31Expected
        (mmFiber31RowAt 7) (by decide) mmFiber31ReverseRow_7_ok
      simpa [mmFiber31StateAt, mmFiber31RowAt, mmFiber31Rows, listGetD, directRow] using h)

theorem mmFiber31State0_in_close :
    mmFiber31StateAt 0 ∈ closeChainFiber mmWord mmFiber31DirectStates mmFiber31DirectStates.length [mmFiber31StateAt 0] := by
  change mmFiber31StateAt 0 ∈ closeChainFiber mmWord mmFiber31DirectStates 8 [mmFiber31StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber31DirectStates 0 8 [mmFiber31StateAt 0] (mmFiber31StateAt 0) (by simp [closeChainFiber])

theorem mmFiber31State1_in_close :
    mmFiber31StateAt 1 ∈ closeChainFiber mmWord mmFiber31DirectStates mmFiber31DirectStates.length [mmFiber31StateAt 0] := by
  have h0 : mmFiber31StateAt 0 ∈ closeChainFiber mmWord mmFiber31DirectStates 0 [mmFiber31StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber31StateAt 1 ∈ closeChainFiber mmWord mmFiber31DirectStates 1 [mmFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber31DirectStates 0 [mmFiber31StateAt 0]
      (mmFiber31StateAt 0) (mmFiber31StateAt 1) (by decide) h0 (by decide)
      mmFiber31ReverseSingleStep1
  change mmFiber31StateAt 1 ∈ closeChainFiber mmWord mmFiber31DirectStates (1 + 7) [mmFiber31StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber31DirectStates 1 7 [mmFiber31StateAt 0] (mmFiber31StateAt 1) h1

theorem mmFiber31State2_in_close :
    mmFiber31StateAt 2 ∈ closeChainFiber mmWord mmFiber31DirectStates mmFiber31DirectStates.length [mmFiber31StateAt 0] := by
  have h0 : mmFiber31StateAt 0 ∈ closeChainFiber mmWord mmFiber31DirectStates 0 [mmFiber31StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber31StateAt 2 ∈ closeChainFiber mmWord mmFiber31DirectStates 1 [mmFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber31DirectStates 0 [mmFiber31StateAt 0]
      (mmFiber31StateAt 0) (mmFiber31StateAt 2) (by decide) h0 (by decide)
      mmFiber31ReverseSingleStep2
  change mmFiber31StateAt 2 ∈ closeChainFiber mmWord mmFiber31DirectStates (1 + 7) [mmFiber31StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber31DirectStates 1 7 [mmFiber31StateAt 0] (mmFiber31StateAt 2) h1

theorem mmFiber31State3_in_close :
    mmFiber31StateAt 3 ∈ closeChainFiber mmWord mmFiber31DirectStates mmFiber31DirectStates.length [mmFiber31StateAt 0] := by
  have h0 : mmFiber31StateAt 0 ∈ closeChainFiber mmWord mmFiber31DirectStates 0 [mmFiber31StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber31StateAt 1 ∈ closeChainFiber mmWord mmFiber31DirectStates 1 [mmFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber31DirectStates 0 [mmFiber31StateAt 0]
      (mmFiber31StateAt 0) (mmFiber31StateAt 1) (by decide) h0 (by decide)
      mmFiber31ReverseSingleStep1
  have h2 : mmFiber31StateAt 3 ∈ closeChainFiber mmWord mmFiber31DirectStates 2 [mmFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber31DirectStates 1 [mmFiber31StateAt 0]
      (mmFiber31StateAt 1) (mmFiber31StateAt 3) (by decide) h1 (by decide)
      mmFiber31ReverseSingleStep3
  change mmFiber31StateAt 3 ∈ closeChainFiber mmWord mmFiber31DirectStates (2 + 6) [mmFiber31StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber31DirectStates 2 6 [mmFiber31StateAt 0] (mmFiber31StateAt 3) h2

theorem mmFiber31State4_in_close :
    mmFiber31StateAt 4 ∈ closeChainFiber mmWord mmFiber31DirectStates mmFiber31DirectStates.length [mmFiber31StateAt 0] := by
  have h0 : mmFiber31StateAt 0 ∈ closeChainFiber mmWord mmFiber31DirectStates 0 [mmFiber31StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber31StateAt 4 ∈ closeChainFiber mmWord mmFiber31DirectStates 1 [mmFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber31DirectStates 0 [mmFiber31StateAt 0]
      (mmFiber31StateAt 0) (mmFiber31StateAt 4) (by decide) h0 (by decide)
      mmFiber31ReverseSingleStep4
  change mmFiber31StateAt 4 ∈ closeChainFiber mmWord mmFiber31DirectStates (1 + 7) [mmFiber31StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber31DirectStates 1 7 [mmFiber31StateAt 0] (mmFiber31StateAt 4) h1

theorem mmFiber31State5_in_close :
    mmFiber31StateAt 5 ∈ closeChainFiber mmWord mmFiber31DirectStates mmFiber31DirectStates.length [mmFiber31StateAt 0] := by
  have h0 : mmFiber31StateAt 0 ∈ closeChainFiber mmWord mmFiber31DirectStates 0 [mmFiber31StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber31StateAt 1 ∈ closeChainFiber mmWord mmFiber31DirectStates 1 [mmFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber31DirectStates 0 [mmFiber31StateAt 0]
      (mmFiber31StateAt 0) (mmFiber31StateAt 1) (by decide) h0 (by decide)
      mmFiber31ReverseSingleStep1
  have h2 : mmFiber31StateAt 5 ∈ closeChainFiber mmWord mmFiber31DirectStates 2 [mmFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber31DirectStates 1 [mmFiber31StateAt 0]
      (mmFiber31StateAt 1) (mmFiber31StateAt 5) (by decide) h1 (by decide)
      mmFiber31ReverseSingleStep5
  change mmFiber31StateAt 5 ∈ closeChainFiber mmWord mmFiber31DirectStates (2 + 6) [mmFiber31StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber31DirectStates 2 6 [mmFiber31StateAt 0] (mmFiber31StateAt 5) h2

theorem mmFiber31State6_in_close :
    mmFiber31StateAt 6 ∈ closeChainFiber mmWord mmFiber31DirectStates mmFiber31DirectStates.length [mmFiber31StateAt 0] := by
  have h0 : mmFiber31StateAt 0 ∈ closeChainFiber mmWord mmFiber31DirectStates 0 [mmFiber31StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber31StateAt 2 ∈ closeChainFiber mmWord mmFiber31DirectStates 1 [mmFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber31DirectStates 0 [mmFiber31StateAt 0]
      (mmFiber31StateAt 0) (mmFiber31StateAt 2) (by decide) h0 (by decide)
      mmFiber31ReverseSingleStep2
  have h2 : mmFiber31StateAt 6 ∈ closeChainFiber mmWord mmFiber31DirectStates 2 [mmFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber31DirectStates 1 [mmFiber31StateAt 0]
      (mmFiber31StateAt 2) (mmFiber31StateAt 6) (by decide) h1 (by decide)
      mmFiber31ReverseSingleStep6
  change mmFiber31StateAt 6 ∈ closeChainFiber mmWord mmFiber31DirectStates (2 + 6) [mmFiber31StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber31DirectStates 2 6 [mmFiber31StateAt 0] (mmFiber31StateAt 6) h2

theorem mmFiber31State7_in_close :
    mmFiber31StateAt 7 ∈ closeChainFiber mmWord mmFiber31DirectStates mmFiber31DirectStates.length [mmFiber31StateAt 0] := by
  have h0 : mmFiber31StateAt 0 ∈ closeChainFiber mmWord mmFiber31DirectStates 0 [mmFiber31StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber31StateAt 1 ∈ closeChainFiber mmWord mmFiber31DirectStates 1 [mmFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber31DirectStates 0 [mmFiber31StateAt 0]
      (mmFiber31StateAt 0) (mmFiber31StateAt 1) (by decide) h0 (by decide)
      mmFiber31ReverseSingleStep1
  have h2 : mmFiber31StateAt 3 ∈ closeChainFiber mmWord mmFiber31DirectStates 2 [mmFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber31DirectStates 1 [mmFiber31StateAt 0]
      (mmFiber31StateAt 1) (mmFiber31StateAt 3) (by decide) h1 (by decide)
      mmFiber31ReverseSingleStep3
  have h3 : mmFiber31StateAt 7 ∈ closeChainFiber mmWord mmFiber31DirectStates 3 [mmFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber31DirectStates 2 [mmFiber31StateAt 0]
      (mmFiber31StateAt 3) (mmFiber31StateAt 7) (by decide) h2 (by decide)
      mmFiber31ReverseSingleStep7
  change mmFiber31StateAt 7 ∈ closeChainFiber mmWord mmFiber31DirectStates (3 + 5) [mmFiber31StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber31DirectStates 3 5 [mmFiber31StateAt 0] (mmFiber31StateAt 7) h3

theorem mmFiber31DirectConnected :
    chainFiberConnected mmWord mmFiber31DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber31DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber31State0_in_close
  · subst state
    exact mmFiber31State1_in_close
  · subst state
    exact mmFiber31State2_in_close
  · subst state
    exact mmFiber31State3_in_close
  · subst state
    exact mmFiber31State4_in_close
  · subst state
    exact mmFiber31State5_in_close
  · subst state
    exact mmFiber31State6_in_close
  · subst state
    exact mmFiber31State7_in_close
  · cases h
def mmFiber33StateAt (i : Nat) : List TauState :=
  directStates (mmFiber33RowAt i).sourceLeft (mmFiber33RowAt i).sourceRight

def mmFiber33DirectStates : List (List TauState) :=
  [mmFiber33StateAt 0, mmFiber33StateAt 1, mmFiber33StateAt 2, mmFiber33StateAt 3, mmFiber33StateAt 4, mmFiber33StateAt 5, mmFiber33StateAt 6, mmFiber33StateAt 7]

theorem mmFiber33ReverseRow_1_ok :
    mmRowReverseValid mmFiber33Key mmFiber33Expected (mmFiber33RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber33Chunk0_ok
  change (mmRowReverseValid mmFiber33Key mmFiber33Expected (mmFiber33RowAt 0) &&
    mmRowReverseValid mmFiber33Key mmFiber33Expected (mmFiber33RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber33ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber33StateAt 0) (mmFiber33StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber33StateAt 0) (mmFiber33StateAt 1)
    (mmFiber33RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber33Key mmFiber33Expected
        (mmFiber33RowAt 1) (by decide) mmFiber33ReverseRow_1_ok
      simpa [mmFiber33StateAt, mmFiber33RowAt, mmFiber33Rows, listGetD, directRow] using h)

theorem mmFiber33ReverseRow_2_ok :
    mmRowReverseValid mmFiber33Key mmFiber33Expected (mmFiber33RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber33Chunk1_ok
  change (mmRowReverseValid mmFiber33Key mmFiber33Expected (mmFiber33RowAt 2) &&
    mmRowReverseValid mmFiber33Key mmFiber33Expected (mmFiber33RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber33ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber33StateAt 0) (mmFiber33StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber33StateAt 0) (mmFiber33StateAt 2)
    (mmFiber33RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber33Key mmFiber33Expected
        (mmFiber33RowAt 2) (by decide) mmFiber33ReverseRow_2_ok
      simpa [mmFiber33StateAt, mmFiber33RowAt, mmFiber33Rows, listGetD, directRow] using h)

theorem mmFiber33ReverseRow_3_ok :
    mmRowReverseValid mmFiber33Key mmFiber33Expected (mmFiber33RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber33Chunk1_ok
  change (mmRowReverseValid mmFiber33Key mmFiber33Expected (mmFiber33RowAt 2) &&
    mmRowReverseValid mmFiber33Key mmFiber33Expected (mmFiber33RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber33ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber33StateAt 1) (mmFiber33StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber33StateAt 1) (mmFiber33StateAt 3)
    (mmFiber33RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber33Key mmFiber33Expected
        (mmFiber33RowAt 3) (by decide) mmFiber33ReverseRow_3_ok
      simpa [mmFiber33StateAt, mmFiber33RowAt, mmFiber33Rows, listGetD, directRow] using h)

theorem mmFiber33ReverseRow_4_ok :
    mmRowReverseValid mmFiber33Key mmFiber33Expected (mmFiber33RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber33Chunk2_ok
  change (mmRowReverseValid mmFiber33Key mmFiber33Expected (mmFiber33RowAt 4) &&
    mmRowReverseValid mmFiber33Key mmFiber33Expected (mmFiber33RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber33ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber33StateAt 0) (mmFiber33StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber33StateAt 0) (mmFiber33StateAt 4)
    (mmFiber33RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber33Key mmFiber33Expected
        (mmFiber33RowAt 4) (by decide) mmFiber33ReverseRow_4_ok
      simpa [mmFiber33StateAt, mmFiber33RowAt, mmFiber33Rows, listGetD, directRow] using h)

theorem mmFiber33ReverseRow_5_ok :
    mmRowReverseValid mmFiber33Key mmFiber33Expected (mmFiber33RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber33Chunk2_ok
  change (mmRowReverseValid mmFiber33Key mmFiber33Expected (mmFiber33RowAt 4) &&
    mmRowReverseValid mmFiber33Key mmFiber33Expected (mmFiber33RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber33ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber33StateAt 1) (mmFiber33StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber33StateAt 1) (mmFiber33StateAt 5)
    (mmFiber33RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber33Key mmFiber33Expected
        (mmFiber33RowAt 5) (by decide) mmFiber33ReverseRow_5_ok
      simpa [mmFiber33StateAt, mmFiber33RowAt, mmFiber33Rows, listGetD, directRow] using h)

theorem mmFiber33ReverseRow_6_ok :
    mmRowReverseValid mmFiber33Key mmFiber33Expected (mmFiber33RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber33Chunk3_ok
  change (mmRowReverseValid mmFiber33Key mmFiber33Expected (mmFiber33RowAt 6) &&
    mmRowReverseValid mmFiber33Key mmFiber33Expected (mmFiber33RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber33ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber33StateAt 2) (mmFiber33StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber33StateAt 2) (mmFiber33StateAt 6)
    (mmFiber33RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber33Key mmFiber33Expected
        (mmFiber33RowAt 6) (by decide) mmFiber33ReverseRow_6_ok
      simpa [mmFiber33StateAt, mmFiber33RowAt, mmFiber33Rows, listGetD, directRow] using h)

theorem mmFiber33ReverseRow_7_ok :
    mmRowReverseValid mmFiber33Key mmFiber33Expected (mmFiber33RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber33Chunk3_ok
  change (mmRowReverseValid mmFiber33Key mmFiber33Expected (mmFiber33RowAt 6) &&
    mmRowReverseValid mmFiber33Key mmFiber33Expected (mmFiber33RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber33ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber33StateAt 3) (mmFiber33StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber33StateAt 3) (mmFiber33StateAt 7)
    (mmFiber33RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber33Key mmFiber33Expected
        (mmFiber33RowAt 7) (by decide) mmFiber33ReverseRow_7_ok
      simpa [mmFiber33StateAt, mmFiber33RowAt, mmFiber33Rows, listGetD, directRow] using h)

theorem mmFiber33State0_in_close :
    mmFiber33StateAt 0 ∈ closeChainFiber mmWord mmFiber33DirectStates mmFiber33DirectStates.length [mmFiber33StateAt 0] := by
  change mmFiber33StateAt 0 ∈ closeChainFiber mmWord mmFiber33DirectStates 8 [mmFiber33StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber33DirectStates 0 8 [mmFiber33StateAt 0] (mmFiber33StateAt 0) (by simp [closeChainFiber])

theorem mmFiber33State1_in_close :
    mmFiber33StateAt 1 ∈ closeChainFiber mmWord mmFiber33DirectStates mmFiber33DirectStates.length [mmFiber33StateAt 0] := by
  have h0 : mmFiber33StateAt 0 ∈ closeChainFiber mmWord mmFiber33DirectStates 0 [mmFiber33StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber33StateAt 1 ∈ closeChainFiber mmWord mmFiber33DirectStates 1 [mmFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber33DirectStates 0 [mmFiber33StateAt 0]
      (mmFiber33StateAt 0) (mmFiber33StateAt 1) (by decide) h0 (by decide)
      mmFiber33ReverseSingleStep1
  change mmFiber33StateAt 1 ∈ closeChainFiber mmWord mmFiber33DirectStates (1 + 7) [mmFiber33StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber33DirectStates 1 7 [mmFiber33StateAt 0] (mmFiber33StateAt 1) h1

theorem mmFiber33State2_in_close :
    mmFiber33StateAt 2 ∈ closeChainFiber mmWord mmFiber33DirectStates mmFiber33DirectStates.length [mmFiber33StateAt 0] := by
  have h0 : mmFiber33StateAt 0 ∈ closeChainFiber mmWord mmFiber33DirectStates 0 [mmFiber33StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber33StateAt 2 ∈ closeChainFiber mmWord mmFiber33DirectStates 1 [mmFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber33DirectStates 0 [mmFiber33StateAt 0]
      (mmFiber33StateAt 0) (mmFiber33StateAt 2) (by decide) h0 (by decide)
      mmFiber33ReverseSingleStep2
  change mmFiber33StateAt 2 ∈ closeChainFiber mmWord mmFiber33DirectStates (1 + 7) [mmFiber33StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber33DirectStates 1 7 [mmFiber33StateAt 0] (mmFiber33StateAt 2) h1

theorem mmFiber33State3_in_close :
    mmFiber33StateAt 3 ∈ closeChainFiber mmWord mmFiber33DirectStates mmFiber33DirectStates.length [mmFiber33StateAt 0] := by
  have h0 : mmFiber33StateAt 0 ∈ closeChainFiber mmWord mmFiber33DirectStates 0 [mmFiber33StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber33StateAt 1 ∈ closeChainFiber mmWord mmFiber33DirectStates 1 [mmFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber33DirectStates 0 [mmFiber33StateAt 0]
      (mmFiber33StateAt 0) (mmFiber33StateAt 1) (by decide) h0 (by decide)
      mmFiber33ReverseSingleStep1
  have h2 : mmFiber33StateAt 3 ∈ closeChainFiber mmWord mmFiber33DirectStates 2 [mmFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber33DirectStates 1 [mmFiber33StateAt 0]
      (mmFiber33StateAt 1) (mmFiber33StateAt 3) (by decide) h1 (by decide)
      mmFiber33ReverseSingleStep3
  change mmFiber33StateAt 3 ∈ closeChainFiber mmWord mmFiber33DirectStates (2 + 6) [mmFiber33StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber33DirectStates 2 6 [mmFiber33StateAt 0] (mmFiber33StateAt 3) h2

theorem mmFiber33State4_in_close :
    mmFiber33StateAt 4 ∈ closeChainFiber mmWord mmFiber33DirectStates mmFiber33DirectStates.length [mmFiber33StateAt 0] := by
  have h0 : mmFiber33StateAt 0 ∈ closeChainFiber mmWord mmFiber33DirectStates 0 [mmFiber33StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber33StateAt 4 ∈ closeChainFiber mmWord mmFiber33DirectStates 1 [mmFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber33DirectStates 0 [mmFiber33StateAt 0]
      (mmFiber33StateAt 0) (mmFiber33StateAt 4) (by decide) h0 (by decide)
      mmFiber33ReverseSingleStep4
  change mmFiber33StateAt 4 ∈ closeChainFiber mmWord mmFiber33DirectStates (1 + 7) [mmFiber33StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber33DirectStates 1 7 [mmFiber33StateAt 0] (mmFiber33StateAt 4) h1

theorem mmFiber33State5_in_close :
    mmFiber33StateAt 5 ∈ closeChainFiber mmWord mmFiber33DirectStates mmFiber33DirectStates.length [mmFiber33StateAt 0] := by
  have h0 : mmFiber33StateAt 0 ∈ closeChainFiber mmWord mmFiber33DirectStates 0 [mmFiber33StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber33StateAt 1 ∈ closeChainFiber mmWord mmFiber33DirectStates 1 [mmFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber33DirectStates 0 [mmFiber33StateAt 0]
      (mmFiber33StateAt 0) (mmFiber33StateAt 1) (by decide) h0 (by decide)
      mmFiber33ReverseSingleStep1
  have h2 : mmFiber33StateAt 5 ∈ closeChainFiber mmWord mmFiber33DirectStates 2 [mmFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber33DirectStates 1 [mmFiber33StateAt 0]
      (mmFiber33StateAt 1) (mmFiber33StateAt 5) (by decide) h1 (by decide)
      mmFiber33ReverseSingleStep5
  change mmFiber33StateAt 5 ∈ closeChainFiber mmWord mmFiber33DirectStates (2 + 6) [mmFiber33StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber33DirectStates 2 6 [mmFiber33StateAt 0] (mmFiber33StateAt 5) h2

theorem mmFiber33State6_in_close :
    mmFiber33StateAt 6 ∈ closeChainFiber mmWord mmFiber33DirectStates mmFiber33DirectStates.length [mmFiber33StateAt 0] := by
  have h0 : mmFiber33StateAt 0 ∈ closeChainFiber mmWord mmFiber33DirectStates 0 [mmFiber33StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber33StateAt 2 ∈ closeChainFiber mmWord mmFiber33DirectStates 1 [mmFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber33DirectStates 0 [mmFiber33StateAt 0]
      (mmFiber33StateAt 0) (mmFiber33StateAt 2) (by decide) h0 (by decide)
      mmFiber33ReverseSingleStep2
  have h2 : mmFiber33StateAt 6 ∈ closeChainFiber mmWord mmFiber33DirectStates 2 [mmFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber33DirectStates 1 [mmFiber33StateAt 0]
      (mmFiber33StateAt 2) (mmFiber33StateAt 6) (by decide) h1 (by decide)
      mmFiber33ReverseSingleStep6
  change mmFiber33StateAt 6 ∈ closeChainFiber mmWord mmFiber33DirectStates (2 + 6) [mmFiber33StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber33DirectStates 2 6 [mmFiber33StateAt 0] (mmFiber33StateAt 6) h2

theorem mmFiber33State7_in_close :
    mmFiber33StateAt 7 ∈ closeChainFiber mmWord mmFiber33DirectStates mmFiber33DirectStates.length [mmFiber33StateAt 0] := by
  have h0 : mmFiber33StateAt 0 ∈ closeChainFiber mmWord mmFiber33DirectStates 0 [mmFiber33StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber33StateAt 1 ∈ closeChainFiber mmWord mmFiber33DirectStates 1 [mmFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber33DirectStates 0 [mmFiber33StateAt 0]
      (mmFiber33StateAt 0) (mmFiber33StateAt 1) (by decide) h0 (by decide)
      mmFiber33ReverseSingleStep1
  have h2 : mmFiber33StateAt 3 ∈ closeChainFiber mmWord mmFiber33DirectStates 2 [mmFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber33DirectStates 1 [mmFiber33StateAt 0]
      (mmFiber33StateAt 1) (mmFiber33StateAt 3) (by decide) h1 (by decide)
      mmFiber33ReverseSingleStep3
  have h3 : mmFiber33StateAt 7 ∈ closeChainFiber mmWord mmFiber33DirectStates 3 [mmFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber33DirectStates 2 [mmFiber33StateAt 0]
      (mmFiber33StateAt 3) (mmFiber33StateAt 7) (by decide) h2 (by decide)
      mmFiber33ReverseSingleStep7
  change mmFiber33StateAt 7 ∈ closeChainFiber mmWord mmFiber33DirectStates (3 + 5) [mmFiber33StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber33DirectStates 3 5 [mmFiber33StateAt 0] (mmFiber33StateAt 7) h3

theorem mmFiber33DirectConnected :
    chainFiberConnected mmWord mmFiber33DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber33DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber33State0_in_close
  · subst state
    exact mmFiber33State1_in_close
  · subst state
    exact mmFiber33State2_in_close
  · subst state
    exact mmFiber33State3_in_close
  · subst state
    exact mmFiber33State4_in_close
  · subst state
    exact mmFiber33State5_in_close
  · subst state
    exact mmFiber33State6_in_close
  · subst state
    exact mmFiber33State7_in_close
  · cases h
def mmFiber35StateAt (i : Nat) : List TauState :=
  directStates (mmFiber35RowAt i).sourceLeft (mmFiber35RowAt i).sourceRight

def mmFiber35DirectStates : List (List TauState) :=
  [mmFiber35StateAt 0, mmFiber35StateAt 1, mmFiber35StateAt 2, mmFiber35StateAt 3, mmFiber35StateAt 4, mmFiber35StateAt 5, mmFiber35StateAt 6, mmFiber35StateAt 7]

theorem mmFiber35ReverseRow_1_ok :
    mmRowReverseValid mmFiber35Key mmFiber35Expected (mmFiber35RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber35Chunk0_ok
  change (mmRowReverseValid mmFiber35Key mmFiber35Expected (mmFiber35RowAt 0) &&
    mmRowReverseValid mmFiber35Key mmFiber35Expected (mmFiber35RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber35ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber35StateAt 0) (mmFiber35StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber35StateAt 0) (mmFiber35StateAt 1)
    (mmFiber35RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber35Key mmFiber35Expected
        (mmFiber35RowAt 1) (by decide) mmFiber35ReverseRow_1_ok
      simpa [mmFiber35StateAt, mmFiber35RowAt, mmFiber35Rows, listGetD, directRow] using h)

theorem mmFiber35ReverseRow_2_ok :
    mmRowReverseValid mmFiber35Key mmFiber35Expected (mmFiber35RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber35Chunk1_ok
  change (mmRowReverseValid mmFiber35Key mmFiber35Expected (mmFiber35RowAt 2) &&
    mmRowReverseValid mmFiber35Key mmFiber35Expected (mmFiber35RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber35ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber35StateAt 0) (mmFiber35StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber35StateAt 0) (mmFiber35StateAt 2)
    (mmFiber35RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber35Key mmFiber35Expected
        (mmFiber35RowAt 2) (by decide) mmFiber35ReverseRow_2_ok
      simpa [mmFiber35StateAt, mmFiber35RowAt, mmFiber35Rows, listGetD, directRow] using h)

theorem mmFiber35ReverseRow_3_ok :
    mmRowReverseValid mmFiber35Key mmFiber35Expected (mmFiber35RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber35Chunk1_ok
  change (mmRowReverseValid mmFiber35Key mmFiber35Expected (mmFiber35RowAt 2) &&
    mmRowReverseValid mmFiber35Key mmFiber35Expected (mmFiber35RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber35ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber35StateAt 1) (mmFiber35StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber35StateAt 1) (mmFiber35StateAt 3)
    (mmFiber35RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber35Key mmFiber35Expected
        (mmFiber35RowAt 3) (by decide) mmFiber35ReverseRow_3_ok
      simpa [mmFiber35StateAt, mmFiber35RowAt, mmFiber35Rows, listGetD, directRow] using h)

theorem mmFiber35ReverseRow_4_ok :
    mmRowReverseValid mmFiber35Key mmFiber35Expected (mmFiber35RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber35Chunk2_ok
  change (mmRowReverseValid mmFiber35Key mmFiber35Expected (mmFiber35RowAt 4) &&
    mmRowReverseValid mmFiber35Key mmFiber35Expected (mmFiber35RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber35ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber35StateAt 0) (mmFiber35StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber35StateAt 0) (mmFiber35StateAt 4)
    (mmFiber35RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber35Key mmFiber35Expected
        (mmFiber35RowAt 4) (by decide) mmFiber35ReverseRow_4_ok
      simpa [mmFiber35StateAt, mmFiber35RowAt, mmFiber35Rows, listGetD, directRow] using h)

theorem mmFiber35ReverseRow_5_ok :
    mmRowReverseValid mmFiber35Key mmFiber35Expected (mmFiber35RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber35Chunk2_ok
  change (mmRowReverseValid mmFiber35Key mmFiber35Expected (mmFiber35RowAt 4) &&
    mmRowReverseValid mmFiber35Key mmFiber35Expected (mmFiber35RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber35ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber35StateAt 1) (mmFiber35StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber35StateAt 1) (mmFiber35StateAt 5)
    (mmFiber35RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber35Key mmFiber35Expected
        (mmFiber35RowAt 5) (by decide) mmFiber35ReverseRow_5_ok
      simpa [mmFiber35StateAt, mmFiber35RowAt, mmFiber35Rows, listGetD, directRow] using h)

theorem mmFiber35ReverseRow_6_ok :
    mmRowReverseValid mmFiber35Key mmFiber35Expected (mmFiber35RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber35Chunk3_ok
  change (mmRowReverseValid mmFiber35Key mmFiber35Expected (mmFiber35RowAt 6) &&
    mmRowReverseValid mmFiber35Key mmFiber35Expected (mmFiber35RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber35ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber35StateAt 2) (mmFiber35StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber35StateAt 2) (mmFiber35StateAt 6)
    (mmFiber35RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber35Key mmFiber35Expected
        (mmFiber35RowAt 6) (by decide) mmFiber35ReverseRow_6_ok
      simpa [mmFiber35StateAt, mmFiber35RowAt, mmFiber35Rows, listGetD, directRow] using h)

theorem mmFiber35ReverseRow_7_ok :
    mmRowReverseValid mmFiber35Key mmFiber35Expected (mmFiber35RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber35Chunk3_ok
  change (mmRowReverseValid mmFiber35Key mmFiber35Expected (mmFiber35RowAt 6) &&
    mmRowReverseValid mmFiber35Key mmFiber35Expected (mmFiber35RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber35ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber35StateAt 3) (mmFiber35StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber35StateAt 3) (mmFiber35StateAt 7)
    (mmFiber35RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber35Key mmFiber35Expected
        (mmFiber35RowAt 7) (by decide) mmFiber35ReverseRow_7_ok
      simpa [mmFiber35StateAt, mmFiber35RowAt, mmFiber35Rows, listGetD, directRow] using h)

theorem mmFiber35State0_in_close :
    mmFiber35StateAt 0 ∈ closeChainFiber mmWord mmFiber35DirectStates mmFiber35DirectStates.length [mmFiber35StateAt 0] := by
  change mmFiber35StateAt 0 ∈ closeChainFiber mmWord mmFiber35DirectStates 8 [mmFiber35StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber35DirectStates 0 8 [mmFiber35StateAt 0] (mmFiber35StateAt 0) (by simp [closeChainFiber])

theorem mmFiber35State1_in_close :
    mmFiber35StateAt 1 ∈ closeChainFiber mmWord mmFiber35DirectStates mmFiber35DirectStates.length [mmFiber35StateAt 0] := by
  have h0 : mmFiber35StateAt 0 ∈ closeChainFiber mmWord mmFiber35DirectStates 0 [mmFiber35StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber35StateAt 1 ∈ closeChainFiber mmWord mmFiber35DirectStates 1 [mmFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber35DirectStates 0 [mmFiber35StateAt 0]
      (mmFiber35StateAt 0) (mmFiber35StateAt 1) (by decide) h0 (by decide)
      mmFiber35ReverseSingleStep1
  change mmFiber35StateAt 1 ∈ closeChainFiber mmWord mmFiber35DirectStates (1 + 7) [mmFiber35StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber35DirectStates 1 7 [mmFiber35StateAt 0] (mmFiber35StateAt 1) h1

theorem mmFiber35State2_in_close :
    mmFiber35StateAt 2 ∈ closeChainFiber mmWord mmFiber35DirectStates mmFiber35DirectStates.length [mmFiber35StateAt 0] := by
  have h0 : mmFiber35StateAt 0 ∈ closeChainFiber mmWord mmFiber35DirectStates 0 [mmFiber35StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber35StateAt 2 ∈ closeChainFiber mmWord mmFiber35DirectStates 1 [mmFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber35DirectStates 0 [mmFiber35StateAt 0]
      (mmFiber35StateAt 0) (mmFiber35StateAt 2) (by decide) h0 (by decide)
      mmFiber35ReverseSingleStep2
  change mmFiber35StateAt 2 ∈ closeChainFiber mmWord mmFiber35DirectStates (1 + 7) [mmFiber35StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber35DirectStates 1 7 [mmFiber35StateAt 0] (mmFiber35StateAt 2) h1

theorem mmFiber35State3_in_close :
    mmFiber35StateAt 3 ∈ closeChainFiber mmWord mmFiber35DirectStates mmFiber35DirectStates.length [mmFiber35StateAt 0] := by
  have h0 : mmFiber35StateAt 0 ∈ closeChainFiber mmWord mmFiber35DirectStates 0 [mmFiber35StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber35StateAt 1 ∈ closeChainFiber mmWord mmFiber35DirectStates 1 [mmFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber35DirectStates 0 [mmFiber35StateAt 0]
      (mmFiber35StateAt 0) (mmFiber35StateAt 1) (by decide) h0 (by decide)
      mmFiber35ReverseSingleStep1
  have h2 : mmFiber35StateAt 3 ∈ closeChainFiber mmWord mmFiber35DirectStates 2 [mmFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber35DirectStates 1 [mmFiber35StateAt 0]
      (mmFiber35StateAt 1) (mmFiber35StateAt 3) (by decide) h1 (by decide)
      mmFiber35ReverseSingleStep3
  change mmFiber35StateAt 3 ∈ closeChainFiber mmWord mmFiber35DirectStates (2 + 6) [mmFiber35StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber35DirectStates 2 6 [mmFiber35StateAt 0] (mmFiber35StateAt 3) h2

theorem mmFiber35State4_in_close :
    mmFiber35StateAt 4 ∈ closeChainFiber mmWord mmFiber35DirectStates mmFiber35DirectStates.length [mmFiber35StateAt 0] := by
  have h0 : mmFiber35StateAt 0 ∈ closeChainFiber mmWord mmFiber35DirectStates 0 [mmFiber35StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber35StateAt 4 ∈ closeChainFiber mmWord mmFiber35DirectStates 1 [mmFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber35DirectStates 0 [mmFiber35StateAt 0]
      (mmFiber35StateAt 0) (mmFiber35StateAt 4) (by decide) h0 (by decide)
      mmFiber35ReverseSingleStep4
  change mmFiber35StateAt 4 ∈ closeChainFiber mmWord mmFiber35DirectStates (1 + 7) [mmFiber35StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber35DirectStates 1 7 [mmFiber35StateAt 0] (mmFiber35StateAt 4) h1

theorem mmFiber35State5_in_close :
    mmFiber35StateAt 5 ∈ closeChainFiber mmWord mmFiber35DirectStates mmFiber35DirectStates.length [mmFiber35StateAt 0] := by
  have h0 : mmFiber35StateAt 0 ∈ closeChainFiber mmWord mmFiber35DirectStates 0 [mmFiber35StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber35StateAt 1 ∈ closeChainFiber mmWord mmFiber35DirectStates 1 [mmFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber35DirectStates 0 [mmFiber35StateAt 0]
      (mmFiber35StateAt 0) (mmFiber35StateAt 1) (by decide) h0 (by decide)
      mmFiber35ReverseSingleStep1
  have h2 : mmFiber35StateAt 5 ∈ closeChainFiber mmWord mmFiber35DirectStates 2 [mmFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber35DirectStates 1 [mmFiber35StateAt 0]
      (mmFiber35StateAt 1) (mmFiber35StateAt 5) (by decide) h1 (by decide)
      mmFiber35ReverseSingleStep5
  change mmFiber35StateAt 5 ∈ closeChainFiber mmWord mmFiber35DirectStates (2 + 6) [mmFiber35StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber35DirectStates 2 6 [mmFiber35StateAt 0] (mmFiber35StateAt 5) h2

theorem mmFiber35State6_in_close :
    mmFiber35StateAt 6 ∈ closeChainFiber mmWord mmFiber35DirectStates mmFiber35DirectStates.length [mmFiber35StateAt 0] := by
  have h0 : mmFiber35StateAt 0 ∈ closeChainFiber mmWord mmFiber35DirectStates 0 [mmFiber35StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber35StateAt 2 ∈ closeChainFiber mmWord mmFiber35DirectStates 1 [mmFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber35DirectStates 0 [mmFiber35StateAt 0]
      (mmFiber35StateAt 0) (mmFiber35StateAt 2) (by decide) h0 (by decide)
      mmFiber35ReverseSingleStep2
  have h2 : mmFiber35StateAt 6 ∈ closeChainFiber mmWord mmFiber35DirectStates 2 [mmFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber35DirectStates 1 [mmFiber35StateAt 0]
      (mmFiber35StateAt 2) (mmFiber35StateAt 6) (by decide) h1 (by decide)
      mmFiber35ReverseSingleStep6
  change mmFiber35StateAt 6 ∈ closeChainFiber mmWord mmFiber35DirectStates (2 + 6) [mmFiber35StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber35DirectStates 2 6 [mmFiber35StateAt 0] (mmFiber35StateAt 6) h2

theorem mmFiber35State7_in_close :
    mmFiber35StateAt 7 ∈ closeChainFiber mmWord mmFiber35DirectStates mmFiber35DirectStates.length [mmFiber35StateAt 0] := by
  have h0 : mmFiber35StateAt 0 ∈ closeChainFiber mmWord mmFiber35DirectStates 0 [mmFiber35StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber35StateAt 1 ∈ closeChainFiber mmWord mmFiber35DirectStates 1 [mmFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber35DirectStates 0 [mmFiber35StateAt 0]
      (mmFiber35StateAt 0) (mmFiber35StateAt 1) (by decide) h0 (by decide)
      mmFiber35ReverseSingleStep1
  have h2 : mmFiber35StateAt 3 ∈ closeChainFiber mmWord mmFiber35DirectStates 2 [mmFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber35DirectStates 1 [mmFiber35StateAt 0]
      (mmFiber35StateAt 1) (mmFiber35StateAt 3) (by decide) h1 (by decide)
      mmFiber35ReverseSingleStep3
  have h3 : mmFiber35StateAt 7 ∈ closeChainFiber mmWord mmFiber35DirectStates 3 [mmFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber35DirectStates 2 [mmFiber35StateAt 0]
      (mmFiber35StateAt 3) (mmFiber35StateAt 7) (by decide) h2 (by decide)
      mmFiber35ReverseSingleStep7
  change mmFiber35StateAt 7 ∈ closeChainFiber mmWord mmFiber35DirectStates (3 + 5) [mmFiber35StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber35DirectStates 3 5 [mmFiber35StateAt 0] (mmFiber35StateAt 7) h3

theorem mmFiber35DirectConnected :
    chainFiberConnected mmWord mmFiber35DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber35DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber35State0_in_close
  · subst state
    exact mmFiber35State1_in_close
  · subst state
    exact mmFiber35State2_in_close
  · subst state
    exact mmFiber35State3_in_close
  · subst state
    exact mmFiber35State4_in_close
  · subst state
    exact mmFiber35State5_in_close
  · subst state
    exact mmFiber35State6_in_close
  · subst state
    exact mmFiber35State7_in_close
  · cases h
def mmFiber37StateAt (i : Nat) : List TauState :=
  directStates (mmFiber37RowAt i).sourceLeft (mmFiber37RowAt i).sourceRight

def mmFiber37DirectStates : List (List TauState) :=
  [mmFiber37StateAt 0, mmFiber37StateAt 1, mmFiber37StateAt 2, mmFiber37StateAt 3, mmFiber37StateAt 4, mmFiber37StateAt 5, mmFiber37StateAt 6, mmFiber37StateAt 7]

theorem mmFiber37ReverseRow_1_ok :
    mmRowReverseValid mmFiber37Key mmFiber37Expected (mmFiber37RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber37Chunk0_ok
  change (mmRowReverseValid mmFiber37Key mmFiber37Expected (mmFiber37RowAt 0) &&
    mmRowReverseValid mmFiber37Key mmFiber37Expected (mmFiber37RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber37ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber37StateAt 0) (mmFiber37StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber37StateAt 0) (mmFiber37StateAt 1)
    (mmFiber37RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber37Key mmFiber37Expected
        (mmFiber37RowAt 1) (by decide) mmFiber37ReverseRow_1_ok
      simpa [mmFiber37StateAt, mmFiber37RowAt, mmFiber37Rows, listGetD, directRow] using h)

theorem mmFiber37ReverseRow_2_ok :
    mmRowReverseValid mmFiber37Key mmFiber37Expected (mmFiber37RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber37Chunk1_ok
  change (mmRowReverseValid mmFiber37Key mmFiber37Expected (mmFiber37RowAt 2) &&
    mmRowReverseValid mmFiber37Key mmFiber37Expected (mmFiber37RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber37ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber37StateAt 0) (mmFiber37StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber37StateAt 0) (mmFiber37StateAt 2)
    (mmFiber37RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber37Key mmFiber37Expected
        (mmFiber37RowAt 2) (by decide) mmFiber37ReverseRow_2_ok
      simpa [mmFiber37StateAt, mmFiber37RowAt, mmFiber37Rows, listGetD, directRow] using h)

theorem mmFiber37ReverseRow_3_ok :
    mmRowReverseValid mmFiber37Key mmFiber37Expected (mmFiber37RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber37Chunk1_ok
  change (mmRowReverseValid mmFiber37Key mmFiber37Expected (mmFiber37RowAt 2) &&
    mmRowReverseValid mmFiber37Key mmFiber37Expected (mmFiber37RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber37ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber37StateAt 1) (mmFiber37StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber37StateAt 1) (mmFiber37StateAt 3)
    (mmFiber37RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber37Key mmFiber37Expected
        (mmFiber37RowAt 3) (by decide) mmFiber37ReverseRow_3_ok
      simpa [mmFiber37StateAt, mmFiber37RowAt, mmFiber37Rows, listGetD, directRow] using h)

theorem mmFiber37ReverseRow_4_ok :
    mmRowReverseValid mmFiber37Key mmFiber37Expected (mmFiber37RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber37Chunk2_ok
  change (mmRowReverseValid mmFiber37Key mmFiber37Expected (mmFiber37RowAt 4) &&
    mmRowReverseValid mmFiber37Key mmFiber37Expected (mmFiber37RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber37ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber37StateAt 0) (mmFiber37StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber37StateAt 0) (mmFiber37StateAt 4)
    (mmFiber37RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber37Key mmFiber37Expected
        (mmFiber37RowAt 4) (by decide) mmFiber37ReverseRow_4_ok
      simpa [mmFiber37StateAt, mmFiber37RowAt, mmFiber37Rows, listGetD, directRow] using h)

theorem mmFiber37ReverseRow_5_ok :
    mmRowReverseValid mmFiber37Key mmFiber37Expected (mmFiber37RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber37Chunk2_ok
  change (mmRowReverseValid mmFiber37Key mmFiber37Expected (mmFiber37RowAt 4) &&
    mmRowReverseValid mmFiber37Key mmFiber37Expected (mmFiber37RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber37ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber37StateAt 1) (mmFiber37StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber37StateAt 1) (mmFiber37StateAt 5)
    (mmFiber37RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber37Key mmFiber37Expected
        (mmFiber37RowAt 5) (by decide) mmFiber37ReverseRow_5_ok
      simpa [mmFiber37StateAt, mmFiber37RowAt, mmFiber37Rows, listGetD, directRow] using h)

theorem mmFiber37ReverseRow_6_ok :
    mmRowReverseValid mmFiber37Key mmFiber37Expected (mmFiber37RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber37Chunk3_ok
  change (mmRowReverseValid mmFiber37Key mmFiber37Expected (mmFiber37RowAt 6) &&
    mmRowReverseValid mmFiber37Key mmFiber37Expected (mmFiber37RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber37ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber37StateAt 2) (mmFiber37StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber37StateAt 2) (mmFiber37StateAt 6)
    (mmFiber37RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber37Key mmFiber37Expected
        (mmFiber37RowAt 6) (by decide) mmFiber37ReverseRow_6_ok
      simpa [mmFiber37StateAt, mmFiber37RowAt, mmFiber37Rows, listGetD, directRow] using h)

theorem mmFiber37ReverseRow_7_ok :
    mmRowReverseValid mmFiber37Key mmFiber37Expected (mmFiber37RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber37Chunk3_ok
  change (mmRowReverseValid mmFiber37Key mmFiber37Expected (mmFiber37RowAt 6) &&
    mmRowReverseValid mmFiber37Key mmFiber37Expected (mmFiber37RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber37ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber37StateAt 3) (mmFiber37StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber37StateAt 3) (mmFiber37StateAt 7)
    (mmFiber37RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber37Key mmFiber37Expected
        (mmFiber37RowAt 7) (by decide) mmFiber37ReverseRow_7_ok
      simpa [mmFiber37StateAt, mmFiber37RowAt, mmFiber37Rows, listGetD, directRow] using h)

theorem mmFiber37State0_in_close :
    mmFiber37StateAt 0 ∈ closeChainFiber mmWord mmFiber37DirectStates mmFiber37DirectStates.length [mmFiber37StateAt 0] := by
  change mmFiber37StateAt 0 ∈ closeChainFiber mmWord mmFiber37DirectStates 8 [mmFiber37StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber37DirectStates 0 8 [mmFiber37StateAt 0] (mmFiber37StateAt 0) (by simp [closeChainFiber])

theorem mmFiber37State1_in_close :
    mmFiber37StateAt 1 ∈ closeChainFiber mmWord mmFiber37DirectStates mmFiber37DirectStates.length [mmFiber37StateAt 0] := by
  have h0 : mmFiber37StateAt 0 ∈ closeChainFiber mmWord mmFiber37DirectStates 0 [mmFiber37StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber37StateAt 1 ∈ closeChainFiber mmWord mmFiber37DirectStates 1 [mmFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber37DirectStates 0 [mmFiber37StateAt 0]
      (mmFiber37StateAt 0) (mmFiber37StateAt 1) (by decide) h0 (by decide)
      mmFiber37ReverseSingleStep1
  change mmFiber37StateAt 1 ∈ closeChainFiber mmWord mmFiber37DirectStates (1 + 7) [mmFiber37StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber37DirectStates 1 7 [mmFiber37StateAt 0] (mmFiber37StateAt 1) h1

theorem mmFiber37State2_in_close :
    mmFiber37StateAt 2 ∈ closeChainFiber mmWord mmFiber37DirectStates mmFiber37DirectStates.length [mmFiber37StateAt 0] := by
  have h0 : mmFiber37StateAt 0 ∈ closeChainFiber mmWord mmFiber37DirectStates 0 [mmFiber37StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber37StateAt 2 ∈ closeChainFiber mmWord mmFiber37DirectStates 1 [mmFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber37DirectStates 0 [mmFiber37StateAt 0]
      (mmFiber37StateAt 0) (mmFiber37StateAt 2) (by decide) h0 (by decide)
      mmFiber37ReverseSingleStep2
  change mmFiber37StateAt 2 ∈ closeChainFiber mmWord mmFiber37DirectStates (1 + 7) [mmFiber37StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber37DirectStates 1 7 [mmFiber37StateAt 0] (mmFiber37StateAt 2) h1

theorem mmFiber37State3_in_close :
    mmFiber37StateAt 3 ∈ closeChainFiber mmWord mmFiber37DirectStates mmFiber37DirectStates.length [mmFiber37StateAt 0] := by
  have h0 : mmFiber37StateAt 0 ∈ closeChainFiber mmWord mmFiber37DirectStates 0 [mmFiber37StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber37StateAt 1 ∈ closeChainFiber mmWord mmFiber37DirectStates 1 [mmFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber37DirectStates 0 [mmFiber37StateAt 0]
      (mmFiber37StateAt 0) (mmFiber37StateAt 1) (by decide) h0 (by decide)
      mmFiber37ReverseSingleStep1
  have h2 : mmFiber37StateAt 3 ∈ closeChainFiber mmWord mmFiber37DirectStates 2 [mmFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber37DirectStates 1 [mmFiber37StateAt 0]
      (mmFiber37StateAt 1) (mmFiber37StateAt 3) (by decide) h1 (by decide)
      mmFiber37ReverseSingleStep3
  change mmFiber37StateAt 3 ∈ closeChainFiber mmWord mmFiber37DirectStates (2 + 6) [mmFiber37StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber37DirectStates 2 6 [mmFiber37StateAt 0] (mmFiber37StateAt 3) h2

theorem mmFiber37State4_in_close :
    mmFiber37StateAt 4 ∈ closeChainFiber mmWord mmFiber37DirectStates mmFiber37DirectStates.length [mmFiber37StateAt 0] := by
  have h0 : mmFiber37StateAt 0 ∈ closeChainFiber mmWord mmFiber37DirectStates 0 [mmFiber37StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber37StateAt 4 ∈ closeChainFiber mmWord mmFiber37DirectStates 1 [mmFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber37DirectStates 0 [mmFiber37StateAt 0]
      (mmFiber37StateAt 0) (mmFiber37StateAt 4) (by decide) h0 (by decide)
      mmFiber37ReverseSingleStep4
  change mmFiber37StateAt 4 ∈ closeChainFiber mmWord mmFiber37DirectStates (1 + 7) [mmFiber37StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber37DirectStates 1 7 [mmFiber37StateAt 0] (mmFiber37StateAt 4) h1

theorem mmFiber37State5_in_close :
    mmFiber37StateAt 5 ∈ closeChainFiber mmWord mmFiber37DirectStates mmFiber37DirectStates.length [mmFiber37StateAt 0] := by
  have h0 : mmFiber37StateAt 0 ∈ closeChainFiber mmWord mmFiber37DirectStates 0 [mmFiber37StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber37StateAt 1 ∈ closeChainFiber mmWord mmFiber37DirectStates 1 [mmFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber37DirectStates 0 [mmFiber37StateAt 0]
      (mmFiber37StateAt 0) (mmFiber37StateAt 1) (by decide) h0 (by decide)
      mmFiber37ReverseSingleStep1
  have h2 : mmFiber37StateAt 5 ∈ closeChainFiber mmWord mmFiber37DirectStates 2 [mmFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber37DirectStates 1 [mmFiber37StateAt 0]
      (mmFiber37StateAt 1) (mmFiber37StateAt 5) (by decide) h1 (by decide)
      mmFiber37ReverseSingleStep5
  change mmFiber37StateAt 5 ∈ closeChainFiber mmWord mmFiber37DirectStates (2 + 6) [mmFiber37StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber37DirectStates 2 6 [mmFiber37StateAt 0] (mmFiber37StateAt 5) h2

theorem mmFiber37State6_in_close :
    mmFiber37StateAt 6 ∈ closeChainFiber mmWord mmFiber37DirectStates mmFiber37DirectStates.length [mmFiber37StateAt 0] := by
  have h0 : mmFiber37StateAt 0 ∈ closeChainFiber mmWord mmFiber37DirectStates 0 [mmFiber37StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber37StateAt 2 ∈ closeChainFiber mmWord mmFiber37DirectStates 1 [mmFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber37DirectStates 0 [mmFiber37StateAt 0]
      (mmFiber37StateAt 0) (mmFiber37StateAt 2) (by decide) h0 (by decide)
      mmFiber37ReverseSingleStep2
  have h2 : mmFiber37StateAt 6 ∈ closeChainFiber mmWord mmFiber37DirectStates 2 [mmFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber37DirectStates 1 [mmFiber37StateAt 0]
      (mmFiber37StateAt 2) (mmFiber37StateAt 6) (by decide) h1 (by decide)
      mmFiber37ReverseSingleStep6
  change mmFiber37StateAt 6 ∈ closeChainFiber mmWord mmFiber37DirectStates (2 + 6) [mmFiber37StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber37DirectStates 2 6 [mmFiber37StateAt 0] (mmFiber37StateAt 6) h2

theorem mmFiber37State7_in_close :
    mmFiber37StateAt 7 ∈ closeChainFiber mmWord mmFiber37DirectStates mmFiber37DirectStates.length [mmFiber37StateAt 0] := by
  have h0 : mmFiber37StateAt 0 ∈ closeChainFiber mmWord mmFiber37DirectStates 0 [mmFiber37StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber37StateAt 1 ∈ closeChainFiber mmWord mmFiber37DirectStates 1 [mmFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber37DirectStates 0 [mmFiber37StateAt 0]
      (mmFiber37StateAt 0) (mmFiber37StateAt 1) (by decide) h0 (by decide)
      mmFiber37ReverseSingleStep1
  have h2 : mmFiber37StateAt 3 ∈ closeChainFiber mmWord mmFiber37DirectStates 2 [mmFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber37DirectStates 1 [mmFiber37StateAt 0]
      (mmFiber37StateAt 1) (mmFiber37StateAt 3) (by decide) h1 (by decide)
      mmFiber37ReverseSingleStep3
  have h3 : mmFiber37StateAt 7 ∈ closeChainFiber mmWord mmFiber37DirectStates 3 [mmFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber37DirectStates 2 [mmFiber37StateAt 0]
      (mmFiber37StateAt 3) (mmFiber37StateAt 7) (by decide) h2 (by decide)
      mmFiber37ReverseSingleStep7
  change mmFiber37StateAt 7 ∈ closeChainFiber mmWord mmFiber37DirectStates (3 + 5) [mmFiber37StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber37DirectStates 3 5 [mmFiber37StateAt 0] (mmFiber37StateAt 7) h3

theorem mmFiber37DirectConnected :
    chainFiberConnected mmWord mmFiber37DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber37DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber37State0_in_close
  · subst state
    exact mmFiber37State1_in_close
  · subst state
    exact mmFiber37State2_in_close
  · subst state
    exact mmFiber37State3_in_close
  · subst state
    exact mmFiber37State4_in_close
  · subst state
    exact mmFiber37State5_in_close
  · subst state
    exact mmFiber37State6_in_close
  · subst state
    exact mmFiber37State7_in_close
  · cases h
end GoertzelLemma818LengthTwoMMBridge

end Mettapedia.GraphTheory.FourColor
