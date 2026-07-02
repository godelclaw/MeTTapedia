import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for size-8 `mirror,mirror` length-two fibers, group 5

This module proves direct connectedness for generated `mirror,mirror` size-8 fibers from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMMBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorMirrorCertificate
open GoertzelLemma818MirrorMirrorReverseAudit

def mmFiber64StateAt (i : Nat) : List TauState :=
  directStates (mmFiber64RowAt i).sourceLeft (mmFiber64RowAt i).sourceRight

def mmFiber64DirectStates : List (List TauState) :=
  [mmFiber64StateAt 0, mmFiber64StateAt 1, mmFiber64StateAt 2, mmFiber64StateAt 3, mmFiber64StateAt 4, mmFiber64StateAt 5, mmFiber64StateAt 6, mmFiber64StateAt 7]

theorem mmFiber64ReverseRow_1_ok :
    mmRowReverseValid mmFiber64Key mmFiber64Expected (mmFiber64RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber64Chunk0_ok
  change (mmRowReverseValid mmFiber64Key mmFiber64Expected (mmFiber64RowAt 0) &&
    mmRowReverseValid mmFiber64Key mmFiber64Expected (mmFiber64RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber64ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber64StateAt 0) (mmFiber64StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber64StateAt 0) (mmFiber64StateAt 1)
    (mmFiber64RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber64Key mmFiber64Expected
        (mmFiber64RowAt 1) (by decide) mmFiber64ReverseRow_1_ok
      simpa [mmFiber64StateAt, mmFiber64RowAt, mmFiber64Rows, listGetD, directRow] using h)

theorem mmFiber64ReverseRow_2_ok :
    mmRowReverseValid mmFiber64Key mmFiber64Expected (mmFiber64RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber64Chunk1_ok
  change (mmRowReverseValid mmFiber64Key mmFiber64Expected (mmFiber64RowAt 2) &&
    mmRowReverseValid mmFiber64Key mmFiber64Expected (mmFiber64RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber64ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber64StateAt 0) (mmFiber64StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber64StateAt 0) (mmFiber64StateAt 2)
    (mmFiber64RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber64Key mmFiber64Expected
        (mmFiber64RowAt 2) (by decide) mmFiber64ReverseRow_2_ok
      simpa [mmFiber64StateAt, mmFiber64RowAt, mmFiber64Rows, listGetD, directRow] using h)

theorem mmFiber64ReverseRow_3_ok :
    mmRowReverseValid mmFiber64Key mmFiber64Expected (mmFiber64RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber64Chunk1_ok
  change (mmRowReverseValid mmFiber64Key mmFiber64Expected (mmFiber64RowAt 2) &&
    mmRowReverseValid mmFiber64Key mmFiber64Expected (mmFiber64RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber64ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber64StateAt 1) (mmFiber64StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber64StateAt 1) (mmFiber64StateAt 3)
    (mmFiber64RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber64Key mmFiber64Expected
        (mmFiber64RowAt 3) (by decide) mmFiber64ReverseRow_3_ok
      simpa [mmFiber64StateAt, mmFiber64RowAt, mmFiber64Rows, listGetD, directRow] using h)

theorem mmFiber64ReverseRow_4_ok :
    mmRowReverseValid mmFiber64Key mmFiber64Expected (mmFiber64RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber64Chunk2_ok
  change (mmRowReverseValid mmFiber64Key mmFiber64Expected (mmFiber64RowAt 4) &&
    mmRowReverseValid mmFiber64Key mmFiber64Expected (mmFiber64RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber64ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber64StateAt 0) (mmFiber64StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber64StateAt 0) (mmFiber64StateAt 4)
    (mmFiber64RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber64Key mmFiber64Expected
        (mmFiber64RowAt 4) (by decide) mmFiber64ReverseRow_4_ok
      simpa [mmFiber64StateAt, mmFiber64RowAt, mmFiber64Rows, listGetD, directRow] using h)

theorem mmFiber64ReverseRow_5_ok :
    mmRowReverseValid mmFiber64Key mmFiber64Expected (mmFiber64RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber64Chunk2_ok
  change (mmRowReverseValid mmFiber64Key mmFiber64Expected (mmFiber64RowAt 4) &&
    mmRowReverseValid mmFiber64Key mmFiber64Expected (mmFiber64RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber64ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber64StateAt 1) (mmFiber64StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber64StateAt 1) (mmFiber64StateAt 5)
    (mmFiber64RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber64Key mmFiber64Expected
        (mmFiber64RowAt 5) (by decide) mmFiber64ReverseRow_5_ok
      simpa [mmFiber64StateAt, mmFiber64RowAt, mmFiber64Rows, listGetD, directRow] using h)

theorem mmFiber64ReverseRow_6_ok :
    mmRowReverseValid mmFiber64Key mmFiber64Expected (mmFiber64RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber64Chunk3_ok
  change (mmRowReverseValid mmFiber64Key mmFiber64Expected (mmFiber64RowAt 6) &&
    mmRowReverseValid mmFiber64Key mmFiber64Expected (mmFiber64RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber64ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber64StateAt 2) (mmFiber64StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber64StateAt 2) (mmFiber64StateAt 6)
    (mmFiber64RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber64Key mmFiber64Expected
        (mmFiber64RowAt 6) (by decide) mmFiber64ReverseRow_6_ok
      simpa [mmFiber64StateAt, mmFiber64RowAt, mmFiber64Rows, listGetD, directRow] using h)

theorem mmFiber64ReverseRow_7_ok :
    mmRowReverseValid mmFiber64Key mmFiber64Expected (mmFiber64RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber64Chunk3_ok
  change (mmRowReverseValid mmFiber64Key mmFiber64Expected (mmFiber64RowAt 6) &&
    mmRowReverseValid mmFiber64Key mmFiber64Expected (mmFiber64RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber64ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber64StateAt 3) (mmFiber64StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber64StateAt 3) (mmFiber64StateAt 7)
    (mmFiber64RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber64Key mmFiber64Expected
        (mmFiber64RowAt 7) (by decide) mmFiber64ReverseRow_7_ok
      simpa [mmFiber64StateAt, mmFiber64RowAt, mmFiber64Rows, listGetD, directRow] using h)

theorem mmFiber64State0_in_close :
    mmFiber64StateAt 0 ∈ closeChainFiber mmWord mmFiber64DirectStates mmFiber64DirectStates.length [mmFiber64StateAt 0] := by
  change mmFiber64StateAt 0 ∈ closeChainFiber mmWord mmFiber64DirectStates 8 [mmFiber64StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber64DirectStates 0 8 [mmFiber64StateAt 0] (mmFiber64StateAt 0) (by simp [closeChainFiber])

theorem mmFiber64State1_in_close :
    mmFiber64StateAt 1 ∈ closeChainFiber mmWord mmFiber64DirectStates mmFiber64DirectStates.length [mmFiber64StateAt 0] := by
  have h0 : mmFiber64StateAt 0 ∈ closeChainFiber mmWord mmFiber64DirectStates 0 [mmFiber64StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber64StateAt 1 ∈ closeChainFiber mmWord mmFiber64DirectStates 1 [mmFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber64DirectStates 0 [mmFiber64StateAt 0]
      (mmFiber64StateAt 0) (mmFiber64StateAt 1) (by decide) h0 (by decide)
      mmFiber64ReverseSingleStep1
  change mmFiber64StateAt 1 ∈ closeChainFiber mmWord mmFiber64DirectStates (1 + 7) [mmFiber64StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber64DirectStates 1 7 [mmFiber64StateAt 0] (mmFiber64StateAt 1) h1

theorem mmFiber64State2_in_close :
    mmFiber64StateAt 2 ∈ closeChainFiber mmWord mmFiber64DirectStates mmFiber64DirectStates.length [mmFiber64StateAt 0] := by
  have h0 : mmFiber64StateAt 0 ∈ closeChainFiber mmWord mmFiber64DirectStates 0 [mmFiber64StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber64StateAt 2 ∈ closeChainFiber mmWord mmFiber64DirectStates 1 [mmFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber64DirectStates 0 [mmFiber64StateAt 0]
      (mmFiber64StateAt 0) (mmFiber64StateAt 2) (by decide) h0 (by decide)
      mmFiber64ReverseSingleStep2
  change mmFiber64StateAt 2 ∈ closeChainFiber mmWord mmFiber64DirectStates (1 + 7) [mmFiber64StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber64DirectStates 1 7 [mmFiber64StateAt 0] (mmFiber64StateAt 2) h1

theorem mmFiber64State3_in_close :
    mmFiber64StateAt 3 ∈ closeChainFiber mmWord mmFiber64DirectStates mmFiber64DirectStates.length [mmFiber64StateAt 0] := by
  have h0 : mmFiber64StateAt 0 ∈ closeChainFiber mmWord mmFiber64DirectStates 0 [mmFiber64StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber64StateAt 1 ∈ closeChainFiber mmWord mmFiber64DirectStates 1 [mmFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber64DirectStates 0 [mmFiber64StateAt 0]
      (mmFiber64StateAt 0) (mmFiber64StateAt 1) (by decide) h0 (by decide)
      mmFiber64ReverseSingleStep1
  have h2 : mmFiber64StateAt 3 ∈ closeChainFiber mmWord mmFiber64DirectStates 2 [mmFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber64DirectStates 1 [mmFiber64StateAt 0]
      (mmFiber64StateAt 1) (mmFiber64StateAt 3) (by decide) h1 (by decide)
      mmFiber64ReverseSingleStep3
  change mmFiber64StateAt 3 ∈ closeChainFiber mmWord mmFiber64DirectStates (2 + 6) [mmFiber64StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber64DirectStates 2 6 [mmFiber64StateAt 0] (mmFiber64StateAt 3) h2

theorem mmFiber64State4_in_close :
    mmFiber64StateAt 4 ∈ closeChainFiber mmWord mmFiber64DirectStates mmFiber64DirectStates.length [mmFiber64StateAt 0] := by
  have h0 : mmFiber64StateAt 0 ∈ closeChainFiber mmWord mmFiber64DirectStates 0 [mmFiber64StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber64StateAt 4 ∈ closeChainFiber mmWord mmFiber64DirectStates 1 [mmFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber64DirectStates 0 [mmFiber64StateAt 0]
      (mmFiber64StateAt 0) (mmFiber64StateAt 4) (by decide) h0 (by decide)
      mmFiber64ReverseSingleStep4
  change mmFiber64StateAt 4 ∈ closeChainFiber mmWord mmFiber64DirectStates (1 + 7) [mmFiber64StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber64DirectStates 1 7 [mmFiber64StateAt 0] (mmFiber64StateAt 4) h1

theorem mmFiber64State5_in_close :
    mmFiber64StateAt 5 ∈ closeChainFiber mmWord mmFiber64DirectStates mmFiber64DirectStates.length [mmFiber64StateAt 0] := by
  have h0 : mmFiber64StateAt 0 ∈ closeChainFiber mmWord mmFiber64DirectStates 0 [mmFiber64StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber64StateAt 1 ∈ closeChainFiber mmWord mmFiber64DirectStates 1 [mmFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber64DirectStates 0 [mmFiber64StateAt 0]
      (mmFiber64StateAt 0) (mmFiber64StateAt 1) (by decide) h0 (by decide)
      mmFiber64ReverseSingleStep1
  have h2 : mmFiber64StateAt 5 ∈ closeChainFiber mmWord mmFiber64DirectStates 2 [mmFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber64DirectStates 1 [mmFiber64StateAt 0]
      (mmFiber64StateAt 1) (mmFiber64StateAt 5) (by decide) h1 (by decide)
      mmFiber64ReverseSingleStep5
  change mmFiber64StateAt 5 ∈ closeChainFiber mmWord mmFiber64DirectStates (2 + 6) [mmFiber64StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber64DirectStates 2 6 [mmFiber64StateAt 0] (mmFiber64StateAt 5) h2

theorem mmFiber64State6_in_close :
    mmFiber64StateAt 6 ∈ closeChainFiber mmWord mmFiber64DirectStates mmFiber64DirectStates.length [mmFiber64StateAt 0] := by
  have h0 : mmFiber64StateAt 0 ∈ closeChainFiber mmWord mmFiber64DirectStates 0 [mmFiber64StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber64StateAt 2 ∈ closeChainFiber mmWord mmFiber64DirectStates 1 [mmFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber64DirectStates 0 [mmFiber64StateAt 0]
      (mmFiber64StateAt 0) (mmFiber64StateAt 2) (by decide) h0 (by decide)
      mmFiber64ReverseSingleStep2
  have h2 : mmFiber64StateAt 6 ∈ closeChainFiber mmWord mmFiber64DirectStates 2 [mmFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber64DirectStates 1 [mmFiber64StateAt 0]
      (mmFiber64StateAt 2) (mmFiber64StateAt 6) (by decide) h1 (by decide)
      mmFiber64ReverseSingleStep6
  change mmFiber64StateAt 6 ∈ closeChainFiber mmWord mmFiber64DirectStates (2 + 6) [mmFiber64StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber64DirectStates 2 6 [mmFiber64StateAt 0] (mmFiber64StateAt 6) h2

theorem mmFiber64State7_in_close :
    mmFiber64StateAt 7 ∈ closeChainFiber mmWord mmFiber64DirectStates mmFiber64DirectStates.length [mmFiber64StateAt 0] := by
  have h0 : mmFiber64StateAt 0 ∈ closeChainFiber mmWord mmFiber64DirectStates 0 [mmFiber64StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber64StateAt 1 ∈ closeChainFiber mmWord mmFiber64DirectStates 1 [mmFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber64DirectStates 0 [mmFiber64StateAt 0]
      (mmFiber64StateAt 0) (mmFiber64StateAt 1) (by decide) h0 (by decide)
      mmFiber64ReverseSingleStep1
  have h2 : mmFiber64StateAt 3 ∈ closeChainFiber mmWord mmFiber64DirectStates 2 [mmFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber64DirectStates 1 [mmFiber64StateAt 0]
      (mmFiber64StateAt 1) (mmFiber64StateAt 3) (by decide) h1 (by decide)
      mmFiber64ReverseSingleStep3
  have h3 : mmFiber64StateAt 7 ∈ closeChainFiber mmWord mmFiber64DirectStates 3 [mmFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber64DirectStates 2 [mmFiber64StateAt 0]
      (mmFiber64StateAt 3) (mmFiber64StateAt 7) (by decide) h2 (by decide)
      mmFiber64ReverseSingleStep7
  change mmFiber64StateAt 7 ∈ closeChainFiber mmWord mmFiber64DirectStates (3 + 5) [mmFiber64StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber64DirectStates 3 5 [mmFiber64StateAt 0] (mmFiber64StateAt 7) h3

theorem mmFiber64DirectConnected :
    chainFiberConnected mmWord mmFiber64DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber64DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber64State0_in_close
  · subst state
    exact mmFiber64State1_in_close
  · subst state
    exact mmFiber64State2_in_close
  · subst state
    exact mmFiber64State3_in_close
  · subst state
    exact mmFiber64State4_in_close
  · subst state
    exact mmFiber64State5_in_close
  · subst state
    exact mmFiber64State6_in_close
  · subst state
    exact mmFiber64State7_in_close
  · cases h
def mmFiber71StateAt (i : Nat) : List TauState :=
  directStates (mmFiber71RowAt i).sourceLeft (mmFiber71RowAt i).sourceRight

def mmFiber71DirectStates : List (List TauState) :=
  [mmFiber71StateAt 0, mmFiber71StateAt 1, mmFiber71StateAt 2, mmFiber71StateAt 3, mmFiber71StateAt 4, mmFiber71StateAt 5, mmFiber71StateAt 6, mmFiber71StateAt 7]

theorem mmFiber71ReverseRow_1_ok :
    mmRowReverseValid mmFiber71Key mmFiber71Expected (mmFiber71RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber71Chunk0_ok
  change (mmRowReverseValid mmFiber71Key mmFiber71Expected (mmFiber71RowAt 0) &&
    mmRowReverseValid mmFiber71Key mmFiber71Expected (mmFiber71RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber71ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber71StateAt 0) (mmFiber71StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber71StateAt 0) (mmFiber71StateAt 1)
    (mmFiber71RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber71Key mmFiber71Expected
        (mmFiber71RowAt 1) (by decide) mmFiber71ReverseRow_1_ok
      simpa [mmFiber71StateAt, mmFiber71RowAt, mmFiber71Rows, listGetD, directRow] using h)

theorem mmFiber71ReverseRow_2_ok :
    mmRowReverseValid mmFiber71Key mmFiber71Expected (mmFiber71RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber71Chunk1_ok
  change (mmRowReverseValid mmFiber71Key mmFiber71Expected (mmFiber71RowAt 2) &&
    mmRowReverseValid mmFiber71Key mmFiber71Expected (mmFiber71RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber71ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber71StateAt 1) (mmFiber71StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber71StateAt 1) (mmFiber71StateAt 2)
    (mmFiber71RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber71Key mmFiber71Expected
        (mmFiber71RowAt 2) (by decide) mmFiber71ReverseRow_2_ok
      simpa [mmFiber71StateAt, mmFiber71RowAt, mmFiber71Rows, listGetD, directRow] using h)

theorem mmFiber71ReverseRow_3_ok :
    mmRowReverseValid mmFiber71Key mmFiber71Expected (mmFiber71RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber71Chunk1_ok
  change (mmRowReverseValid mmFiber71Key mmFiber71Expected (mmFiber71RowAt 2) &&
    mmRowReverseValid mmFiber71Key mmFiber71Expected (mmFiber71RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber71ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber71StateAt 0) (mmFiber71StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber71StateAt 0) (mmFiber71StateAt 3)
    (mmFiber71RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber71Key mmFiber71Expected
        (mmFiber71RowAt 3) (by decide) mmFiber71ReverseRow_3_ok
      simpa [mmFiber71StateAt, mmFiber71RowAt, mmFiber71Rows, listGetD, directRow] using h)

theorem mmFiber71ReverseRow_4_ok :
    mmRowReverseValid mmFiber71Key mmFiber71Expected (mmFiber71RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber71Chunk2_ok
  change (mmRowReverseValid mmFiber71Key mmFiber71Expected (mmFiber71RowAt 4) &&
    mmRowReverseValid mmFiber71Key mmFiber71Expected (mmFiber71RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber71ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber71StateAt 0) (mmFiber71StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber71StateAt 0) (mmFiber71StateAt 4)
    (mmFiber71RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber71Key mmFiber71Expected
        (mmFiber71RowAt 4) (by decide) mmFiber71ReverseRow_4_ok
      simpa [mmFiber71StateAt, mmFiber71RowAt, mmFiber71Rows, listGetD, directRow] using h)

theorem mmFiber71ReverseRow_5_ok :
    mmRowReverseValid mmFiber71Key mmFiber71Expected (mmFiber71RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber71Chunk2_ok
  change (mmRowReverseValid mmFiber71Key mmFiber71Expected (mmFiber71RowAt 4) &&
    mmRowReverseValid mmFiber71Key mmFiber71Expected (mmFiber71RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber71ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber71StateAt 1) (mmFiber71StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber71StateAt 1) (mmFiber71StateAt 5)
    (mmFiber71RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber71Key mmFiber71Expected
        (mmFiber71RowAt 5) (by decide) mmFiber71ReverseRow_5_ok
      simpa [mmFiber71StateAt, mmFiber71RowAt, mmFiber71Rows, listGetD, directRow] using h)

theorem mmFiber71ReverseRow_6_ok :
    mmRowReverseValid mmFiber71Key mmFiber71Expected (mmFiber71RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber71Chunk3_ok
  change (mmRowReverseValid mmFiber71Key mmFiber71Expected (mmFiber71RowAt 6) &&
    mmRowReverseValid mmFiber71Key mmFiber71Expected (mmFiber71RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber71ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber71StateAt 2) (mmFiber71StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber71StateAt 2) (mmFiber71StateAt 6)
    (mmFiber71RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber71Key mmFiber71Expected
        (mmFiber71RowAt 6) (by decide) mmFiber71ReverseRow_6_ok
      simpa [mmFiber71StateAt, mmFiber71RowAt, mmFiber71Rows, listGetD, directRow] using h)

theorem mmFiber71ReverseRow_7_ok :
    mmRowReverseValid mmFiber71Key mmFiber71Expected (mmFiber71RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber71Chunk3_ok
  change (mmRowReverseValid mmFiber71Key mmFiber71Expected (mmFiber71RowAt 6) &&
    mmRowReverseValid mmFiber71Key mmFiber71Expected (mmFiber71RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber71ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber71StateAt 3) (mmFiber71StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber71StateAt 3) (mmFiber71StateAt 7)
    (mmFiber71RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber71Key mmFiber71Expected
        (mmFiber71RowAt 7) (by decide) mmFiber71ReverseRow_7_ok
      simpa [mmFiber71StateAt, mmFiber71RowAt, mmFiber71Rows, listGetD, directRow] using h)

theorem mmFiber71State0_in_close :
    mmFiber71StateAt 0 ∈ closeChainFiber mmWord mmFiber71DirectStates mmFiber71DirectStates.length [mmFiber71StateAt 0] := by
  change mmFiber71StateAt 0 ∈ closeChainFiber mmWord mmFiber71DirectStates 8 [mmFiber71StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber71DirectStates 0 8 [mmFiber71StateAt 0] (mmFiber71StateAt 0) (by simp [closeChainFiber])

theorem mmFiber71State1_in_close :
    mmFiber71StateAt 1 ∈ closeChainFiber mmWord mmFiber71DirectStates mmFiber71DirectStates.length [mmFiber71StateAt 0] := by
  have h0 : mmFiber71StateAt 0 ∈ closeChainFiber mmWord mmFiber71DirectStates 0 [mmFiber71StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber71StateAt 1 ∈ closeChainFiber mmWord mmFiber71DirectStates 1 [mmFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber71DirectStates 0 [mmFiber71StateAt 0]
      (mmFiber71StateAt 0) (mmFiber71StateAt 1) (by decide) h0 (by decide)
      mmFiber71ReverseSingleStep1
  change mmFiber71StateAt 1 ∈ closeChainFiber mmWord mmFiber71DirectStates (1 + 7) [mmFiber71StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber71DirectStates 1 7 [mmFiber71StateAt 0] (mmFiber71StateAt 1) h1

theorem mmFiber71State2_in_close :
    mmFiber71StateAt 2 ∈ closeChainFiber mmWord mmFiber71DirectStates mmFiber71DirectStates.length [mmFiber71StateAt 0] := by
  have h0 : mmFiber71StateAt 0 ∈ closeChainFiber mmWord mmFiber71DirectStates 0 [mmFiber71StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber71StateAt 1 ∈ closeChainFiber mmWord mmFiber71DirectStates 1 [mmFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber71DirectStates 0 [mmFiber71StateAt 0]
      (mmFiber71StateAt 0) (mmFiber71StateAt 1) (by decide) h0 (by decide)
      mmFiber71ReverseSingleStep1
  have h2 : mmFiber71StateAt 2 ∈ closeChainFiber mmWord mmFiber71DirectStates 2 [mmFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber71DirectStates 1 [mmFiber71StateAt 0]
      (mmFiber71StateAt 1) (mmFiber71StateAt 2) (by decide) h1 (by decide)
      mmFiber71ReverseSingleStep2
  change mmFiber71StateAt 2 ∈ closeChainFiber mmWord mmFiber71DirectStates (2 + 6) [mmFiber71StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber71DirectStates 2 6 [mmFiber71StateAt 0] (mmFiber71StateAt 2) h2

theorem mmFiber71State3_in_close :
    mmFiber71StateAt 3 ∈ closeChainFiber mmWord mmFiber71DirectStates mmFiber71DirectStates.length [mmFiber71StateAt 0] := by
  have h0 : mmFiber71StateAt 0 ∈ closeChainFiber mmWord mmFiber71DirectStates 0 [mmFiber71StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber71StateAt 3 ∈ closeChainFiber mmWord mmFiber71DirectStates 1 [mmFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber71DirectStates 0 [mmFiber71StateAt 0]
      (mmFiber71StateAt 0) (mmFiber71StateAt 3) (by decide) h0 (by decide)
      mmFiber71ReverseSingleStep3
  change mmFiber71StateAt 3 ∈ closeChainFiber mmWord mmFiber71DirectStates (1 + 7) [mmFiber71StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber71DirectStates 1 7 [mmFiber71StateAt 0] (mmFiber71StateAt 3) h1

theorem mmFiber71State4_in_close :
    mmFiber71StateAt 4 ∈ closeChainFiber mmWord mmFiber71DirectStates mmFiber71DirectStates.length [mmFiber71StateAt 0] := by
  have h0 : mmFiber71StateAt 0 ∈ closeChainFiber mmWord mmFiber71DirectStates 0 [mmFiber71StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber71StateAt 4 ∈ closeChainFiber mmWord mmFiber71DirectStates 1 [mmFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber71DirectStates 0 [mmFiber71StateAt 0]
      (mmFiber71StateAt 0) (mmFiber71StateAt 4) (by decide) h0 (by decide)
      mmFiber71ReverseSingleStep4
  change mmFiber71StateAt 4 ∈ closeChainFiber mmWord mmFiber71DirectStates (1 + 7) [mmFiber71StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber71DirectStates 1 7 [mmFiber71StateAt 0] (mmFiber71StateAt 4) h1

theorem mmFiber71State5_in_close :
    mmFiber71StateAt 5 ∈ closeChainFiber mmWord mmFiber71DirectStates mmFiber71DirectStates.length [mmFiber71StateAt 0] := by
  have h0 : mmFiber71StateAt 0 ∈ closeChainFiber mmWord mmFiber71DirectStates 0 [mmFiber71StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber71StateAt 1 ∈ closeChainFiber mmWord mmFiber71DirectStates 1 [mmFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber71DirectStates 0 [mmFiber71StateAt 0]
      (mmFiber71StateAt 0) (mmFiber71StateAt 1) (by decide) h0 (by decide)
      mmFiber71ReverseSingleStep1
  have h2 : mmFiber71StateAt 5 ∈ closeChainFiber mmWord mmFiber71DirectStates 2 [mmFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber71DirectStates 1 [mmFiber71StateAt 0]
      (mmFiber71StateAt 1) (mmFiber71StateAt 5) (by decide) h1 (by decide)
      mmFiber71ReverseSingleStep5
  change mmFiber71StateAt 5 ∈ closeChainFiber mmWord mmFiber71DirectStates (2 + 6) [mmFiber71StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber71DirectStates 2 6 [mmFiber71StateAt 0] (mmFiber71StateAt 5) h2

theorem mmFiber71State6_in_close :
    mmFiber71StateAt 6 ∈ closeChainFiber mmWord mmFiber71DirectStates mmFiber71DirectStates.length [mmFiber71StateAt 0] := by
  have h0 : mmFiber71StateAt 0 ∈ closeChainFiber mmWord mmFiber71DirectStates 0 [mmFiber71StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber71StateAt 1 ∈ closeChainFiber mmWord mmFiber71DirectStates 1 [mmFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber71DirectStates 0 [mmFiber71StateAt 0]
      (mmFiber71StateAt 0) (mmFiber71StateAt 1) (by decide) h0 (by decide)
      mmFiber71ReverseSingleStep1
  have h2 : mmFiber71StateAt 2 ∈ closeChainFiber mmWord mmFiber71DirectStates 2 [mmFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber71DirectStates 1 [mmFiber71StateAt 0]
      (mmFiber71StateAt 1) (mmFiber71StateAt 2) (by decide) h1 (by decide)
      mmFiber71ReverseSingleStep2
  have h3 : mmFiber71StateAt 6 ∈ closeChainFiber mmWord mmFiber71DirectStates 3 [mmFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber71DirectStates 2 [mmFiber71StateAt 0]
      (mmFiber71StateAt 2) (mmFiber71StateAt 6) (by decide) h2 (by decide)
      mmFiber71ReverseSingleStep6
  change mmFiber71StateAt 6 ∈ closeChainFiber mmWord mmFiber71DirectStates (3 + 5) [mmFiber71StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber71DirectStates 3 5 [mmFiber71StateAt 0] (mmFiber71StateAt 6) h3

theorem mmFiber71State7_in_close :
    mmFiber71StateAt 7 ∈ closeChainFiber mmWord mmFiber71DirectStates mmFiber71DirectStates.length [mmFiber71StateAt 0] := by
  have h0 : mmFiber71StateAt 0 ∈ closeChainFiber mmWord mmFiber71DirectStates 0 [mmFiber71StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber71StateAt 3 ∈ closeChainFiber mmWord mmFiber71DirectStates 1 [mmFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber71DirectStates 0 [mmFiber71StateAt 0]
      (mmFiber71StateAt 0) (mmFiber71StateAt 3) (by decide) h0 (by decide)
      mmFiber71ReverseSingleStep3
  have h2 : mmFiber71StateAt 7 ∈ closeChainFiber mmWord mmFiber71DirectStates 2 [mmFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber71DirectStates 1 [mmFiber71StateAt 0]
      (mmFiber71StateAt 3) (mmFiber71StateAt 7) (by decide) h1 (by decide)
      mmFiber71ReverseSingleStep7
  change mmFiber71StateAt 7 ∈ closeChainFiber mmWord mmFiber71DirectStates (2 + 6) [mmFiber71StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber71DirectStates 2 6 [mmFiber71StateAt 0] (mmFiber71StateAt 7) h2

theorem mmFiber71DirectConnected :
    chainFiberConnected mmWord mmFiber71DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber71DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber71State0_in_close
  · subst state
    exact mmFiber71State1_in_close
  · subst state
    exact mmFiber71State2_in_close
  · subst state
    exact mmFiber71State3_in_close
  · subst state
    exact mmFiber71State4_in_close
  · subst state
    exact mmFiber71State5_in_close
  · subst state
    exact mmFiber71State6_in_close
  · subst state
    exact mmFiber71State7_in_close
  · cases h
def mmFiber74StateAt (i : Nat) : List TauState :=
  directStates (mmFiber74RowAt i).sourceLeft (mmFiber74RowAt i).sourceRight

def mmFiber74DirectStates : List (List TauState) :=
  [mmFiber74StateAt 0, mmFiber74StateAt 1, mmFiber74StateAt 2, mmFiber74StateAt 3, mmFiber74StateAt 4, mmFiber74StateAt 5, mmFiber74StateAt 6, mmFiber74StateAt 7]

theorem mmFiber74ReverseRow_1_ok :
    mmRowReverseValid mmFiber74Key mmFiber74Expected (mmFiber74RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber74Chunk0_ok
  change (mmRowReverseValid mmFiber74Key mmFiber74Expected (mmFiber74RowAt 0) &&
    mmRowReverseValid mmFiber74Key mmFiber74Expected (mmFiber74RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber74ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber74StateAt 0) (mmFiber74StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber74StateAt 0) (mmFiber74StateAt 1)
    (mmFiber74RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber74Key mmFiber74Expected
        (mmFiber74RowAt 1) (by decide) mmFiber74ReverseRow_1_ok
      simpa [mmFiber74StateAt, mmFiber74RowAt, mmFiber74Rows, listGetD, directRow] using h)

theorem mmFiber74ReverseRow_2_ok :
    mmRowReverseValid mmFiber74Key mmFiber74Expected (mmFiber74RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber74Chunk1_ok
  change (mmRowReverseValid mmFiber74Key mmFiber74Expected (mmFiber74RowAt 2) &&
    mmRowReverseValid mmFiber74Key mmFiber74Expected (mmFiber74RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber74ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber74StateAt 0) (mmFiber74StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber74StateAt 0) (mmFiber74StateAt 2)
    (mmFiber74RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber74Key mmFiber74Expected
        (mmFiber74RowAt 2) (by decide) mmFiber74ReverseRow_2_ok
      simpa [mmFiber74StateAt, mmFiber74RowAt, mmFiber74Rows, listGetD, directRow] using h)

theorem mmFiber74ReverseRow_3_ok :
    mmRowReverseValid mmFiber74Key mmFiber74Expected (mmFiber74RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber74Chunk1_ok
  change (mmRowReverseValid mmFiber74Key mmFiber74Expected (mmFiber74RowAt 2) &&
    mmRowReverseValid mmFiber74Key mmFiber74Expected (mmFiber74RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber74ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber74StateAt 1) (mmFiber74StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber74StateAt 1) (mmFiber74StateAt 3)
    (mmFiber74RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber74Key mmFiber74Expected
        (mmFiber74RowAt 3) (by decide) mmFiber74ReverseRow_3_ok
      simpa [mmFiber74StateAt, mmFiber74RowAt, mmFiber74Rows, listGetD, directRow] using h)

theorem mmFiber74ReverseRow_4_ok :
    mmRowReverseValid mmFiber74Key mmFiber74Expected (mmFiber74RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber74Chunk2_ok
  change (mmRowReverseValid mmFiber74Key mmFiber74Expected (mmFiber74RowAt 4) &&
    mmRowReverseValid mmFiber74Key mmFiber74Expected (mmFiber74RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber74ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber74StateAt 0) (mmFiber74StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber74StateAt 0) (mmFiber74StateAt 4)
    (mmFiber74RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber74Key mmFiber74Expected
        (mmFiber74RowAt 4) (by decide) mmFiber74ReverseRow_4_ok
      simpa [mmFiber74StateAt, mmFiber74RowAt, mmFiber74Rows, listGetD, directRow] using h)

theorem mmFiber74ReverseRow_5_ok :
    mmRowReverseValid mmFiber74Key mmFiber74Expected (mmFiber74RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber74Chunk2_ok
  change (mmRowReverseValid mmFiber74Key mmFiber74Expected (mmFiber74RowAt 4) &&
    mmRowReverseValid mmFiber74Key mmFiber74Expected (mmFiber74RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber74ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber74StateAt 1) (mmFiber74StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber74StateAt 1) (mmFiber74StateAt 5)
    (mmFiber74RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber74Key mmFiber74Expected
        (mmFiber74RowAt 5) (by decide) mmFiber74ReverseRow_5_ok
      simpa [mmFiber74StateAt, mmFiber74RowAt, mmFiber74Rows, listGetD, directRow] using h)

theorem mmFiber74ReverseRow_6_ok :
    mmRowReverseValid mmFiber74Key mmFiber74Expected (mmFiber74RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber74Chunk3_ok
  change (mmRowReverseValid mmFiber74Key mmFiber74Expected (mmFiber74RowAt 6) &&
    mmRowReverseValid mmFiber74Key mmFiber74Expected (mmFiber74RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber74ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber74StateAt 2) (mmFiber74StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber74StateAt 2) (mmFiber74StateAt 6)
    (mmFiber74RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber74Key mmFiber74Expected
        (mmFiber74RowAt 6) (by decide) mmFiber74ReverseRow_6_ok
      simpa [mmFiber74StateAt, mmFiber74RowAt, mmFiber74Rows, listGetD, directRow] using h)

theorem mmFiber74ReverseRow_7_ok :
    mmRowReverseValid mmFiber74Key mmFiber74Expected (mmFiber74RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber74Chunk3_ok
  change (mmRowReverseValid mmFiber74Key mmFiber74Expected (mmFiber74RowAt 6) &&
    mmRowReverseValid mmFiber74Key mmFiber74Expected (mmFiber74RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber74ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber74StateAt 3) (mmFiber74StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber74StateAt 3) (mmFiber74StateAt 7)
    (mmFiber74RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber74Key mmFiber74Expected
        (mmFiber74RowAt 7) (by decide) mmFiber74ReverseRow_7_ok
      simpa [mmFiber74StateAt, mmFiber74RowAt, mmFiber74Rows, listGetD, directRow] using h)

theorem mmFiber74State0_in_close :
    mmFiber74StateAt 0 ∈ closeChainFiber mmWord mmFiber74DirectStates mmFiber74DirectStates.length [mmFiber74StateAt 0] := by
  change mmFiber74StateAt 0 ∈ closeChainFiber mmWord mmFiber74DirectStates 8 [mmFiber74StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber74DirectStates 0 8 [mmFiber74StateAt 0] (mmFiber74StateAt 0) (by simp [closeChainFiber])

theorem mmFiber74State1_in_close :
    mmFiber74StateAt 1 ∈ closeChainFiber mmWord mmFiber74DirectStates mmFiber74DirectStates.length [mmFiber74StateAt 0] := by
  have h0 : mmFiber74StateAt 0 ∈ closeChainFiber mmWord mmFiber74DirectStates 0 [mmFiber74StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber74StateAt 1 ∈ closeChainFiber mmWord mmFiber74DirectStates 1 [mmFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber74DirectStates 0 [mmFiber74StateAt 0]
      (mmFiber74StateAt 0) (mmFiber74StateAt 1) (by decide) h0 (by decide)
      mmFiber74ReverseSingleStep1
  change mmFiber74StateAt 1 ∈ closeChainFiber mmWord mmFiber74DirectStates (1 + 7) [mmFiber74StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber74DirectStates 1 7 [mmFiber74StateAt 0] (mmFiber74StateAt 1) h1

theorem mmFiber74State2_in_close :
    mmFiber74StateAt 2 ∈ closeChainFiber mmWord mmFiber74DirectStates mmFiber74DirectStates.length [mmFiber74StateAt 0] := by
  have h0 : mmFiber74StateAt 0 ∈ closeChainFiber mmWord mmFiber74DirectStates 0 [mmFiber74StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber74StateAt 2 ∈ closeChainFiber mmWord mmFiber74DirectStates 1 [mmFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber74DirectStates 0 [mmFiber74StateAt 0]
      (mmFiber74StateAt 0) (mmFiber74StateAt 2) (by decide) h0 (by decide)
      mmFiber74ReverseSingleStep2
  change mmFiber74StateAt 2 ∈ closeChainFiber mmWord mmFiber74DirectStates (1 + 7) [mmFiber74StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber74DirectStates 1 7 [mmFiber74StateAt 0] (mmFiber74StateAt 2) h1

theorem mmFiber74State3_in_close :
    mmFiber74StateAt 3 ∈ closeChainFiber mmWord mmFiber74DirectStates mmFiber74DirectStates.length [mmFiber74StateAt 0] := by
  have h0 : mmFiber74StateAt 0 ∈ closeChainFiber mmWord mmFiber74DirectStates 0 [mmFiber74StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber74StateAt 1 ∈ closeChainFiber mmWord mmFiber74DirectStates 1 [mmFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber74DirectStates 0 [mmFiber74StateAt 0]
      (mmFiber74StateAt 0) (mmFiber74StateAt 1) (by decide) h0 (by decide)
      mmFiber74ReverseSingleStep1
  have h2 : mmFiber74StateAt 3 ∈ closeChainFiber mmWord mmFiber74DirectStates 2 [mmFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber74DirectStates 1 [mmFiber74StateAt 0]
      (mmFiber74StateAt 1) (mmFiber74StateAt 3) (by decide) h1 (by decide)
      mmFiber74ReverseSingleStep3
  change mmFiber74StateAt 3 ∈ closeChainFiber mmWord mmFiber74DirectStates (2 + 6) [mmFiber74StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber74DirectStates 2 6 [mmFiber74StateAt 0] (mmFiber74StateAt 3) h2

theorem mmFiber74State4_in_close :
    mmFiber74StateAt 4 ∈ closeChainFiber mmWord mmFiber74DirectStates mmFiber74DirectStates.length [mmFiber74StateAt 0] := by
  have h0 : mmFiber74StateAt 0 ∈ closeChainFiber mmWord mmFiber74DirectStates 0 [mmFiber74StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber74StateAt 4 ∈ closeChainFiber mmWord mmFiber74DirectStates 1 [mmFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber74DirectStates 0 [mmFiber74StateAt 0]
      (mmFiber74StateAt 0) (mmFiber74StateAt 4) (by decide) h0 (by decide)
      mmFiber74ReverseSingleStep4
  change mmFiber74StateAt 4 ∈ closeChainFiber mmWord mmFiber74DirectStates (1 + 7) [mmFiber74StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber74DirectStates 1 7 [mmFiber74StateAt 0] (mmFiber74StateAt 4) h1

theorem mmFiber74State5_in_close :
    mmFiber74StateAt 5 ∈ closeChainFiber mmWord mmFiber74DirectStates mmFiber74DirectStates.length [mmFiber74StateAt 0] := by
  have h0 : mmFiber74StateAt 0 ∈ closeChainFiber mmWord mmFiber74DirectStates 0 [mmFiber74StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber74StateAt 1 ∈ closeChainFiber mmWord mmFiber74DirectStates 1 [mmFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber74DirectStates 0 [mmFiber74StateAt 0]
      (mmFiber74StateAt 0) (mmFiber74StateAt 1) (by decide) h0 (by decide)
      mmFiber74ReverseSingleStep1
  have h2 : mmFiber74StateAt 5 ∈ closeChainFiber mmWord mmFiber74DirectStates 2 [mmFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber74DirectStates 1 [mmFiber74StateAt 0]
      (mmFiber74StateAt 1) (mmFiber74StateAt 5) (by decide) h1 (by decide)
      mmFiber74ReverseSingleStep5
  change mmFiber74StateAt 5 ∈ closeChainFiber mmWord mmFiber74DirectStates (2 + 6) [mmFiber74StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber74DirectStates 2 6 [mmFiber74StateAt 0] (mmFiber74StateAt 5) h2

theorem mmFiber74State6_in_close :
    mmFiber74StateAt 6 ∈ closeChainFiber mmWord mmFiber74DirectStates mmFiber74DirectStates.length [mmFiber74StateAt 0] := by
  have h0 : mmFiber74StateAt 0 ∈ closeChainFiber mmWord mmFiber74DirectStates 0 [mmFiber74StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber74StateAt 2 ∈ closeChainFiber mmWord mmFiber74DirectStates 1 [mmFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber74DirectStates 0 [mmFiber74StateAt 0]
      (mmFiber74StateAt 0) (mmFiber74StateAt 2) (by decide) h0 (by decide)
      mmFiber74ReverseSingleStep2
  have h2 : mmFiber74StateAt 6 ∈ closeChainFiber mmWord mmFiber74DirectStates 2 [mmFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber74DirectStates 1 [mmFiber74StateAt 0]
      (mmFiber74StateAt 2) (mmFiber74StateAt 6) (by decide) h1 (by decide)
      mmFiber74ReverseSingleStep6
  change mmFiber74StateAt 6 ∈ closeChainFiber mmWord mmFiber74DirectStates (2 + 6) [mmFiber74StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber74DirectStates 2 6 [mmFiber74StateAt 0] (mmFiber74StateAt 6) h2

theorem mmFiber74State7_in_close :
    mmFiber74StateAt 7 ∈ closeChainFiber mmWord mmFiber74DirectStates mmFiber74DirectStates.length [mmFiber74StateAt 0] := by
  have h0 : mmFiber74StateAt 0 ∈ closeChainFiber mmWord mmFiber74DirectStates 0 [mmFiber74StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber74StateAt 1 ∈ closeChainFiber mmWord mmFiber74DirectStates 1 [mmFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber74DirectStates 0 [mmFiber74StateAt 0]
      (mmFiber74StateAt 0) (mmFiber74StateAt 1) (by decide) h0 (by decide)
      mmFiber74ReverseSingleStep1
  have h2 : mmFiber74StateAt 3 ∈ closeChainFiber mmWord mmFiber74DirectStates 2 [mmFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber74DirectStates 1 [mmFiber74StateAt 0]
      (mmFiber74StateAt 1) (mmFiber74StateAt 3) (by decide) h1 (by decide)
      mmFiber74ReverseSingleStep3
  have h3 : mmFiber74StateAt 7 ∈ closeChainFiber mmWord mmFiber74DirectStates 3 [mmFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber74DirectStates 2 [mmFiber74StateAt 0]
      (mmFiber74StateAt 3) (mmFiber74StateAt 7) (by decide) h2 (by decide)
      mmFiber74ReverseSingleStep7
  change mmFiber74StateAt 7 ∈ closeChainFiber mmWord mmFiber74DirectStates (3 + 5) [mmFiber74StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber74DirectStates 3 5 [mmFiber74StateAt 0] (mmFiber74StateAt 7) h3

theorem mmFiber74DirectConnected :
    chainFiberConnected mmWord mmFiber74DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber74DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber74State0_in_close
  · subst state
    exact mmFiber74State1_in_close
  · subst state
    exact mmFiber74State2_in_close
  · subst state
    exact mmFiber74State3_in_close
  · subst state
    exact mmFiber74State4_in_close
  · subst state
    exact mmFiber74State5_in_close
  · subst state
    exact mmFiber74State6_in_close
  · subst state
    exact mmFiber74State7_in_close
  · cases h
def mmFiber77StateAt (i : Nat) : List TauState :=
  directStates (mmFiber77RowAt i).sourceLeft (mmFiber77RowAt i).sourceRight

def mmFiber77DirectStates : List (List TauState) :=
  [mmFiber77StateAt 0, mmFiber77StateAt 1, mmFiber77StateAt 2, mmFiber77StateAt 3, mmFiber77StateAt 4, mmFiber77StateAt 5, mmFiber77StateAt 6, mmFiber77StateAt 7]

theorem mmFiber77ReverseRow_1_ok :
    mmRowReverseValid mmFiber77Key mmFiber77Expected (mmFiber77RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber77Chunk0_ok
  change (mmRowReverseValid mmFiber77Key mmFiber77Expected (mmFiber77RowAt 0) &&
    mmRowReverseValid mmFiber77Key mmFiber77Expected (mmFiber77RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber77ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber77StateAt 0) (mmFiber77StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber77StateAt 0) (mmFiber77StateAt 1)
    (mmFiber77RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber77Key mmFiber77Expected
        (mmFiber77RowAt 1) (by decide) mmFiber77ReverseRow_1_ok
      simpa [mmFiber77StateAt, mmFiber77RowAt, mmFiber77Rows, listGetD, directRow] using h)

theorem mmFiber77ReverseRow_2_ok :
    mmRowReverseValid mmFiber77Key mmFiber77Expected (mmFiber77RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber77Chunk1_ok
  change (mmRowReverseValid mmFiber77Key mmFiber77Expected (mmFiber77RowAt 2) &&
    mmRowReverseValid mmFiber77Key mmFiber77Expected (mmFiber77RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber77ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber77StateAt 1) (mmFiber77StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber77StateAt 1) (mmFiber77StateAt 2)
    (mmFiber77RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber77Key mmFiber77Expected
        (mmFiber77RowAt 2) (by decide) mmFiber77ReverseRow_2_ok
      simpa [mmFiber77StateAt, mmFiber77RowAt, mmFiber77Rows, listGetD, directRow] using h)

theorem mmFiber77ReverseRow_3_ok :
    mmRowReverseValid mmFiber77Key mmFiber77Expected (mmFiber77RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber77Chunk1_ok
  change (mmRowReverseValid mmFiber77Key mmFiber77Expected (mmFiber77RowAt 2) &&
    mmRowReverseValid mmFiber77Key mmFiber77Expected (mmFiber77RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber77ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber77StateAt 0) (mmFiber77StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber77StateAt 0) (mmFiber77StateAt 3)
    (mmFiber77RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber77Key mmFiber77Expected
        (mmFiber77RowAt 3) (by decide) mmFiber77ReverseRow_3_ok
      simpa [mmFiber77StateAt, mmFiber77RowAt, mmFiber77Rows, listGetD, directRow] using h)

theorem mmFiber77ReverseRow_4_ok :
    mmRowReverseValid mmFiber77Key mmFiber77Expected (mmFiber77RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber77Chunk2_ok
  change (mmRowReverseValid mmFiber77Key mmFiber77Expected (mmFiber77RowAt 4) &&
    mmRowReverseValid mmFiber77Key mmFiber77Expected (mmFiber77RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber77ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber77StateAt 0) (mmFiber77StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber77StateAt 0) (mmFiber77StateAt 4)
    (mmFiber77RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber77Key mmFiber77Expected
        (mmFiber77RowAt 4) (by decide) mmFiber77ReverseRow_4_ok
      simpa [mmFiber77StateAt, mmFiber77RowAt, mmFiber77Rows, listGetD, directRow] using h)

theorem mmFiber77ReverseRow_5_ok :
    mmRowReverseValid mmFiber77Key mmFiber77Expected (mmFiber77RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber77Chunk2_ok
  change (mmRowReverseValid mmFiber77Key mmFiber77Expected (mmFiber77RowAt 4) &&
    mmRowReverseValid mmFiber77Key mmFiber77Expected (mmFiber77RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber77ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber77StateAt 1) (mmFiber77StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber77StateAt 1) (mmFiber77StateAt 5)
    (mmFiber77RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber77Key mmFiber77Expected
        (mmFiber77RowAt 5) (by decide) mmFiber77ReverseRow_5_ok
      simpa [mmFiber77StateAt, mmFiber77RowAt, mmFiber77Rows, listGetD, directRow] using h)

theorem mmFiber77ReverseRow_6_ok :
    mmRowReverseValid mmFiber77Key mmFiber77Expected (mmFiber77RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber77Chunk3_ok
  change (mmRowReverseValid mmFiber77Key mmFiber77Expected (mmFiber77RowAt 6) &&
    mmRowReverseValid mmFiber77Key mmFiber77Expected (mmFiber77RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber77ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber77StateAt 2) (mmFiber77StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber77StateAt 2) (mmFiber77StateAt 6)
    (mmFiber77RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber77Key mmFiber77Expected
        (mmFiber77RowAt 6) (by decide) mmFiber77ReverseRow_6_ok
      simpa [mmFiber77StateAt, mmFiber77RowAt, mmFiber77Rows, listGetD, directRow] using h)

theorem mmFiber77ReverseRow_7_ok :
    mmRowReverseValid mmFiber77Key mmFiber77Expected (mmFiber77RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber77Chunk3_ok
  change (mmRowReverseValid mmFiber77Key mmFiber77Expected (mmFiber77RowAt 6) &&
    mmRowReverseValid mmFiber77Key mmFiber77Expected (mmFiber77RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber77ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber77StateAt 3) (mmFiber77StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber77StateAt 3) (mmFiber77StateAt 7)
    (mmFiber77RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber77Key mmFiber77Expected
        (mmFiber77RowAt 7) (by decide) mmFiber77ReverseRow_7_ok
      simpa [mmFiber77StateAt, mmFiber77RowAt, mmFiber77Rows, listGetD, directRow] using h)

theorem mmFiber77State0_in_close :
    mmFiber77StateAt 0 ∈ closeChainFiber mmWord mmFiber77DirectStates mmFiber77DirectStates.length [mmFiber77StateAt 0] := by
  change mmFiber77StateAt 0 ∈ closeChainFiber mmWord mmFiber77DirectStates 8 [mmFiber77StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber77DirectStates 0 8 [mmFiber77StateAt 0] (mmFiber77StateAt 0) (by simp [closeChainFiber])

theorem mmFiber77State1_in_close :
    mmFiber77StateAt 1 ∈ closeChainFiber mmWord mmFiber77DirectStates mmFiber77DirectStates.length [mmFiber77StateAt 0] := by
  have h0 : mmFiber77StateAt 0 ∈ closeChainFiber mmWord mmFiber77DirectStates 0 [mmFiber77StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber77StateAt 1 ∈ closeChainFiber mmWord mmFiber77DirectStates 1 [mmFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber77DirectStates 0 [mmFiber77StateAt 0]
      (mmFiber77StateAt 0) (mmFiber77StateAt 1) (by decide) h0 (by decide)
      mmFiber77ReverseSingleStep1
  change mmFiber77StateAt 1 ∈ closeChainFiber mmWord mmFiber77DirectStates (1 + 7) [mmFiber77StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber77DirectStates 1 7 [mmFiber77StateAt 0] (mmFiber77StateAt 1) h1

theorem mmFiber77State2_in_close :
    mmFiber77StateAt 2 ∈ closeChainFiber mmWord mmFiber77DirectStates mmFiber77DirectStates.length [mmFiber77StateAt 0] := by
  have h0 : mmFiber77StateAt 0 ∈ closeChainFiber mmWord mmFiber77DirectStates 0 [mmFiber77StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber77StateAt 1 ∈ closeChainFiber mmWord mmFiber77DirectStates 1 [mmFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber77DirectStates 0 [mmFiber77StateAt 0]
      (mmFiber77StateAt 0) (mmFiber77StateAt 1) (by decide) h0 (by decide)
      mmFiber77ReverseSingleStep1
  have h2 : mmFiber77StateAt 2 ∈ closeChainFiber mmWord mmFiber77DirectStates 2 [mmFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber77DirectStates 1 [mmFiber77StateAt 0]
      (mmFiber77StateAt 1) (mmFiber77StateAt 2) (by decide) h1 (by decide)
      mmFiber77ReverseSingleStep2
  change mmFiber77StateAt 2 ∈ closeChainFiber mmWord mmFiber77DirectStates (2 + 6) [mmFiber77StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber77DirectStates 2 6 [mmFiber77StateAt 0] (mmFiber77StateAt 2) h2

theorem mmFiber77State3_in_close :
    mmFiber77StateAt 3 ∈ closeChainFiber mmWord mmFiber77DirectStates mmFiber77DirectStates.length [mmFiber77StateAt 0] := by
  have h0 : mmFiber77StateAt 0 ∈ closeChainFiber mmWord mmFiber77DirectStates 0 [mmFiber77StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber77StateAt 3 ∈ closeChainFiber mmWord mmFiber77DirectStates 1 [mmFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber77DirectStates 0 [mmFiber77StateAt 0]
      (mmFiber77StateAt 0) (mmFiber77StateAt 3) (by decide) h0 (by decide)
      mmFiber77ReverseSingleStep3
  change mmFiber77StateAt 3 ∈ closeChainFiber mmWord mmFiber77DirectStates (1 + 7) [mmFiber77StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber77DirectStates 1 7 [mmFiber77StateAt 0] (mmFiber77StateAt 3) h1

theorem mmFiber77State4_in_close :
    mmFiber77StateAt 4 ∈ closeChainFiber mmWord mmFiber77DirectStates mmFiber77DirectStates.length [mmFiber77StateAt 0] := by
  have h0 : mmFiber77StateAt 0 ∈ closeChainFiber mmWord mmFiber77DirectStates 0 [mmFiber77StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber77StateAt 4 ∈ closeChainFiber mmWord mmFiber77DirectStates 1 [mmFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber77DirectStates 0 [mmFiber77StateAt 0]
      (mmFiber77StateAt 0) (mmFiber77StateAt 4) (by decide) h0 (by decide)
      mmFiber77ReverseSingleStep4
  change mmFiber77StateAt 4 ∈ closeChainFiber mmWord mmFiber77DirectStates (1 + 7) [mmFiber77StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber77DirectStates 1 7 [mmFiber77StateAt 0] (mmFiber77StateAt 4) h1

theorem mmFiber77State5_in_close :
    mmFiber77StateAt 5 ∈ closeChainFiber mmWord mmFiber77DirectStates mmFiber77DirectStates.length [mmFiber77StateAt 0] := by
  have h0 : mmFiber77StateAt 0 ∈ closeChainFiber mmWord mmFiber77DirectStates 0 [mmFiber77StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber77StateAt 1 ∈ closeChainFiber mmWord mmFiber77DirectStates 1 [mmFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber77DirectStates 0 [mmFiber77StateAt 0]
      (mmFiber77StateAt 0) (mmFiber77StateAt 1) (by decide) h0 (by decide)
      mmFiber77ReverseSingleStep1
  have h2 : mmFiber77StateAt 5 ∈ closeChainFiber mmWord mmFiber77DirectStates 2 [mmFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber77DirectStates 1 [mmFiber77StateAt 0]
      (mmFiber77StateAt 1) (mmFiber77StateAt 5) (by decide) h1 (by decide)
      mmFiber77ReverseSingleStep5
  change mmFiber77StateAt 5 ∈ closeChainFiber mmWord mmFiber77DirectStates (2 + 6) [mmFiber77StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber77DirectStates 2 6 [mmFiber77StateAt 0] (mmFiber77StateAt 5) h2

theorem mmFiber77State6_in_close :
    mmFiber77StateAt 6 ∈ closeChainFiber mmWord mmFiber77DirectStates mmFiber77DirectStates.length [mmFiber77StateAt 0] := by
  have h0 : mmFiber77StateAt 0 ∈ closeChainFiber mmWord mmFiber77DirectStates 0 [mmFiber77StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber77StateAt 1 ∈ closeChainFiber mmWord mmFiber77DirectStates 1 [mmFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber77DirectStates 0 [mmFiber77StateAt 0]
      (mmFiber77StateAt 0) (mmFiber77StateAt 1) (by decide) h0 (by decide)
      mmFiber77ReverseSingleStep1
  have h2 : mmFiber77StateAt 2 ∈ closeChainFiber mmWord mmFiber77DirectStates 2 [mmFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber77DirectStates 1 [mmFiber77StateAt 0]
      (mmFiber77StateAt 1) (mmFiber77StateAt 2) (by decide) h1 (by decide)
      mmFiber77ReverseSingleStep2
  have h3 : mmFiber77StateAt 6 ∈ closeChainFiber mmWord mmFiber77DirectStates 3 [mmFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber77DirectStates 2 [mmFiber77StateAt 0]
      (mmFiber77StateAt 2) (mmFiber77StateAt 6) (by decide) h2 (by decide)
      mmFiber77ReverseSingleStep6
  change mmFiber77StateAt 6 ∈ closeChainFiber mmWord mmFiber77DirectStates (3 + 5) [mmFiber77StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber77DirectStates 3 5 [mmFiber77StateAt 0] (mmFiber77StateAt 6) h3

theorem mmFiber77State7_in_close :
    mmFiber77StateAt 7 ∈ closeChainFiber mmWord mmFiber77DirectStates mmFiber77DirectStates.length [mmFiber77StateAt 0] := by
  have h0 : mmFiber77StateAt 0 ∈ closeChainFiber mmWord mmFiber77DirectStates 0 [mmFiber77StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber77StateAt 3 ∈ closeChainFiber mmWord mmFiber77DirectStates 1 [mmFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber77DirectStates 0 [mmFiber77StateAt 0]
      (mmFiber77StateAt 0) (mmFiber77StateAt 3) (by decide) h0 (by decide)
      mmFiber77ReverseSingleStep3
  have h2 : mmFiber77StateAt 7 ∈ closeChainFiber mmWord mmFiber77DirectStates 2 [mmFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber77DirectStates 1 [mmFiber77StateAt 0]
      (mmFiber77StateAt 3) (mmFiber77StateAt 7) (by decide) h1 (by decide)
      mmFiber77ReverseSingleStep7
  change mmFiber77StateAt 7 ∈ closeChainFiber mmWord mmFiber77DirectStates (2 + 6) [mmFiber77StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber77DirectStates 2 6 [mmFiber77StateAt 0] (mmFiber77StateAt 7) h2

theorem mmFiber77DirectConnected :
    chainFiberConnected mmWord mmFiber77DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber77DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber77State0_in_close
  · subst state
    exact mmFiber77State1_in_close
  · subst state
    exact mmFiber77State2_in_close
  · subst state
    exact mmFiber77State3_in_close
  · subst state
    exact mmFiber77State4_in_close
  · subst state
    exact mmFiber77State5_in_close
  · subst state
    exact mmFiber77State6_in_close
  · subst state
    exact mmFiber77State7_in_close
  · cases h
end GoertzelLemma818LengthTwoMMBridge

end Mettapedia.GraphTheory.FourColor
