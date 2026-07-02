import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for size-8 `mirror,mirror` length-two fibers, group 4

This module proves direct connectedness for generated `mirror,mirror` size-8 fibers from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMMBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorMirrorCertificate
open GoertzelLemma818MirrorMirrorReverseAudit

def mmFiber57StateAt (i : Nat) : List TauState :=
  directStates (mmFiber57RowAt i).sourceLeft (mmFiber57RowAt i).sourceRight

def mmFiber57DirectStates : List (List TauState) :=
  [mmFiber57StateAt 0, mmFiber57StateAt 1, mmFiber57StateAt 2, mmFiber57StateAt 3, mmFiber57StateAt 4, mmFiber57StateAt 5, mmFiber57StateAt 6, mmFiber57StateAt 7]

theorem mmFiber57ReverseRow_1_ok :
    mmRowReverseValid mmFiber57Key mmFiber57Expected (mmFiber57RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber57Chunk0_ok
  change (mmRowReverseValid mmFiber57Key mmFiber57Expected (mmFiber57RowAt 0) &&
    mmRowReverseValid mmFiber57Key mmFiber57Expected (mmFiber57RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber57ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber57StateAt 0) (mmFiber57StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber57StateAt 0) (mmFiber57StateAt 1)
    (mmFiber57RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber57Key mmFiber57Expected
        (mmFiber57RowAt 1) (by decide) mmFiber57ReverseRow_1_ok
      simpa [mmFiber57StateAt, mmFiber57RowAt, mmFiber57Rows, listGetD, directRow] using h)

theorem mmFiber57ReverseRow_2_ok :
    mmRowReverseValid mmFiber57Key mmFiber57Expected (mmFiber57RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber57Chunk1_ok
  change (mmRowReverseValid mmFiber57Key mmFiber57Expected (mmFiber57RowAt 2) &&
    mmRowReverseValid mmFiber57Key mmFiber57Expected (mmFiber57RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber57ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber57StateAt 1) (mmFiber57StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber57StateAt 1) (mmFiber57StateAt 2)
    (mmFiber57RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber57Key mmFiber57Expected
        (mmFiber57RowAt 2) (by decide) mmFiber57ReverseRow_2_ok
      simpa [mmFiber57StateAt, mmFiber57RowAt, mmFiber57Rows, listGetD, directRow] using h)

theorem mmFiber57ReverseRow_3_ok :
    mmRowReverseValid mmFiber57Key mmFiber57Expected (mmFiber57RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber57Chunk1_ok
  change (mmRowReverseValid mmFiber57Key mmFiber57Expected (mmFiber57RowAt 2) &&
    mmRowReverseValid mmFiber57Key mmFiber57Expected (mmFiber57RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber57ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber57StateAt 0) (mmFiber57StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber57StateAt 0) (mmFiber57StateAt 3)
    (mmFiber57RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber57Key mmFiber57Expected
        (mmFiber57RowAt 3) (by decide) mmFiber57ReverseRow_3_ok
      simpa [mmFiber57StateAt, mmFiber57RowAt, mmFiber57Rows, listGetD, directRow] using h)

theorem mmFiber57ReverseRow_4_ok :
    mmRowReverseValid mmFiber57Key mmFiber57Expected (mmFiber57RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber57Chunk2_ok
  change (mmRowReverseValid mmFiber57Key mmFiber57Expected (mmFiber57RowAt 4) &&
    mmRowReverseValid mmFiber57Key mmFiber57Expected (mmFiber57RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber57ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber57StateAt 0) (mmFiber57StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber57StateAt 0) (mmFiber57StateAt 4)
    (mmFiber57RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber57Key mmFiber57Expected
        (mmFiber57RowAt 4) (by decide) mmFiber57ReverseRow_4_ok
      simpa [mmFiber57StateAt, mmFiber57RowAt, mmFiber57Rows, listGetD, directRow] using h)

theorem mmFiber57ReverseRow_5_ok :
    mmRowReverseValid mmFiber57Key mmFiber57Expected (mmFiber57RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber57Chunk2_ok
  change (mmRowReverseValid mmFiber57Key mmFiber57Expected (mmFiber57RowAt 4) &&
    mmRowReverseValid mmFiber57Key mmFiber57Expected (mmFiber57RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber57ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber57StateAt 1) (mmFiber57StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber57StateAt 1) (mmFiber57StateAt 5)
    (mmFiber57RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber57Key mmFiber57Expected
        (mmFiber57RowAt 5) (by decide) mmFiber57ReverseRow_5_ok
      simpa [mmFiber57StateAt, mmFiber57RowAt, mmFiber57Rows, listGetD, directRow] using h)

theorem mmFiber57ReverseRow_6_ok :
    mmRowReverseValid mmFiber57Key mmFiber57Expected (mmFiber57RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber57Chunk3_ok
  change (mmRowReverseValid mmFiber57Key mmFiber57Expected (mmFiber57RowAt 6) &&
    mmRowReverseValid mmFiber57Key mmFiber57Expected (mmFiber57RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber57ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber57StateAt 2) (mmFiber57StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber57StateAt 2) (mmFiber57StateAt 6)
    (mmFiber57RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber57Key mmFiber57Expected
        (mmFiber57RowAt 6) (by decide) mmFiber57ReverseRow_6_ok
      simpa [mmFiber57StateAt, mmFiber57RowAt, mmFiber57Rows, listGetD, directRow] using h)

theorem mmFiber57ReverseRow_7_ok :
    mmRowReverseValid mmFiber57Key mmFiber57Expected (mmFiber57RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber57Chunk3_ok
  change (mmRowReverseValid mmFiber57Key mmFiber57Expected (mmFiber57RowAt 6) &&
    mmRowReverseValid mmFiber57Key mmFiber57Expected (mmFiber57RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber57ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber57StateAt 3) (mmFiber57StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber57StateAt 3) (mmFiber57StateAt 7)
    (mmFiber57RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber57Key mmFiber57Expected
        (mmFiber57RowAt 7) (by decide) mmFiber57ReverseRow_7_ok
      simpa [mmFiber57StateAt, mmFiber57RowAt, mmFiber57Rows, listGetD, directRow] using h)

theorem mmFiber57State0_in_close :
    mmFiber57StateAt 0 ∈ closeChainFiber mmWord mmFiber57DirectStates mmFiber57DirectStates.length [mmFiber57StateAt 0] := by
  change mmFiber57StateAt 0 ∈ closeChainFiber mmWord mmFiber57DirectStates 8 [mmFiber57StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber57DirectStates 0 8 [mmFiber57StateAt 0] (mmFiber57StateAt 0) (by simp [closeChainFiber])

theorem mmFiber57State1_in_close :
    mmFiber57StateAt 1 ∈ closeChainFiber mmWord mmFiber57DirectStates mmFiber57DirectStates.length [mmFiber57StateAt 0] := by
  have h0 : mmFiber57StateAt 0 ∈ closeChainFiber mmWord mmFiber57DirectStates 0 [mmFiber57StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber57StateAt 1 ∈ closeChainFiber mmWord mmFiber57DirectStates 1 [mmFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber57DirectStates 0 [mmFiber57StateAt 0]
      (mmFiber57StateAt 0) (mmFiber57StateAt 1) (by decide) h0 (by decide)
      mmFiber57ReverseSingleStep1
  change mmFiber57StateAt 1 ∈ closeChainFiber mmWord mmFiber57DirectStates (1 + 7) [mmFiber57StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber57DirectStates 1 7 [mmFiber57StateAt 0] (mmFiber57StateAt 1) h1

theorem mmFiber57State2_in_close :
    mmFiber57StateAt 2 ∈ closeChainFiber mmWord mmFiber57DirectStates mmFiber57DirectStates.length [mmFiber57StateAt 0] := by
  have h0 : mmFiber57StateAt 0 ∈ closeChainFiber mmWord mmFiber57DirectStates 0 [mmFiber57StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber57StateAt 1 ∈ closeChainFiber mmWord mmFiber57DirectStates 1 [mmFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber57DirectStates 0 [mmFiber57StateAt 0]
      (mmFiber57StateAt 0) (mmFiber57StateAt 1) (by decide) h0 (by decide)
      mmFiber57ReverseSingleStep1
  have h2 : mmFiber57StateAt 2 ∈ closeChainFiber mmWord mmFiber57DirectStates 2 [mmFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber57DirectStates 1 [mmFiber57StateAt 0]
      (mmFiber57StateAt 1) (mmFiber57StateAt 2) (by decide) h1 (by decide)
      mmFiber57ReverseSingleStep2
  change mmFiber57StateAt 2 ∈ closeChainFiber mmWord mmFiber57DirectStates (2 + 6) [mmFiber57StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber57DirectStates 2 6 [mmFiber57StateAt 0] (mmFiber57StateAt 2) h2

theorem mmFiber57State3_in_close :
    mmFiber57StateAt 3 ∈ closeChainFiber mmWord mmFiber57DirectStates mmFiber57DirectStates.length [mmFiber57StateAt 0] := by
  have h0 : mmFiber57StateAt 0 ∈ closeChainFiber mmWord mmFiber57DirectStates 0 [mmFiber57StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber57StateAt 3 ∈ closeChainFiber mmWord mmFiber57DirectStates 1 [mmFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber57DirectStates 0 [mmFiber57StateAt 0]
      (mmFiber57StateAt 0) (mmFiber57StateAt 3) (by decide) h0 (by decide)
      mmFiber57ReverseSingleStep3
  change mmFiber57StateAt 3 ∈ closeChainFiber mmWord mmFiber57DirectStates (1 + 7) [mmFiber57StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber57DirectStates 1 7 [mmFiber57StateAt 0] (mmFiber57StateAt 3) h1

theorem mmFiber57State4_in_close :
    mmFiber57StateAt 4 ∈ closeChainFiber mmWord mmFiber57DirectStates mmFiber57DirectStates.length [mmFiber57StateAt 0] := by
  have h0 : mmFiber57StateAt 0 ∈ closeChainFiber mmWord mmFiber57DirectStates 0 [mmFiber57StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber57StateAt 4 ∈ closeChainFiber mmWord mmFiber57DirectStates 1 [mmFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber57DirectStates 0 [mmFiber57StateAt 0]
      (mmFiber57StateAt 0) (mmFiber57StateAt 4) (by decide) h0 (by decide)
      mmFiber57ReverseSingleStep4
  change mmFiber57StateAt 4 ∈ closeChainFiber mmWord mmFiber57DirectStates (1 + 7) [mmFiber57StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber57DirectStates 1 7 [mmFiber57StateAt 0] (mmFiber57StateAt 4) h1

theorem mmFiber57State5_in_close :
    mmFiber57StateAt 5 ∈ closeChainFiber mmWord mmFiber57DirectStates mmFiber57DirectStates.length [mmFiber57StateAt 0] := by
  have h0 : mmFiber57StateAt 0 ∈ closeChainFiber mmWord mmFiber57DirectStates 0 [mmFiber57StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber57StateAt 1 ∈ closeChainFiber mmWord mmFiber57DirectStates 1 [mmFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber57DirectStates 0 [mmFiber57StateAt 0]
      (mmFiber57StateAt 0) (mmFiber57StateAt 1) (by decide) h0 (by decide)
      mmFiber57ReverseSingleStep1
  have h2 : mmFiber57StateAt 5 ∈ closeChainFiber mmWord mmFiber57DirectStates 2 [mmFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber57DirectStates 1 [mmFiber57StateAt 0]
      (mmFiber57StateAt 1) (mmFiber57StateAt 5) (by decide) h1 (by decide)
      mmFiber57ReverseSingleStep5
  change mmFiber57StateAt 5 ∈ closeChainFiber mmWord mmFiber57DirectStates (2 + 6) [mmFiber57StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber57DirectStates 2 6 [mmFiber57StateAt 0] (mmFiber57StateAt 5) h2

theorem mmFiber57State6_in_close :
    mmFiber57StateAt 6 ∈ closeChainFiber mmWord mmFiber57DirectStates mmFiber57DirectStates.length [mmFiber57StateAt 0] := by
  have h0 : mmFiber57StateAt 0 ∈ closeChainFiber mmWord mmFiber57DirectStates 0 [mmFiber57StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber57StateAt 1 ∈ closeChainFiber mmWord mmFiber57DirectStates 1 [mmFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber57DirectStates 0 [mmFiber57StateAt 0]
      (mmFiber57StateAt 0) (mmFiber57StateAt 1) (by decide) h0 (by decide)
      mmFiber57ReverseSingleStep1
  have h2 : mmFiber57StateAt 2 ∈ closeChainFiber mmWord mmFiber57DirectStates 2 [mmFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber57DirectStates 1 [mmFiber57StateAt 0]
      (mmFiber57StateAt 1) (mmFiber57StateAt 2) (by decide) h1 (by decide)
      mmFiber57ReverseSingleStep2
  have h3 : mmFiber57StateAt 6 ∈ closeChainFiber mmWord mmFiber57DirectStates 3 [mmFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber57DirectStates 2 [mmFiber57StateAt 0]
      (mmFiber57StateAt 2) (mmFiber57StateAt 6) (by decide) h2 (by decide)
      mmFiber57ReverseSingleStep6
  change mmFiber57StateAt 6 ∈ closeChainFiber mmWord mmFiber57DirectStates (3 + 5) [mmFiber57StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber57DirectStates 3 5 [mmFiber57StateAt 0] (mmFiber57StateAt 6) h3

theorem mmFiber57State7_in_close :
    mmFiber57StateAt 7 ∈ closeChainFiber mmWord mmFiber57DirectStates mmFiber57DirectStates.length [mmFiber57StateAt 0] := by
  have h0 : mmFiber57StateAt 0 ∈ closeChainFiber mmWord mmFiber57DirectStates 0 [mmFiber57StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber57StateAt 3 ∈ closeChainFiber mmWord mmFiber57DirectStates 1 [mmFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber57DirectStates 0 [mmFiber57StateAt 0]
      (mmFiber57StateAt 0) (mmFiber57StateAt 3) (by decide) h0 (by decide)
      mmFiber57ReverseSingleStep3
  have h2 : mmFiber57StateAt 7 ∈ closeChainFiber mmWord mmFiber57DirectStates 2 [mmFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber57DirectStates 1 [mmFiber57StateAt 0]
      (mmFiber57StateAt 3) (mmFiber57StateAt 7) (by decide) h1 (by decide)
      mmFiber57ReverseSingleStep7
  change mmFiber57StateAt 7 ∈ closeChainFiber mmWord mmFiber57DirectStates (2 + 6) [mmFiber57StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber57DirectStates 2 6 [mmFiber57StateAt 0] (mmFiber57StateAt 7) h2

theorem mmFiber57DirectConnected :
    chainFiberConnected mmWord mmFiber57DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber57DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber57State0_in_close
  · subst state
    exact mmFiber57State1_in_close
  · subst state
    exact mmFiber57State2_in_close
  · subst state
    exact mmFiber57State3_in_close
  · subst state
    exact mmFiber57State4_in_close
  · subst state
    exact mmFiber57State5_in_close
  · subst state
    exact mmFiber57State6_in_close
  · subst state
    exact mmFiber57State7_in_close
  · cases h
def mmFiber58StateAt (i : Nat) : List TauState :=
  directStates (mmFiber58RowAt i).sourceLeft (mmFiber58RowAt i).sourceRight

def mmFiber58DirectStates : List (List TauState) :=
  [mmFiber58StateAt 0, mmFiber58StateAt 1, mmFiber58StateAt 2, mmFiber58StateAt 3, mmFiber58StateAt 4, mmFiber58StateAt 5, mmFiber58StateAt 6, mmFiber58StateAt 7]

theorem mmFiber58ReverseRow_1_ok :
    mmRowReverseValid mmFiber58Key mmFiber58Expected (mmFiber58RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber58Chunk0_ok
  change (mmRowReverseValid mmFiber58Key mmFiber58Expected (mmFiber58RowAt 0) &&
    mmRowReverseValid mmFiber58Key mmFiber58Expected (mmFiber58RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber58ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber58StateAt 0) (mmFiber58StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber58StateAt 0) (mmFiber58StateAt 1)
    (mmFiber58RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber58Key mmFiber58Expected
        (mmFiber58RowAt 1) (by decide) mmFiber58ReverseRow_1_ok
      simpa [mmFiber58StateAt, mmFiber58RowAt, mmFiber58Rows, listGetD, directRow] using h)

theorem mmFiber58ReverseRow_2_ok :
    mmRowReverseValid mmFiber58Key mmFiber58Expected (mmFiber58RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber58Chunk1_ok
  change (mmRowReverseValid mmFiber58Key mmFiber58Expected (mmFiber58RowAt 2) &&
    mmRowReverseValid mmFiber58Key mmFiber58Expected (mmFiber58RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber58ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber58StateAt 0) (mmFiber58StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber58StateAt 0) (mmFiber58StateAt 2)
    (mmFiber58RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber58Key mmFiber58Expected
        (mmFiber58RowAt 2) (by decide) mmFiber58ReverseRow_2_ok
      simpa [mmFiber58StateAt, mmFiber58RowAt, mmFiber58Rows, listGetD, directRow] using h)

theorem mmFiber58ReverseRow_3_ok :
    mmRowReverseValid mmFiber58Key mmFiber58Expected (mmFiber58RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber58Chunk1_ok
  change (mmRowReverseValid mmFiber58Key mmFiber58Expected (mmFiber58RowAt 2) &&
    mmRowReverseValid mmFiber58Key mmFiber58Expected (mmFiber58RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber58ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber58StateAt 1) (mmFiber58StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber58StateAt 1) (mmFiber58StateAt 3)
    (mmFiber58RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber58Key mmFiber58Expected
        (mmFiber58RowAt 3) (by decide) mmFiber58ReverseRow_3_ok
      simpa [mmFiber58StateAt, mmFiber58RowAt, mmFiber58Rows, listGetD, directRow] using h)

theorem mmFiber58ReverseRow_4_ok :
    mmRowReverseValid mmFiber58Key mmFiber58Expected (mmFiber58RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber58Chunk2_ok
  change (mmRowReverseValid mmFiber58Key mmFiber58Expected (mmFiber58RowAt 4) &&
    mmRowReverseValid mmFiber58Key mmFiber58Expected (mmFiber58RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber58ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber58StateAt 0) (mmFiber58StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber58StateAt 0) (mmFiber58StateAt 4)
    (mmFiber58RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber58Key mmFiber58Expected
        (mmFiber58RowAt 4) (by decide) mmFiber58ReverseRow_4_ok
      simpa [mmFiber58StateAt, mmFiber58RowAt, mmFiber58Rows, listGetD, directRow] using h)

theorem mmFiber58ReverseRow_5_ok :
    mmRowReverseValid mmFiber58Key mmFiber58Expected (mmFiber58RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber58Chunk2_ok
  change (mmRowReverseValid mmFiber58Key mmFiber58Expected (mmFiber58RowAt 4) &&
    mmRowReverseValid mmFiber58Key mmFiber58Expected (mmFiber58RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber58ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber58StateAt 1) (mmFiber58StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber58StateAt 1) (mmFiber58StateAt 5)
    (mmFiber58RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber58Key mmFiber58Expected
        (mmFiber58RowAt 5) (by decide) mmFiber58ReverseRow_5_ok
      simpa [mmFiber58StateAt, mmFiber58RowAt, mmFiber58Rows, listGetD, directRow] using h)

theorem mmFiber58ReverseRow_6_ok :
    mmRowReverseValid mmFiber58Key mmFiber58Expected (mmFiber58RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber58Chunk3_ok
  change (mmRowReverseValid mmFiber58Key mmFiber58Expected (mmFiber58RowAt 6) &&
    mmRowReverseValid mmFiber58Key mmFiber58Expected (mmFiber58RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber58ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber58StateAt 2) (mmFiber58StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber58StateAt 2) (mmFiber58StateAt 6)
    (mmFiber58RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber58Key mmFiber58Expected
        (mmFiber58RowAt 6) (by decide) mmFiber58ReverseRow_6_ok
      simpa [mmFiber58StateAt, mmFiber58RowAt, mmFiber58Rows, listGetD, directRow] using h)

theorem mmFiber58ReverseRow_7_ok :
    mmRowReverseValid mmFiber58Key mmFiber58Expected (mmFiber58RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber58Chunk3_ok
  change (mmRowReverseValid mmFiber58Key mmFiber58Expected (mmFiber58RowAt 6) &&
    mmRowReverseValid mmFiber58Key mmFiber58Expected (mmFiber58RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber58ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber58StateAt 3) (mmFiber58StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber58StateAt 3) (mmFiber58StateAt 7)
    (mmFiber58RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber58Key mmFiber58Expected
        (mmFiber58RowAt 7) (by decide) mmFiber58ReverseRow_7_ok
      simpa [mmFiber58StateAt, mmFiber58RowAt, mmFiber58Rows, listGetD, directRow] using h)

theorem mmFiber58State0_in_close :
    mmFiber58StateAt 0 ∈ closeChainFiber mmWord mmFiber58DirectStates mmFiber58DirectStates.length [mmFiber58StateAt 0] := by
  change mmFiber58StateAt 0 ∈ closeChainFiber mmWord mmFiber58DirectStates 8 [mmFiber58StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber58DirectStates 0 8 [mmFiber58StateAt 0] (mmFiber58StateAt 0) (by simp [closeChainFiber])

theorem mmFiber58State1_in_close :
    mmFiber58StateAt 1 ∈ closeChainFiber mmWord mmFiber58DirectStates mmFiber58DirectStates.length [mmFiber58StateAt 0] := by
  have h0 : mmFiber58StateAt 0 ∈ closeChainFiber mmWord mmFiber58DirectStates 0 [mmFiber58StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber58StateAt 1 ∈ closeChainFiber mmWord mmFiber58DirectStates 1 [mmFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber58DirectStates 0 [mmFiber58StateAt 0]
      (mmFiber58StateAt 0) (mmFiber58StateAt 1) (by decide) h0 (by decide)
      mmFiber58ReverseSingleStep1
  change mmFiber58StateAt 1 ∈ closeChainFiber mmWord mmFiber58DirectStates (1 + 7) [mmFiber58StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber58DirectStates 1 7 [mmFiber58StateAt 0] (mmFiber58StateAt 1) h1

theorem mmFiber58State2_in_close :
    mmFiber58StateAt 2 ∈ closeChainFiber mmWord mmFiber58DirectStates mmFiber58DirectStates.length [mmFiber58StateAt 0] := by
  have h0 : mmFiber58StateAt 0 ∈ closeChainFiber mmWord mmFiber58DirectStates 0 [mmFiber58StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber58StateAt 2 ∈ closeChainFiber mmWord mmFiber58DirectStates 1 [mmFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber58DirectStates 0 [mmFiber58StateAt 0]
      (mmFiber58StateAt 0) (mmFiber58StateAt 2) (by decide) h0 (by decide)
      mmFiber58ReverseSingleStep2
  change mmFiber58StateAt 2 ∈ closeChainFiber mmWord mmFiber58DirectStates (1 + 7) [mmFiber58StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber58DirectStates 1 7 [mmFiber58StateAt 0] (mmFiber58StateAt 2) h1

theorem mmFiber58State3_in_close :
    mmFiber58StateAt 3 ∈ closeChainFiber mmWord mmFiber58DirectStates mmFiber58DirectStates.length [mmFiber58StateAt 0] := by
  have h0 : mmFiber58StateAt 0 ∈ closeChainFiber mmWord mmFiber58DirectStates 0 [mmFiber58StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber58StateAt 1 ∈ closeChainFiber mmWord mmFiber58DirectStates 1 [mmFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber58DirectStates 0 [mmFiber58StateAt 0]
      (mmFiber58StateAt 0) (mmFiber58StateAt 1) (by decide) h0 (by decide)
      mmFiber58ReverseSingleStep1
  have h2 : mmFiber58StateAt 3 ∈ closeChainFiber mmWord mmFiber58DirectStates 2 [mmFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber58DirectStates 1 [mmFiber58StateAt 0]
      (mmFiber58StateAt 1) (mmFiber58StateAt 3) (by decide) h1 (by decide)
      mmFiber58ReverseSingleStep3
  change mmFiber58StateAt 3 ∈ closeChainFiber mmWord mmFiber58DirectStates (2 + 6) [mmFiber58StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber58DirectStates 2 6 [mmFiber58StateAt 0] (mmFiber58StateAt 3) h2

theorem mmFiber58State4_in_close :
    mmFiber58StateAt 4 ∈ closeChainFiber mmWord mmFiber58DirectStates mmFiber58DirectStates.length [mmFiber58StateAt 0] := by
  have h0 : mmFiber58StateAt 0 ∈ closeChainFiber mmWord mmFiber58DirectStates 0 [mmFiber58StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber58StateAt 4 ∈ closeChainFiber mmWord mmFiber58DirectStates 1 [mmFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber58DirectStates 0 [mmFiber58StateAt 0]
      (mmFiber58StateAt 0) (mmFiber58StateAt 4) (by decide) h0 (by decide)
      mmFiber58ReverseSingleStep4
  change mmFiber58StateAt 4 ∈ closeChainFiber mmWord mmFiber58DirectStates (1 + 7) [mmFiber58StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber58DirectStates 1 7 [mmFiber58StateAt 0] (mmFiber58StateAt 4) h1

theorem mmFiber58State5_in_close :
    mmFiber58StateAt 5 ∈ closeChainFiber mmWord mmFiber58DirectStates mmFiber58DirectStates.length [mmFiber58StateAt 0] := by
  have h0 : mmFiber58StateAt 0 ∈ closeChainFiber mmWord mmFiber58DirectStates 0 [mmFiber58StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber58StateAt 1 ∈ closeChainFiber mmWord mmFiber58DirectStates 1 [mmFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber58DirectStates 0 [mmFiber58StateAt 0]
      (mmFiber58StateAt 0) (mmFiber58StateAt 1) (by decide) h0 (by decide)
      mmFiber58ReverseSingleStep1
  have h2 : mmFiber58StateAt 5 ∈ closeChainFiber mmWord mmFiber58DirectStates 2 [mmFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber58DirectStates 1 [mmFiber58StateAt 0]
      (mmFiber58StateAt 1) (mmFiber58StateAt 5) (by decide) h1 (by decide)
      mmFiber58ReverseSingleStep5
  change mmFiber58StateAt 5 ∈ closeChainFiber mmWord mmFiber58DirectStates (2 + 6) [mmFiber58StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber58DirectStates 2 6 [mmFiber58StateAt 0] (mmFiber58StateAt 5) h2

theorem mmFiber58State6_in_close :
    mmFiber58StateAt 6 ∈ closeChainFiber mmWord mmFiber58DirectStates mmFiber58DirectStates.length [mmFiber58StateAt 0] := by
  have h0 : mmFiber58StateAt 0 ∈ closeChainFiber mmWord mmFiber58DirectStates 0 [mmFiber58StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber58StateAt 2 ∈ closeChainFiber mmWord mmFiber58DirectStates 1 [mmFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber58DirectStates 0 [mmFiber58StateAt 0]
      (mmFiber58StateAt 0) (mmFiber58StateAt 2) (by decide) h0 (by decide)
      mmFiber58ReverseSingleStep2
  have h2 : mmFiber58StateAt 6 ∈ closeChainFiber mmWord mmFiber58DirectStates 2 [mmFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber58DirectStates 1 [mmFiber58StateAt 0]
      (mmFiber58StateAt 2) (mmFiber58StateAt 6) (by decide) h1 (by decide)
      mmFiber58ReverseSingleStep6
  change mmFiber58StateAt 6 ∈ closeChainFiber mmWord mmFiber58DirectStates (2 + 6) [mmFiber58StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber58DirectStates 2 6 [mmFiber58StateAt 0] (mmFiber58StateAt 6) h2

theorem mmFiber58State7_in_close :
    mmFiber58StateAt 7 ∈ closeChainFiber mmWord mmFiber58DirectStates mmFiber58DirectStates.length [mmFiber58StateAt 0] := by
  have h0 : mmFiber58StateAt 0 ∈ closeChainFiber mmWord mmFiber58DirectStates 0 [mmFiber58StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber58StateAt 1 ∈ closeChainFiber mmWord mmFiber58DirectStates 1 [mmFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber58DirectStates 0 [mmFiber58StateAt 0]
      (mmFiber58StateAt 0) (mmFiber58StateAt 1) (by decide) h0 (by decide)
      mmFiber58ReverseSingleStep1
  have h2 : mmFiber58StateAt 3 ∈ closeChainFiber mmWord mmFiber58DirectStates 2 [mmFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber58DirectStates 1 [mmFiber58StateAt 0]
      (mmFiber58StateAt 1) (mmFiber58StateAt 3) (by decide) h1 (by decide)
      mmFiber58ReverseSingleStep3
  have h3 : mmFiber58StateAt 7 ∈ closeChainFiber mmWord mmFiber58DirectStates 3 [mmFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber58DirectStates 2 [mmFiber58StateAt 0]
      (mmFiber58StateAt 3) (mmFiber58StateAt 7) (by decide) h2 (by decide)
      mmFiber58ReverseSingleStep7
  change mmFiber58StateAt 7 ∈ closeChainFiber mmWord mmFiber58DirectStates (3 + 5) [mmFiber58StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber58DirectStates 3 5 [mmFiber58StateAt 0] (mmFiber58StateAt 7) h3

theorem mmFiber58DirectConnected :
    chainFiberConnected mmWord mmFiber58DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber58DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber58State0_in_close
  · subst state
    exact mmFiber58State1_in_close
  · subst state
    exact mmFiber58State2_in_close
  · subst state
    exact mmFiber58State3_in_close
  · subst state
    exact mmFiber58State4_in_close
  · subst state
    exact mmFiber58State5_in_close
  · subst state
    exact mmFiber58State6_in_close
  · subst state
    exact mmFiber58State7_in_close
  · cases h
def mmFiber62StateAt (i : Nat) : List TauState :=
  directStates (mmFiber62RowAt i).sourceLeft (mmFiber62RowAt i).sourceRight

def mmFiber62DirectStates : List (List TauState) :=
  [mmFiber62StateAt 0, mmFiber62StateAt 1, mmFiber62StateAt 2, mmFiber62StateAt 3, mmFiber62StateAt 4, mmFiber62StateAt 5, mmFiber62StateAt 6, mmFiber62StateAt 7]

theorem mmFiber62ReverseRow_1_ok :
    mmRowReverseValid mmFiber62Key mmFiber62Expected (mmFiber62RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber62Chunk0_ok
  change (mmRowReverseValid mmFiber62Key mmFiber62Expected (mmFiber62RowAt 0) &&
    mmRowReverseValid mmFiber62Key mmFiber62Expected (mmFiber62RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber62ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber62StateAt 0) (mmFiber62StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber62StateAt 0) (mmFiber62StateAt 1)
    (mmFiber62RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber62Key mmFiber62Expected
        (mmFiber62RowAt 1) (by decide) mmFiber62ReverseRow_1_ok
      simpa [mmFiber62StateAt, mmFiber62RowAt, mmFiber62Rows, listGetD, directRow] using h)

theorem mmFiber62ReverseRow_2_ok :
    mmRowReverseValid mmFiber62Key mmFiber62Expected (mmFiber62RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber62Chunk1_ok
  change (mmRowReverseValid mmFiber62Key mmFiber62Expected (mmFiber62RowAt 2) &&
    mmRowReverseValid mmFiber62Key mmFiber62Expected (mmFiber62RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber62ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber62StateAt 0) (mmFiber62StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber62StateAt 0) (mmFiber62StateAt 2)
    (mmFiber62RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber62Key mmFiber62Expected
        (mmFiber62RowAt 2) (by decide) mmFiber62ReverseRow_2_ok
      simpa [mmFiber62StateAt, mmFiber62RowAt, mmFiber62Rows, listGetD, directRow] using h)

theorem mmFiber62ReverseRow_3_ok :
    mmRowReverseValid mmFiber62Key mmFiber62Expected (mmFiber62RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber62Chunk1_ok
  change (mmRowReverseValid mmFiber62Key mmFiber62Expected (mmFiber62RowAt 2) &&
    mmRowReverseValid mmFiber62Key mmFiber62Expected (mmFiber62RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber62ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber62StateAt 1) (mmFiber62StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber62StateAt 1) (mmFiber62StateAt 3)
    (mmFiber62RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber62Key mmFiber62Expected
        (mmFiber62RowAt 3) (by decide) mmFiber62ReverseRow_3_ok
      simpa [mmFiber62StateAt, mmFiber62RowAt, mmFiber62Rows, listGetD, directRow] using h)

theorem mmFiber62ReverseRow_4_ok :
    mmRowReverseValid mmFiber62Key mmFiber62Expected (mmFiber62RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber62Chunk2_ok
  change (mmRowReverseValid mmFiber62Key mmFiber62Expected (mmFiber62RowAt 4) &&
    mmRowReverseValid mmFiber62Key mmFiber62Expected (mmFiber62RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber62ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber62StateAt 0) (mmFiber62StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber62StateAt 0) (mmFiber62StateAt 4)
    (mmFiber62RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber62Key mmFiber62Expected
        (mmFiber62RowAt 4) (by decide) mmFiber62ReverseRow_4_ok
      simpa [mmFiber62StateAt, mmFiber62RowAt, mmFiber62Rows, listGetD, directRow] using h)

theorem mmFiber62ReverseRow_5_ok :
    mmRowReverseValid mmFiber62Key mmFiber62Expected (mmFiber62RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber62Chunk2_ok
  change (mmRowReverseValid mmFiber62Key mmFiber62Expected (mmFiber62RowAt 4) &&
    mmRowReverseValid mmFiber62Key mmFiber62Expected (mmFiber62RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber62ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber62StateAt 1) (mmFiber62StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber62StateAt 1) (mmFiber62StateAt 5)
    (mmFiber62RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber62Key mmFiber62Expected
        (mmFiber62RowAt 5) (by decide) mmFiber62ReverseRow_5_ok
      simpa [mmFiber62StateAt, mmFiber62RowAt, mmFiber62Rows, listGetD, directRow] using h)

theorem mmFiber62ReverseRow_6_ok :
    mmRowReverseValid mmFiber62Key mmFiber62Expected (mmFiber62RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber62Chunk3_ok
  change (mmRowReverseValid mmFiber62Key mmFiber62Expected (mmFiber62RowAt 6) &&
    mmRowReverseValid mmFiber62Key mmFiber62Expected (mmFiber62RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber62ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber62StateAt 2) (mmFiber62StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber62StateAt 2) (mmFiber62StateAt 6)
    (mmFiber62RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber62Key mmFiber62Expected
        (mmFiber62RowAt 6) (by decide) mmFiber62ReverseRow_6_ok
      simpa [mmFiber62StateAt, mmFiber62RowAt, mmFiber62Rows, listGetD, directRow] using h)

theorem mmFiber62ReverseRow_7_ok :
    mmRowReverseValid mmFiber62Key mmFiber62Expected (mmFiber62RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber62Chunk3_ok
  change (mmRowReverseValid mmFiber62Key mmFiber62Expected (mmFiber62RowAt 6) &&
    mmRowReverseValid mmFiber62Key mmFiber62Expected (mmFiber62RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber62ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber62StateAt 3) (mmFiber62StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber62StateAt 3) (mmFiber62StateAt 7)
    (mmFiber62RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber62Key mmFiber62Expected
        (mmFiber62RowAt 7) (by decide) mmFiber62ReverseRow_7_ok
      simpa [mmFiber62StateAt, mmFiber62RowAt, mmFiber62Rows, listGetD, directRow] using h)

theorem mmFiber62State0_in_close :
    mmFiber62StateAt 0 ∈ closeChainFiber mmWord mmFiber62DirectStates mmFiber62DirectStates.length [mmFiber62StateAt 0] := by
  change mmFiber62StateAt 0 ∈ closeChainFiber mmWord mmFiber62DirectStates 8 [mmFiber62StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber62DirectStates 0 8 [mmFiber62StateAt 0] (mmFiber62StateAt 0) (by simp [closeChainFiber])

theorem mmFiber62State1_in_close :
    mmFiber62StateAt 1 ∈ closeChainFiber mmWord mmFiber62DirectStates mmFiber62DirectStates.length [mmFiber62StateAt 0] := by
  have h0 : mmFiber62StateAt 0 ∈ closeChainFiber mmWord mmFiber62DirectStates 0 [mmFiber62StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber62StateAt 1 ∈ closeChainFiber mmWord mmFiber62DirectStates 1 [mmFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber62DirectStates 0 [mmFiber62StateAt 0]
      (mmFiber62StateAt 0) (mmFiber62StateAt 1) (by decide) h0 (by decide)
      mmFiber62ReverseSingleStep1
  change mmFiber62StateAt 1 ∈ closeChainFiber mmWord mmFiber62DirectStates (1 + 7) [mmFiber62StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber62DirectStates 1 7 [mmFiber62StateAt 0] (mmFiber62StateAt 1) h1

theorem mmFiber62State2_in_close :
    mmFiber62StateAt 2 ∈ closeChainFiber mmWord mmFiber62DirectStates mmFiber62DirectStates.length [mmFiber62StateAt 0] := by
  have h0 : mmFiber62StateAt 0 ∈ closeChainFiber mmWord mmFiber62DirectStates 0 [mmFiber62StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber62StateAt 2 ∈ closeChainFiber mmWord mmFiber62DirectStates 1 [mmFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber62DirectStates 0 [mmFiber62StateAt 0]
      (mmFiber62StateAt 0) (mmFiber62StateAt 2) (by decide) h0 (by decide)
      mmFiber62ReverseSingleStep2
  change mmFiber62StateAt 2 ∈ closeChainFiber mmWord mmFiber62DirectStates (1 + 7) [mmFiber62StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber62DirectStates 1 7 [mmFiber62StateAt 0] (mmFiber62StateAt 2) h1

theorem mmFiber62State3_in_close :
    mmFiber62StateAt 3 ∈ closeChainFiber mmWord mmFiber62DirectStates mmFiber62DirectStates.length [mmFiber62StateAt 0] := by
  have h0 : mmFiber62StateAt 0 ∈ closeChainFiber mmWord mmFiber62DirectStates 0 [mmFiber62StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber62StateAt 1 ∈ closeChainFiber mmWord mmFiber62DirectStates 1 [mmFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber62DirectStates 0 [mmFiber62StateAt 0]
      (mmFiber62StateAt 0) (mmFiber62StateAt 1) (by decide) h0 (by decide)
      mmFiber62ReverseSingleStep1
  have h2 : mmFiber62StateAt 3 ∈ closeChainFiber mmWord mmFiber62DirectStates 2 [mmFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber62DirectStates 1 [mmFiber62StateAt 0]
      (mmFiber62StateAt 1) (mmFiber62StateAt 3) (by decide) h1 (by decide)
      mmFiber62ReverseSingleStep3
  change mmFiber62StateAt 3 ∈ closeChainFiber mmWord mmFiber62DirectStates (2 + 6) [mmFiber62StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber62DirectStates 2 6 [mmFiber62StateAt 0] (mmFiber62StateAt 3) h2

theorem mmFiber62State4_in_close :
    mmFiber62StateAt 4 ∈ closeChainFiber mmWord mmFiber62DirectStates mmFiber62DirectStates.length [mmFiber62StateAt 0] := by
  have h0 : mmFiber62StateAt 0 ∈ closeChainFiber mmWord mmFiber62DirectStates 0 [mmFiber62StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber62StateAt 4 ∈ closeChainFiber mmWord mmFiber62DirectStates 1 [mmFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber62DirectStates 0 [mmFiber62StateAt 0]
      (mmFiber62StateAt 0) (mmFiber62StateAt 4) (by decide) h0 (by decide)
      mmFiber62ReverseSingleStep4
  change mmFiber62StateAt 4 ∈ closeChainFiber mmWord mmFiber62DirectStates (1 + 7) [mmFiber62StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber62DirectStates 1 7 [mmFiber62StateAt 0] (mmFiber62StateAt 4) h1

theorem mmFiber62State5_in_close :
    mmFiber62StateAt 5 ∈ closeChainFiber mmWord mmFiber62DirectStates mmFiber62DirectStates.length [mmFiber62StateAt 0] := by
  have h0 : mmFiber62StateAt 0 ∈ closeChainFiber mmWord mmFiber62DirectStates 0 [mmFiber62StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber62StateAt 1 ∈ closeChainFiber mmWord mmFiber62DirectStates 1 [mmFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber62DirectStates 0 [mmFiber62StateAt 0]
      (mmFiber62StateAt 0) (mmFiber62StateAt 1) (by decide) h0 (by decide)
      mmFiber62ReverseSingleStep1
  have h2 : mmFiber62StateAt 5 ∈ closeChainFiber mmWord mmFiber62DirectStates 2 [mmFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber62DirectStates 1 [mmFiber62StateAt 0]
      (mmFiber62StateAt 1) (mmFiber62StateAt 5) (by decide) h1 (by decide)
      mmFiber62ReverseSingleStep5
  change mmFiber62StateAt 5 ∈ closeChainFiber mmWord mmFiber62DirectStates (2 + 6) [mmFiber62StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber62DirectStates 2 6 [mmFiber62StateAt 0] (mmFiber62StateAt 5) h2

theorem mmFiber62State6_in_close :
    mmFiber62StateAt 6 ∈ closeChainFiber mmWord mmFiber62DirectStates mmFiber62DirectStates.length [mmFiber62StateAt 0] := by
  have h0 : mmFiber62StateAt 0 ∈ closeChainFiber mmWord mmFiber62DirectStates 0 [mmFiber62StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber62StateAt 2 ∈ closeChainFiber mmWord mmFiber62DirectStates 1 [mmFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber62DirectStates 0 [mmFiber62StateAt 0]
      (mmFiber62StateAt 0) (mmFiber62StateAt 2) (by decide) h0 (by decide)
      mmFiber62ReverseSingleStep2
  have h2 : mmFiber62StateAt 6 ∈ closeChainFiber mmWord mmFiber62DirectStates 2 [mmFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber62DirectStates 1 [mmFiber62StateAt 0]
      (mmFiber62StateAt 2) (mmFiber62StateAt 6) (by decide) h1 (by decide)
      mmFiber62ReverseSingleStep6
  change mmFiber62StateAt 6 ∈ closeChainFiber mmWord mmFiber62DirectStates (2 + 6) [mmFiber62StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber62DirectStates 2 6 [mmFiber62StateAt 0] (mmFiber62StateAt 6) h2

theorem mmFiber62State7_in_close :
    mmFiber62StateAt 7 ∈ closeChainFiber mmWord mmFiber62DirectStates mmFiber62DirectStates.length [mmFiber62StateAt 0] := by
  have h0 : mmFiber62StateAt 0 ∈ closeChainFiber mmWord mmFiber62DirectStates 0 [mmFiber62StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber62StateAt 1 ∈ closeChainFiber mmWord mmFiber62DirectStates 1 [mmFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber62DirectStates 0 [mmFiber62StateAt 0]
      (mmFiber62StateAt 0) (mmFiber62StateAt 1) (by decide) h0 (by decide)
      mmFiber62ReverseSingleStep1
  have h2 : mmFiber62StateAt 3 ∈ closeChainFiber mmWord mmFiber62DirectStates 2 [mmFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber62DirectStates 1 [mmFiber62StateAt 0]
      (mmFiber62StateAt 1) (mmFiber62StateAt 3) (by decide) h1 (by decide)
      mmFiber62ReverseSingleStep3
  have h3 : mmFiber62StateAt 7 ∈ closeChainFiber mmWord mmFiber62DirectStates 3 [mmFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber62DirectStates 2 [mmFiber62StateAt 0]
      (mmFiber62StateAt 3) (mmFiber62StateAt 7) (by decide) h2 (by decide)
      mmFiber62ReverseSingleStep7
  change mmFiber62StateAt 7 ∈ closeChainFiber mmWord mmFiber62DirectStates (3 + 5) [mmFiber62StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber62DirectStates 3 5 [mmFiber62StateAt 0] (mmFiber62StateAt 7) h3

theorem mmFiber62DirectConnected :
    chainFiberConnected mmWord mmFiber62DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber62DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber62State0_in_close
  · subst state
    exact mmFiber62State1_in_close
  · subst state
    exact mmFiber62State2_in_close
  · subst state
    exact mmFiber62State3_in_close
  · subst state
    exact mmFiber62State4_in_close
  · subst state
    exact mmFiber62State5_in_close
  · subst state
    exact mmFiber62State6_in_close
  · subst state
    exact mmFiber62State7_in_close
  · cases h
def mmFiber63StateAt (i : Nat) : List TauState :=
  directStates (mmFiber63RowAt i).sourceLeft (mmFiber63RowAt i).sourceRight

def mmFiber63DirectStates : List (List TauState) :=
  [mmFiber63StateAt 0, mmFiber63StateAt 1, mmFiber63StateAt 2, mmFiber63StateAt 3, mmFiber63StateAt 4, mmFiber63StateAt 5, mmFiber63StateAt 6, mmFiber63StateAt 7]

theorem mmFiber63ReverseRow_1_ok :
    mmRowReverseValid mmFiber63Key mmFiber63Expected (mmFiber63RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber63Chunk0_ok
  change (mmRowReverseValid mmFiber63Key mmFiber63Expected (mmFiber63RowAt 0) &&
    mmRowReverseValid mmFiber63Key mmFiber63Expected (mmFiber63RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber63ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber63StateAt 0) (mmFiber63StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber63StateAt 0) (mmFiber63StateAt 1)
    (mmFiber63RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber63Key mmFiber63Expected
        (mmFiber63RowAt 1) (by decide) mmFiber63ReverseRow_1_ok
      simpa [mmFiber63StateAt, mmFiber63RowAt, mmFiber63Rows, listGetD, directRow] using h)

theorem mmFiber63ReverseRow_2_ok :
    mmRowReverseValid mmFiber63Key mmFiber63Expected (mmFiber63RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber63Chunk1_ok
  change (mmRowReverseValid mmFiber63Key mmFiber63Expected (mmFiber63RowAt 2) &&
    mmRowReverseValid mmFiber63Key mmFiber63Expected (mmFiber63RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber63ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber63StateAt 1) (mmFiber63StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber63StateAt 1) (mmFiber63StateAt 2)
    (mmFiber63RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber63Key mmFiber63Expected
        (mmFiber63RowAt 2) (by decide) mmFiber63ReverseRow_2_ok
      simpa [mmFiber63StateAt, mmFiber63RowAt, mmFiber63Rows, listGetD, directRow] using h)

theorem mmFiber63ReverseRow_3_ok :
    mmRowReverseValid mmFiber63Key mmFiber63Expected (mmFiber63RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber63Chunk1_ok
  change (mmRowReverseValid mmFiber63Key mmFiber63Expected (mmFiber63RowAt 2) &&
    mmRowReverseValid mmFiber63Key mmFiber63Expected (mmFiber63RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber63ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber63StateAt 0) (mmFiber63StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber63StateAt 0) (mmFiber63StateAt 3)
    (mmFiber63RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber63Key mmFiber63Expected
        (mmFiber63RowAt 3) (by decide) mmFiber63ReverseRow_3_ok
      simpa [mmFiber63StateAt, mmFiber63RowAt, mmFiber63Rows, listGetD, directRow] using h)

theorem mmFiber63ReverseRow_4_ok :
    mmRowReverseValid mmFiber63Key mmFiber63Expected (mmFiber63RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber63Chunk2_ok
  change (mmRowReverseValid mmFiber63Key mmFiber63Expected (mmFiber63RowAt 4) &&
    mmRowReverseValid mmFiber63Key mmFiber63Expected (mmFiber63RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber63ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber63StateAt 0) (mmFiber63StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber63StateAt 0) (mmFiber63StateAt 4)
    (mmFiber63RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber63Key mmFiber63Expected
        (mmFiber63RowAt 4) (by decide) mmFiber63ReverseRow_4_ok
      simpa [mmFiber63StateAt, mmFiber63RowAt, mmFiber63Rows, listGetD, directRow] using h)

theorem mmFiber63ReverseRow_5_ok :
    mmRowReverseValid mmFiber63Key mmFiber63Expected (mmFiber63RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber63Chunk2_ok
  change (mmRowReverseValid mmFiber63Key mmFiber63Expected (mmFiber63RowAt 4) &&
    mmRowReverseValid mmFiber63Key mmFiber63Expected (mmFiber63RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber63ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber63StateAt 1) (mmFiber63StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber63StateAt 1) (mmFiber63StateAt 5)
    (mmFiber63RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber63Key mmFiber63Expected
        (mmFiber63RowAt 5) (by decide) mmFiber63ReverseRow_5_ok
      simpa [mmFiber63StateAt, mmFiber63RowAt, mmFiber63Rows, listGetD, directRow] using h)

theorem mmFiber63ReverseRow_6_ok :
    mmRowReverseValid mmFiber63Key mmFiber63Expected (mmFiber63RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber63Chunk3_ok
  change (mmRowReverseValid mmFiber63Key mmFiber63Expected (mmFiber63RowAt 6) &&
    mmRowReverseValid mmFiber63Key mmFiber63Expected (mmFiber63RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber63ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber63StateAt 2) (mmFiber63StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber63StateAt 2) (mmFiber63StateAt 6)
    (mmFiber63RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber63Key mmFiber63Expected
        (mmFiber63RowAt 6) (by decide) mmFiber63ReverseRow_6_ok
      simpa [mmFiber63StateAt, mmFiber63RowAt, mmFiber63Rows, listGetD, directRow] using h)

theorem mmFiber63ReverseRow_7_ok :
    mmRowReverseValid mmFiber63Key mmFiber63Expected (mmFiber63RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber63Chunk3_ok
  change (mmRowReverseValid mmFiber63Key mmFiber63Expected (mmFiber63RowAt 6) &&
    mmRowReverseValid mmFiber63Key mmFiber63Expected (mmFiber63RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber63ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber63StateAt 3) (mmFiber63StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber63StateAt 3) (mmFiber63StateAt 7)
    (mmFiber63RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber63Key mmFiber63Expected
        (mmFiber63RowAt 7) (by decide) mmFiber63ReverseRow_7_ok
      simpa [mmFiber63StateAt, mmFiber63RowAt, mmFiber63Rows, listGetD, directRow] using h)

theorem mmFiber63State0_in_close :
    mmFiber63StateAt 0 ∈ closeChainFiber mmWord mmFiber63DirectStates mmFiber63DirectStates.length [mmFiber63StateAt 0] := by
  change mmFiber63StateAt 0 ∈ closeChainFiber mmWord mmFiber63DirectStates 8 [mmFiber63StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber63DirectStates 0 8 [mmFiber63StateAt 0] (mmFiber63StateAt 0) (by simp [closeChainFiber])

theorem mmFiber63State1_in_close :
    mmFiber63StateAt 1 ∈ closeChainFiber mmWord mmFiber63DirectStates mmFiber63DirectStates.length [mmFiber63StateAt 0] := by
  have h0 : mmFiber63StateAt 0 ∈ closeChainFiber mmWord mmFiber63DirectStates 0 [mmFiber63StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber63StateAt 1 ∈ closeChainFiber mmWord mmFiber63DirectStates 1 [mmFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber63DirectStates 0 [mmFiber63StateAt 0]
      (mmFiber63StateAt 0) (mmFiber63StateAt 1) (by decide) h0 (by decide)
      mmFiber63ReverseSingleStep1
  change mmFiber63StateAt 1 ∈ closeChainFiber mmWord mmFiber63DirectStates (1 + 7) [mmFiber63StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber63DirectStates 1 7 [mmFiber63StateAt 0] (mmFiber63StateAt 1) h1

theorem mmFiber63State2_in_close :
    mmFiber63StateAt 2 ∈ closeChainFiber mmWord mmFiber63DirectStates mmFiber63DirectStates.length [mmFiber63StateAt 0] := by
  have h0 : mmFiber63StateAt 0 ∈ closeChainFiber mmWord mmFiber63DirectStates 0 [mmFiber63StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber63StateAt 1 ∈ closeChainFiber mmWord mmFiber63DirectStates 1 [mmFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber63DirectStates 0 [mmFiber63StateAt 0]
      (mmFiber63StateAt 0) (mmFiber63StateAt 1) (by decide) h0 (by decide)
      mmFiber63ReverseSingleStep1
  have h2 : mmFiber63StateAt 2 ∈ closeChainFiber mmWord mmFiber63DirectStates 2 [mmFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber63DirectStates 1 [mmFiber63StateAt 0]
      (mmFiber63StateAt 1) (mmFiber63StateAt 2) (by decide) h1 (by decide)
      mmFiber63ReverseSingleStep2
  change mmFiber63StateAt 2 ∈ closeChainFiber mmWord mmFiber63DirectStates (2 + 6) [mmFiber63StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber63DirectStates 2 6 [mmFiber63StateAt 0] (mmFiber63StateAt 2) h2

theorem mmFiber63State3_in_close :
    mmFiber63StateAt 3 ∈ closeChainFiber mmWord mmFiber63DirectStates mmFiber63DirectStates.length [mmFiber63StateAt 0] := by
  have h0 : mmFiber63StateAt 0 ∈ closeChainFiber mmWord mmFiber63DirectStates 0 [mmFiber63StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber63StateAt 3 ∈ closeChainFiber mmWord mmFiber63DirectStates 1 [mmFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber63DirectStates 0 [mmFiber63StateAt 0]
      (mmFiber63StateAt 0) (mmFiber63StateAt 3) (by decide) h0 (by decide)
      mmFiber63ReverseSingleStep3
  change mmFiber63StateAt 3 ∈ closeChainFiber mmWord mmFiber63DirectStates (1 + 7) [mmFiber63StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber63DirectStates 1 7 [mmFiber63StateAt 0] (mmFiber63StateAt 3) h1

theorem mmFiber63State4_in_close :
    mmFiber63StateAt 4 ∈ closeChainFiber mmWord mmFiber63DirectStates mmFiber63DirectStates.length [mmFiber63StateAt 0] := by
  have h0 : mmFiber63StateAt 0 ∈ closeChainFiber mmWord mmFiber63DirectStates 0 [mmFiber63StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber63StateAt 4 ∈ closeChainFiber mmWord mmFiber63DirectStates 1 [mmFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber63DirectStates 0 [mmFiber63StateAt 0]
      (mmFiber63StateAt 0) (mmFiber63StateAt 4) (by decide) h0 (by decide)
      mmFiber63ReverseSingleStep4
  change mmFiber63StateAt 4 ∈ closeChainFiber mmWord mmFiber63DirectStates (1 + 7) [mmFiber63StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber63DirectStates 1 7 [mmFiber63StateAt 0] (mmFiber63StateAt 4) h1

theorem mmFiber63State5_in_close :
    mmFiber63StateAt 5 ∈ closeChainFiber mmWord mmFiber63DirectStates mmFiber63DirectStates.length [mmFiber63StateAt 0] := by
  have h0 : mmFiber63StateAt 0 ∈ closeChainFiber mmWord mmFiber63DirectStates 0 [mmFiber63StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber63StateAt 1 ∈ closeChainFiber mmWord mmFiber63DirectStates 1 [mmFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber63DirectStates 0 [mmFiber63StateAt 0]
      (mmFiber63StateAt 0) (mmFiber63StateAt 1) (by decide) h0 (by decide)
      mmFiber63ReverseSingleStep1
  have h2 : mmFiber63StateAt 5 ∈ closeChainFiber mmWord mmFiber63DirectStates 2 [mmFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber63DirectStates 1 [mmFiber63StateAt 0]
      (mmFiber63StateAt 1) (mmFiber63StateAt 5) (by decide) h1 (by decide)
      mmFiber63ReverseSingleStep5
  change mmFiber63StateAt 5 ∈ closeChainFiber mmWord mmFiber63DirectStates (2 + 6) [mmFiber63StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber63DirectStates 2 6 [mmFiber63StateAt 0] (mmFiber63StateAt 5) h2

theorem mmFiber63State6_in_close :
    mmFiber63StateAt 6 ∈ closeChainFiber mmWord mmFiber63DirectStates mmFiber63DirectStates.length [mmFiber63StateAt 0] := by
  have h0 : mmFiber63StateAt 0 ∈ closeChainFiber mmWord mmFiber63DirectStates 0 [mmFiber63StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber63StateAt 1 ∈ closeChainFiber mmWord mmFiber63DirectStates 1 [mmFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber63DirectStates 0 [mmFiber63StateAt 0]
      (mmFiber63StateAt 0) (mmFiber63StateAt 1) (by decide) h0 (by decide)
      mmFiber63ReverseSingleStep1
  have h2 : mmFiber63StateAt 2 ∈ closeChainFiber mmWord mmFiber63DirectStates 2 [mmFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber63DirectStates 1 [mmFiber63StateAt 0]
      (mmFiber63StateAt 1) (mmFiber63StateAt 2) (by decide) h1 (by decide)
      mmFiber63ReverseSingleStep2
  have h3 : mmFiber63StateAt 6 ∈ closeChainFiber mmWord mmFiber63DirectStates 3 [mmFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber63DirectStates 2 [mmFiber63StateAt 0]
      (mmFiber63StateAt 2) (mmFiber63StateAt 6) (by decide) h2 (by decide)
      mmFiber63ReverseSingleStep6
  change mmFiber63StateAt 6 ∈ closeChainFiber mmWord mmFiber63DirectStates (3 + 5) [mmFiber63StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber63DirectStates 3 5 [mmFiber63StateAt 0] (mmFiber63StateAt 6) h3

theorem mmFiber63State7_in_close :
    mmFiber63StateAt 7 ∈ closeChainFiber mmWord mmFiber63DirectStates mmFiber63DirectStates.length [mmFiber63StateAt 0] := by
  have h0 : mmFiber63StateAt 0 ∈ closeChainFiber mmWord mmFiber63DirectStates 0 [mmFiber63StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber63StateAt 3 ∈ closeChainFiber mmWord mmFiber63DirectStates 1 [mmFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber63DirectStates 0 [mmFiber63StateAt 0]
      (mmFiber63StateAt 0) (mmFiber63StateAt 3) (by decide) h0 (by decide)
      mmFiber63ReverseSingleStep3
  have h2 : mmFiber63StateAt 7 ∈ closeChainFiber mmWord mmFiber63DirectStates 2 [mmFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber63DirectStates 1 [mmFiber63StateAt 0]
      (mmFiber63StateAt 3) (mmFiber63StateAt 7) (by decide) h1 (by decide)
      mmFiber63ReverseSingleStep7
  change mmFiber63StateAt 7 ∈ closeChainFiber mmWord mmFiber63DirectStates (2 + 6) [mmFiber63StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber63DirectStates 2 6 [mmFiber63StateAt 0] (mmFiber63StateAt 7) h2

theorem mmFiber63DirectConnected :
    chainFiberConnected mmWord mmFiber63DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber63DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber63State0_in_close
  · subst state
    exact mmFiber63State1_in_close
  · subst state
    exact mmFiber63State2_in_close
  · subst state
    exact mmFiber63State3_in_close
  · subst state
    exact mmFiber63State4_in_close
  · subst state
    exact mmFiber63State5_in_close
  · subst state
    exact mmFiber63State6_in_close
  · subst state
    exact mmFiber63State7_in_close
  · cases h
end GoertzelLemma818LengthTwoMMBridge

end Mettapedia.GraphTheory.FourColor
