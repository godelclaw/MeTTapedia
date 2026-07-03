import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for size-8 `mirror,mirror` length-two fibers, group 1

This module proves direct connectedness for generated `mirror,mirror` size-8 fibers from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMMBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorMirrorCertificate
open GoertzelLemma818MirrorMirrorReverseAudit

def mmFiber17StateAt (i : Nat) : List TauState :=
  directStates (mmFiber17RowAt i).sourceLeft (mmFiber17RowAt i).sourceRight

def mmFiber17DirectStates : List (List TauState) :=
  [mmFiber17StateAt 0, mmFiber17StateAt 1, mmFiber17StateAt 2, mmFiber17StateAt 3, mmFiber17StateAt 4, mmFiber17StateAt 5, mmFiber17StateAt 6, mmFiber17StateAt 7]

theorem mmFiber17ReverseRow_1_ok :
    mmRowReverseValid mmFiber17Key mmFiber17Expected (mmFiber17RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber17Chunk0_ok
  change (mmRowReverseValid mmFiber17Key mmFiber17Expected (mmFiber17RowAt 0) &&
    mmRowReverseValid mmFiber17Key mmFiber17Expected (mmFiber17RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber17ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber17StateAt 0) (mmFiber17StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber17StateAt 0) (mmFiber17StateAt 1)
    (mmFiber17RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber17Key mmFiber17Expected
        (mmFiber17RowAt 1) (by decide) mmFiber17ReverseRow_1_ok
      simpa [mmFiber17StateAt, mmFiber17RowAt, mmFiber17Rows, listGetD, directRow] using h)

theorem mmFiber17ReverseRow_2_ok :
    mmRowReverseValid mmFiber17Key mmFiber17Expected (mmFiber17RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber17Chunk1_ok
  change (mmRowReverseValid mmFiber17Key mmFiber17Expected (mmFiber17RowAt 2) &&
    mmRowReverseValid mmFiber17Key mmFiber17Expected (mmFiber17RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber17ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber17StateAt 1) (mmFiber17StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber17StateAt 1) (mmFiber17StateAt 2)
    (mmFiber17RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber17Key mmFiber17Expected
        (mmFiber17RowAt 2) (by decide) mmFiber17ReverseRow_2_ok
      simpa [mmFiber17StateAt, mmFiber17RowAt, mmFiber17Rows, listGetD, directRow] using h)

theorem mmFiber17ReverseRow_3_ok :
    mmRowReverseValid mmFiber17Key mmFiber17Expected (mmFiber17RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber17Chunk1_ok
  change (mmRowReverseValid mmFiber17Key mmFiber17Expected (mmFiber17RowAt 2) &&
    mmRowReverseValid mmFiber17Key mmFiber17Expected (mmFiber17RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber17ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber17StateAt 0) (mmFiber17StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber17StateAt 0) (mmFiber17StateAt 3)
    (mmFiber17RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber17Key mmFiber17Expected
        (mmFiber17RowAt 3) (by decide) mmFiber17ReverseRow_3_ok
      simpa [mmFiber17StateAt, mmFiber17RowAt, mmFiber17Rows, listGetD, directRow] using h)

theorem mmFiber17ReverseRow_4_ok :
    mmRowReverseValid mmFiber17Key mmFiber17Expected (mmFiber17RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber17Chunk2_ok
  change (mmRowReverseValid mmFiber17Key mmFiber17Expected (mmFiber17RowAt 4) &&
    mmRowReverseValid mmFiber17Key mmFiber17Expected (mmFiber17RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber17ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber17StateAt 0) (mmFiber17StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber17StateAt 0) (mmFiber17StateAt 4)
    (mmFiber17RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber17Key mmFiber17Expected
        (mmFiber17RowAt 4) (by decide) mmFiber17ReverseRow_4_ok
      simpa [mmFiber17StateAt, mmFiber17RowAt, mmFiber17Rows, listGetD, directRow] using h)

theorem mmFiber17ReverseRow_5_ok :
    mmRowReverseValid mmFiber17Key mmFiber17Expected (mmFiber17RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber17Chunk2_ok
  change (mmRowReverseValid mmFiber17Key mmFiber17Expected (mmFiber17RowAt 4) &&
    mmRowReverseValid mmFiber17Key mmFiber17Expected (mmFiber17RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber17ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber17StateAt 1) (mmFiber17StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber17StateAt 1) (mmFiber17StateAt 5)
    (mmFiber17RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber17Key mmFiber17Expected
        (mmFiber17RowAt 5) (by decide) mmFiber17ReverseRow_5_ok
      simpa [mmFiber17StateAt, mmFiber17RowAt, mmFiber17Rows, listGetD, directRow] using h)

theorem mmFiber17ReverseRow_6_ok :
    mmRowReverseValid mmFiber17Key mmFiber17Expected (mmFiber17RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber17Chunk3_ok
  change (mmRowReverseValid mmFiber17Key mmFiber17Expected (mmFiber17RowAt 6) &&
    mmRowReverseValid mmFiber17Key mmFiber17Expected (mmFiber17RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber17ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber17StateAt 2) (mmFiber17StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber17StateAt 2) (mmFiber17StateAt 6)
    (mmFiber17RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber17Key mmFiber17Expected
        (mmFiber17RowAt 6) (by decide) mmFiber17ReverseRow_6_ok
      simpa [mmFiber17StateAt, mmFiber17RowAt, mmFiber17Rows, listGetD, directRow] using h)

theorem mmFiber17ReverseRow_7_ok :
    mmRowReverseValid mmFiber17Key mmFiber17Expected (mmFiber17RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber17Chunk3_ok
  change (mmRowReverseValid mmFiber17Key mmFiber17Expected (mmFiber17RowAt 6) &&
    mmRowReverseValid mmFiber17Key mmFiber17Expected (mmFiber17RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber17ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber17StateAt 3) (mmFiber17StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber17StateAt 3) (mmFiber17StateAt 7)
    (mmFiber17RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber17Key mmFiber17Expected
        (mmFiber17RowAt 7) (by decide) mmFiber17ReverseRow_7_ok
      simpa [mmFiber17StateAt, mmFiber17RowAt, mmFiber17Rows, listGetD, directRow] using h)

theorem mmFiber17State0_in_close :
    mmFiber17StateAt 0 ∈ closeChainFiber mmWord mmFiber17DirectStates mmFiber17DirectStates.length [mmFiber17StateAt 0] := by
  change mmFiber17StateAt 0 ∈ closeChainFiber mmWord mmFiber17DirectStates 8 [mmFiber17StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber17DirectStates 0 8 [mmFiber17StateAt 0] (mmFiber17StateAt 0) (by simp [closeChainFiber])

theorem mmFiber17State1_in_close :
    mmFiber17StateAt 1 ∈ closeChainFiber mmWord mmFiber17DirectStates mmFiber17DirectStates.length [mmFiber17StateAt 0] := by
  have h0 : mmFiber17StateAt 0 ∈ closeChainFiber mmWord mmFiber17DirectStates 0 [mmFiber17StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber17StateAt 1 ∈ closeChainFiber mmWord mmFiber17DirectStates 1 [mmFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber17DirectStates 0 [mmFiber17StateAt 0]
      (mmFiber17StateAt 0) (mmFiber17StateAt 1) (by decide) h0 (by decide)
      mmFiber17ReverseSingleStep1
  change mmFiber17StateAt 1 ∈ closeChainFiber mmWord mmFiber17DirectStates (1 + 7) [mmFiber17StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber17DirectStates 1 7 [mmFiber17StateAt 0] (mmFiber17StateAt 1) h1

theorem mmFiber17State2_in_close :
    mmFiber17StateAt 2 ∈ closeChainFiber mmWord mmFiber17DirectStates mmFiber17DirectStates.length [mmFiber17StateAt 0] := by
  have h0 : mmFiber17StateAt 0 ∈ closeChainFiber mmWord mmFiber17DirectStates 0 [mmFiber17StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber17StateAt 1 ∈ closeChainFiber mmWord mmFiber17DirectStates 1 [mmFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber17DirectStates 0 [mmFiber17StateAt 0]
      (mmFiber17StateAt 0) (mmFiber17StateAt 1) (by decide) h0 (by decide)
      mmFiber17ReverseSingleStep1
  have h2 : mmFiber17StateAt 2 ∈ closeChainFiber mmWord mmFiber17DirectStates 2 [mmFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber17DirectStates 1 [mmFiber17StateAt 0]
      (mmFiber17StateAt 1) (mmFiber17StateAt 2) (by decide) h1 (by decide)
      mmFiber17ReverseSingleStep2
  change mmFiber17StateAt 2 ∈ closeChainFiber mmWord mmFiber17DirectStates (2 + 6) [mmFiber17StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber17DirectStates 2 6 [mmFiber17StateAt 0] (mmFiber17StateAt 2) h2

theorem mmFiber17State3_in_close :
    mmFiber17StateAt 3 ∈ closeChainFiber mmWord mmFiber17DirectStates mmFiber17DirectStates.length [mmFiber17StateAt 0] := by
  have h0 : mmFiber17StateAt 0 ∈ closeChainFiber mmWord mmFiber17DirectStates 0 [mmFiber17StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber17StateAt 3 ∈ closeChainFiber mmWord mmFiber17DirectStates 1 [mmFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber17DirectStates 0 [mmFiber17StateAt 0]
      (mmFiber17StateAt 0) (mmFiber17StateAt 3) (by decide) h0 (by decide)
      mmFiber17ReverseSingleStep3
  change mmFiber17StateAt 3 ∈ closeChainFiber mmWord mmFiber17DirectStates (1 + 7) [mmFiber17StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber17DirectStates 1 7 [mmFiber17StateAt 0] (mmFiber17StateAt 3) h1

theorem mmFiber17State4_in_close :
    mmFiber17StateAt 4 ∈ closeChainFiber mmWord mmFiber17DirectStates mmFiber17DirectStates.length [mmFiber17StateAt 0] := by
  have h0 : mmFiber17StateAt 0 ∈ closeChainFiber mmWord mmFiber17DirectStates 0 [mmFiber17StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber17StateAt 4 ∈ closeChainFiber mmWord mmFiber17DirectStates 1 [mmFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber17DirectStates 0 [mmFiber17StateAt 0]
      (mmFiber17StateAt 0) (mmFiber17StateAt 4) (by decide) h0 (by decide)
      mmFiber17ReverseSingleStep4
  change mmFiber17StateAt 4 ∈ closeChainFiber mmWord mmFiber17DirectStates (1 + 7) [mmFiber17StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber17DirectStates 1 7 [mmFiber17StateAt 0] (mmFiber17StateAt 4) h1

theorem mmFiber17State5_in_close :
    mmFiber17StateAt 5 ∈ closeChainFiber mmWord mmFiber17DirectStates mmFiber17DirectStates.length [mmFiber17StateAt 0] := by
  have h0 : mmFiber17StateAt 0 ∈ closeChainFiber mmWord mmFiber17DirectStates 0 [mmFiber17StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber17StateAt 1 ∈ closeChainFiber mmWord mmFiber17DirectStates 1 [mmFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber17DirectStates 0 [mmFiber17StateAt 0]
      (mmFiber17StateAt 0) (mmFiber17StateAt 1) (by decide) h0 (by decide)
      mmFiber17ReverseSingleStep1
  have h2 : mmFiber17StateAt 5 ∈ closeChainFiber mmWord mmFiber17DirectStates 2 [mmFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber17DirectStates 1 [mmFiber17StateAt 0]
      (mmFiber17StateAt 1) (mmFiber17StateAt 5) (by decide) h1 (by decide)
      mmFiber17ReverseSingleStep5
  change mmFiber17StateAt 5 ∈ closeChainFiber mmWord mmFiber17DirectStates (2 + 6) [mmFiber17StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber17DirectStates 2 6 [mmFiber17StateAt 0] (mmFiber17StateAt 5) h2

theorem mmFiber17State6_in_close :
    mmFiber17StateAt 6 ∈ closeChainFiber mmWord mmFiber17DirectStates mmFiber17DirectStates.length [mmFiber17StateAt 0] := by
  have h0 : mmFiber17StateAt 0 ∈ closeChainFiber mmWord mmFiber17DirectStates 0 [mmFiber17StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber17StateAt 1 ∈ closeChainFiber mmWord mmFiber17DirectStates 1 [mmFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber17DirectStates 0 [mmFiber17StateAt 0]
      (mmFiber17StateAt 0) (mmFiber17StateAt 1) (by decide) h0 (by decide)
      mmFiber17ReverseSingleStep1
  have h2 : mmFiber17StateAt 2 ∈ closeChainFiber mmWord mmFiber17DirectStates 2 [mmFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber17DirectStates 1 [mmFiber17StateAt 0]
      (mmFiber17StateAt 1) (mmFiber17StateAt 2) (by decide) h1 (by decide)
      mmFiber17ReverseSingleStep2
  have h3 : mmFiber17StateAt 6 ∈ closeChainFiber mmWord mmFiber17DirectStates 3 [mmFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber17DirectStates 2 [mmFiber17StateAt 0]
      (mmFiber17StateAt 2) (mmFiber17StateAt 6) (by decide) h2 (by decide)
      mmFiber17ReverseSingleStep6
  change mmFiber17StateAt 6 ∈ closeChainFiber mmWord mmFiber17DirectStates (3 + 5) [mmFiber17StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber17DirectStates 3 5 [mmFiber17StateAt 0] (mmFiber17StateAt 6) h3

theorem mmFiber17State7_in_close :
    mmFiber17StateAt 7 ∈ closeChainFiber mmWord mmFiber17DirectStates mmFiber17DirectStates.length [mmFiber17StateAt 0] := by
  have h0 : mmFiber17StateAt 0 ∈ closeChainFiber mmWord mmFiber17DirectStates 0 [mmFiber17StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber17StateAt 3 ∈ closeChainFiber mmWord mmFiber17DirectStates 1 [mmFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber17DirectStates 0 [mmFiber17StateAt 0]
      (mmFiber17StateAt 0) (mmFiber17StateAt 3) (by decide) h0 (by decide)
      mmFiber17ReverseSingleStep3
  have h2 : mmFiber17StateAt 7 ∈ closeChainFiber mmWord mmFiber17DirectStates 2 [mmFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber17DirectStates 1 [mmFiber17StateAt 0]
      (mmFiber17StateAt 3) (mmFiber17StateAt 7) (by decide) h1 (by decide)
      mmFiber17ReverseSingleStep7
  change mmFiber17StateAt 7 ∈ closeChainFiber mmWord mmFiber17DirectStates (2 + 6) [mmFiber17StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber17DirectStates 2 6 [mmFiber17StateAt 0] (mmFiber17StateAt 7) h2

theorem mmFiber17DirectConnected :
    chainFiberConnected mmWord mmFiber17DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber17DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber17State0_in_close
  · subst state
    exact mmFiber17State1_in_close
  · subst state
    exact mmFiber17State2_in_close
  · subst state
    exact mmFiber17State3_in_close
  · subst state
    exact mmFiber17State4_in_close
  · subst state
    exact mmFiber17State5_in_close
  · subst state
    exact mmFiber17State6_in_close
  · subst state
    exact mmFiber17State7_in_close
  · cases h
def mmFiber18StateAt (i : Nat) : List TauState :=
  directStates (mmFiber18RowAt i).sourceLeft (mmFiber18RowAt i).sourceRight

def mmFiber18DirectStates : List (List TauState) :=
  [mmFiber18StateAt 0, mmFiber18StateAt 1, mmFiber18StateAt 2, mmFiber18StateAt 3, mmFiber18StateAt 4, mmFiber18StateAt 5, mmFiber18StateAt 6, mmFiber18StateAt 7]

theorem mmFiber18ReverseRow_1_ok :
    mmRowReverseValid mmFiber18Key mmFiber18Expected (mmFiber18RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber18Chunk0_ok
  change (mmRowReverseValid mmFiber18Key mmFiber18Expected (mmFiber18RowAt 0) &&
    mmRowReverseValid mmFiber18Key mmFiber18Expected (mmFiber18RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber18ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber18StateAt 0) (mmFiber18StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber18StateAt 0) (mmFiber18StateAt 1)
    (mmFiber18RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber18Key mmFiber18Expected
        (mmFiber18RowAt 1) (by decide) mmFiber18ReverseRow_1_ok
      simpa [mmFiber18StateAt, mmFiber18RowAt, mmFiber18Rows, listGetD, directRow] using h)

theorem mmFiber18ReverseRow_2_ok :
    mmRowReverseValid mmFiber18Key mmFiber18Expected (mmFiber18RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber18Chunk1_ok
  change (mmRowReverseValid mmFiber18Key mmFiber18Expected (mmFiber18RowAt 2) &&
    mmRowReverseValid mmFiber18Key mmFiber18Expected (mmFiber18RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber18ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber18StateAt 0) (mmFiber18StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber18StateAt 0) (mmFiber18StateAt 2)
    (mmFiber18RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber18Key mmFiber18Expected
        (mmFiber18RowAt 2) (by decide) mmFiber18ReverseRow_2_ok
      simpa [mmFiber18StateAt, mmFiber18RowAt, mmFiber18Rows, listGetD, directRow] using h)

theorem mmFiber18ReverseRow_3_ok :
    mmRowReverseValid mmFiber18Key mmFiber18Expected (mmFiber18RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber18Chunk1_ok
  change (mmRowReverseValid mmFiber18Key mmFiber18Expected (mmFiber18RowAt 2) &&
    mmRowReverseValid mmFiber18Key mmFiber18Expected (mmFiber18RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber18ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber18StateAt 1) (mmFiber18StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber18StateAt 1) (mmFiber18StateAt 3)
    (mmFiber18RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber18Key mmFiber18Expected
        (mmFiber18RowAt 3) (by decide) mmFiber18ReverseRow_3_ok
      simpa [mmFiber18StateAt, mmFiber18RowAt, mmFiber18Rows, listGetD, directRow] using h)

theorem mmFiber18ReverseRow_4_ok :
    mmRowReverseValid mmFiber18Key mmFiber18Expected (mmFiber18RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber18Chunk2_ok
  change (mmRowReverseValid mmFiber18Key mmFiber18Expected (mmFiber18RowAt 4) &&
    mmRowReverseValid mmFiber18Key mmFiber18Expected (mmFiber18RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber18ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber18StateAt 0) (mmFiber18StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber18StateAt 0) (mmFiber18StateAt 4)
    (mmFiber18RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber18Key mmFiber18Expected
        (mmFiber18RowAt 4) (by decide) mmFiber18ReverseRow_4_ok
      simpa [mmFiber18StateAt, mmFiber18RowAt, mmFiber18Rows, listGetD, directRow] using h)

theorem mmFiber18ReverseRow_5_ok :
    mmRowReverseValid mmFiber18Key mmFiber18Expected (mmFiber18RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber18Chunk2_ok
  change (mmRowReverseValid mmFiber18Key mmFiber18Expected (mmFiber18RowAt 4) &&
    mmRowReverseValid mmFiber18Key mmFiber18Expected (mmFiber18RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber18ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber18StateAt 1) (mmFiber18StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber18StateAt 1) (mmFiber18StateAt 5)
    (mmFiber18RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber18Key mmFiber18Expected
        (mmFiber18RowAt 5) (by decide) mmFiber18ReverseRow_5_ok
      simpa [mmFiber18StateAt, mmFiber18RowAt, mmFiber18Rows, listGetD, directRow] using h)

theorem mmFiber18ReverseRow_6_ok :
    mmRowReverseValid mmFiber18Key mmFiber18Expected (mmFiber18RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber18Chunk3_ok
  change (mmRowReverseValid mmFiber18Key mmFiber18Expected (mmFiber18RowAt 6) &&
    mmRowReverseValid mmFiber18Key mmFiber18Expected (mmFiber18RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber18ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber18StateAt 2) (mmFiber18StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber18StateAt 2) (mmFiber18StateAt 6)
    (mmFiber18RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber18Key mmFiber18Expected
        (mmFiber18RowAt 6) (by decide) mmFiber18ReverseRow_6_ok
      simpa [mmFiber18StateAt, mmFiber18RowAt, mmFiber18Rows, listGetD, directRow] using h)

theorem mmFiber18ReverseRow_7_ok :
    mmRowReverseValid mmFiber18Key mmFiber18Expected (mmFiber18RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber18Chunk3_ok
  change (mmRowReverseValid mmFiber18Key mmFiber18Expected (mmFiber18RowAt 6) &&
    mmRowReverseValid mmFiber18Key mmFiber18Expected (mmFiber18RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber18ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber18StateAt 3) (mmFiber18StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber18StateAt 3) (mmFiber18StateAt 7)
    (mmFiber18RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber18Key mmFiber18Expected
        (mmFiber18RowAt 7) (by decide) mmFiber18ReverseRow_7_ok
      simpa [mmFiber18StateAt, mmFiber18RowAt, mmFiber18Rows, listGetD, directRow] using h)

theorem mmFiber18State0_in_close :
    mmFiber18StateAt 0 ∈ closeChainFiber mmWord mmFiber18DirectStates mmFiber18DirectStates.length [mmFiber18StateAt 0] := by
  change mmFiber18StateAt 0 ∈ closeChainFiber mmWord mmFiber18DirectStates 8 [mmFiber18StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber18DirectStates 0 8 [mmFiber18StateAt 0] (mmFiber18StateAt 0) (by simp [closeChainFiber])

theorem mmFiber18State1_in_close :
    mmFiber18StateAt 1 ∈ closeChainFiber mmWord mmFiber18DirectStates mmFiber18DirectStates.length [mmFiber18StateAt 0] := by
  have h0 : mmFiber18StateAt 0 ∈ closeChainFiber mmWord mmFiber18DirectStates 0 [mmFiber18StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber18StateAt 1 ∈ closeChainFiber mmWord mmFiber18DirectStates 1 [mmFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber18DirectStates 0 [mmFiber18StateAt 0]
      (mmFiber18StateAt 0) (mmFiber18StateAt 1) (by decide) h0 (by decide)
      mmFiber18ReverseSingleStep1
  change mmFiber18StateAt 1 ∈ closeChainFiber mmWord mmFiber18DirectStates (1 + 7) [mmFiber18StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber18DirectStates 1 7 [mmFiber18StateAt 0] (mmFiber18StateAt 1) h1

theorem mmFiber18State2_in_close :
    mmFiber18StateAt 2 ∈ closeChainFiber mmWord mmFiber18DirectStates mmFiber18DirectStates.length [mmFiber18StateAt 0] := by
  have h0 : mmFiber18StateAt 0 ∈ closeChainFiber mmWord mmFiber18DirectStates 0 [mmFiber18StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber18StateAt 2 ∈ closeChainFiber mmWord mmFiber18DirectStates 1 [mmFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber18DirectStates 0 [mmFiber18StateAt 0]
      (mmFiber18StateAt 0) (mmFiber18StateAt 2) (by decide) h0 (by decide)
      mmFiber18ReverseSingleStep2
  change mmFiber18StateAt 2 ∈ closeChainFiber mmWord mmFiber18DirectStates (1 + 7) [mmFiber18StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber18DirectStates 1 7 [mmFiber18StateAt 0] (mmFiber18StateAt 2) h1

theorem mmFiber18State3_in_close :
    mmFiber18StateAt 3 ∈ closeChainFiber mmWord mmFiber18DirectStates mmFiber18DirectStates.length [mmFiber18StateAt 0] := by
  have h0 : mmFiber18StateAt 0 ∈ closeChainFiber mmWord mmFiber18DirectStates 0 [mmFiber18StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber18StateAt 1 ∈ closeChainFiber mmWord mmFiber18DirectStates 1 [mmFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber18DirectStates 0 [mmFiber18StateAt 0]
      (mmFiber18StateAt 0) (mmFiber18StateAt 1) (by decide) h0 (by decide)
      mmFiber18ReverseSingleStep1
  have h2 : mmFiber18StateAt 3 ∈ closeChainFiber mmWord mmFiber18DirectStates 2 [mmFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber18DirectStates 1 [mmFiber18StateAt 0]
      (mmFiber18StateAt 1) (mmFiber18StateAt 3) (by decide) h1 (by decide)
      mmFiber18ReverseSingleStep3
  change mmFiber18StateAt 3 ∈ closeChainFiber mmWord mmFiber18DirectStates (2 + 6) [mmFiber18StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber18DirectStates 2 6 [mmFiber18StateAt 0] (mmFiber18StateAt 3) h2

theorem mmFiber18State4_in_close :
    mmFiber18StateAt 4 ∈ closeChainFiber mmWord mmFiber18DirectStates mmFiber18DirectStates.length [mmFiber18StateAt 0] := by
  have h0 : mmFiber18StateAt 0 ∈ closeChainFiber mmWord mmFiber18DirectStates 0 [mmFiber18StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber18StateAt 4 ∈ closeChainFiber mmWord mmFiber18DirectStates 1 [mmFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber18DirectStates 0 [mmFiber18StateAt 0]
      (mmFiber18StateAt 0) (mmFiber18StateAt 4) (by decide) h0 (by decide)
      mmFiber18ReverseSingleStep4
  change mmFiber18StateAt 4 ∈ closeChainFiber mmWord mmFiber18DirectStates (1 + 7) [mmFiber18StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber18DirectStates 1 7 [mmFiber18StateAt 0] (mmFiber18StateAt 4) h1

theorem mmFiber18State5_in_close :
    mmFiber18StateAt 5 ∈ closeChainFiber mmWord mmFiber18DirectStates mmFiber18DirectStates.length [mmFiber18StateAt 0] := by
  have h0 : mmFiber18StateAt 0 ∈ closeChainFiber mmWord mmFiber18DirectStates 0 [mmFiber18StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber18StateAt 1 ∈ closeChainFiber mmWord mmFiber18DirectStates 1 [mmFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber18DirectStates 0 [mmFiber18StateAt 0]
      (mmFiber18StateAt 0) (mmFiber18StateAt 1) (by decide) h0 (by decide)
      mmFiber18ReverseSingleStep1
  have h2 : mmFiber18StateAt 5 ∈ closeChainFiber mmWord mmFiber18DirectStates 2 [mmFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber18DirectStates 1 [mmFiber18StateAt 0]
      (mmFiber18StateAt 1) (mmFiber18StateAt 5) (by decide) h1 (by decide)
      mmFiber18ReverseSingleStep5
  change mmFiber18StateAt 5 ∈ closeChainFiber mmWord mmFiber18DirectStates (2 + 6) [mmFiber18StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber18DirectStates 2 6 [mmFiber18StateAt 0] (mmFiber18StateAt 5) h2

theorem mmFiber18State6_in_close :
    mmFiber18StateAt 6 ∈ closeChainFiber mmWord mmFiber18DirectStates mmFiber18DirectStates.length [mmFiber18StateAt 0] := by
  have h0 : mmFiber18StateAt 0 ∈ closeChainFiber mmWord mmFiber18DirectStates 0 [mmFiber18StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber18StateAt 2 ∈ closeChainFiber mmWord mmFiber18DirectStates 1 [mmFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber18DirectStates 0 [mmFiber18StateAt 0]
      (mmFiber18StateAt 0) (mmFiber18StateAt 2) (by decide) h0 (by decide)
      mmFiber18ReverseSingleStep2
  have h2 : mmFiber18StateAt 6 ∈ closeChainFiber mmWord mmFiber18DirectStates 2 [mmFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber18DirectStates 1 [mmFiber18StateAt 0]
      (mmFiber18StateAt 2) (mmFiber18StateAt 6) (by decide) h1 (by decide)
      mmFiber18ReverseSingleStep6
  change mmFiber18StateAt 6 ∈ closeChainFiber mmWord mmFiber18DirectStates (2 + 6) [mmFiber18StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber18DirectStates 2 6 [mmFiber18StateAt 0] (mmFiber18StateAt 6) h2

theorem mmFiber18State7_in_close :
    mmFiber18StateAt 7 ∈ closeChainFiber mmWord mmFiber18DirectStates mmFiber18DirectStates.length [mmFiber18StateAt 0] := by
  have h0 : mmFiber18StateAt 0 ∈ closeChainFiber mmWord mmFiber18DirectStates 0 [mmFiber18StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber18StateAt 1 ∈ closeChainFiber mmWord mmFiber18DirectStates 1 [mmFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber18DirectStates 0 [mmFiber18StateAt 0]
      (mmFiber18StateAt 0) (mmFiber18StateAt 1) (by decide) h0 (by decide)
      mmFiber18ReverseSingleStep1
  have h2 : mmFiber18StateAt 3 ∈ closeChainFiber mmWord mmFiber18DirectStates 2 [mmFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber18DirectStates 1 [mmFiber18StateAt 0]
      (mmFiber18StateAt 1) (mmFiber18StateAt 3) (by decide) h1 (by decide)
      mmFiber18ReverseSingleStep3
  have h3 : mmFiber18StateAt 7 ∈ closeChainFiber mmWord mmFiber18DirectStates 3 [mmFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber18DirectStates 2 [mmFiber18StateAt 0]
      (mmFiber18StateAt 3) (mmFiber18StateAt 7) (by decide) h2 (by decide)
      mmFiber18ReverseSingleStep7
  change mmFiber18StateAt 7 ∈ closeChainFiber mmWord mmFiber18DirectStates (3 + 5) [mmFiber18StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber18DirectStates 3 5 [mmFiber18StateAt 0] (mmFiber18StateAt 7) h3

theorem mmFiber18DirectConnected :
    chainFiberConnected mmWord mmFiber18DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber18DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber18State0_in_close
  · subst state
    exact mmFiber18State1_in_close
  · subst state
    exact mmFiber18State2_in_close
  · subst state
    exact mmFiber18State3_in_close
  · subst state
    exact mmFiber18State4_in_close
  · subst state
    exact mmFiber18State5_in_close
  · subst state
    exact mmFiber18State6_in_close
  · subst state
    exact mmFiber18State7_in_close
  · cases h
def mmFiber22StateAt (i : Nat) : List TauState :=
  directStates (mmFiber22RowAt i).sourceLeft (mmFiber22RowAt i).sourceRight

def mmFiber22DirectStates : List (List TauState) :=
  [mmFiber22StateAt 0, mmFiber22StateAt 1, mmFiber22StateAt 2, mmFiber22StateAt 3, mmFiber22StateAt 4, mmFiber22StateAt 5, mmFiber22StateAt 6, mmFiber22StateAt 7]

theorem mmFiber22ReverseRow_1_ok :
    mmRowReverseValid mmFiber22Key mmFiber22Expected (mmFiber22RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber22Chunk0_ok
  change (mmRowReverseValid mmFiber22Key mmFiber22Expected (mmFiber22RowAt 0) &&
    mmRowReverseValid mmFiber22Key mmFiber22Expected (mmFiber22RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber22ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber22StateAt 0) (mmFiber22StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber22StateAt 0) (mmFiber22StateAt 1)
    (mmFiber22RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber22Key mmFiber22Expected
        (mmFiber22RowAt 1) (by decide) mmFiber22ReverseRow_1_ok
      simpa [mmFiber22StateAt, mmFiber22RowAt, mmFiber22Rows, listGetD, directRow] using h)

theorem mmFiber22ReverseRow_2_ok :
    mmRowReverseValid mmFiber22Key mmFiber22Expected (mmFiber22RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber22Chunk1_ok
  change (mmRowReverseValid mmFiber22Key mmFiber22Expected (mmFiber22RowAt 2) &&
    mmRowReverseValid mmFiber22Key mmFiber22Expected (mmFiber22RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber22ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber22StateAt 0) (mmFiber22StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber22StateAt 0) (mmFiber22StateAt 2)
    (mmFiber22RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber22Key mmFiber22Expected
        (mmFiber22RowAt 2) (by decide) mmFiber22ReverseRow_2_ok
      simpa [mmFiber22StateAt, mmFiber22RowAt, mmFiber22Rows, listGetD, directRow] using h)

theorem mmFiber22ReverseRow_3_ok :
    mmRowReverseValid mmFiber22Key mmFiber22Expected (mmFiber22RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber22Chunk1_ok
  change (mmRowReverseValid mmFiber22Key mmFiber22Expected (mmFiber22RowAt 2) &&
    mmRowReverseValid mmFiber22Key mmFiber22Expected (mmFiber22RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber22ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber22StateAt 1) (mmFiber22StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber22StateAt 1) (mmFiber22StateAt 3)
    (mmFiber22RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber22Key mmFiber22Expected
        (mmFiber22RowAt 3) (by decide) mmFiber22ReverseRow_3_ok
      simpa [mmFiber22StateAt, mmFiber22RowAt, mmFiber22Rows, listGetD, directRow] using h)

theorem mmFiber22ReverseRow_4_ok :
    mmRowReverseValid mmFiber22Key mmFiber22Expected (mmFiber22RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber22Chunk2_ok
  change (mmRowReverseValid mmFiber22Key mmFiber22Expected (mmFiber22RowAt 4) &&
    mmRowReverseValid mmFiber22Key mmFiber22Expected (mmFiber22RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber22ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber22StateAt 0) (mmFiber22StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber22StateAt 0) (mmFiber22StateAt 4)
    (mmFiber22RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber22Key mmFiber22Expected
        (mmFiber22RowAt 4) (by decide) mmFiber22ReverseRow_4_ok
      simpa [mmFiber22StateAt, mmFiber22RowAt, mmFiber22Rows, listGetD, directRow] using h)

theorem mmFiber22ReverseRow_5_ok :
    mmRowReverseValid mmFiber22Key mmFiber22Expected (mmFiber22RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber22Chunk2_ok
  change (mmRowReverseValid mmFiber22Key mmFiber22Expected (mmFiber22RowAt 4) &&
    mmRowReverseValid mmFiber22Key mmFiber22Expected (mmFiber22RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber22ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber22StateAt 1) (mmFiber22StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber22StateAt 1) (mmFiber22StateAt 5)
    (mmFiber22RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber22Key mmFiber22Expected
        (mmFiber22RowAt 5) (by decide) mmFiber22ReverseRow_5_ok
      simpa [mmFiber22StateAt, mmFiber22RowAt, mmFiber22Rows, listGetD, directRow] using h)

theorem mmFiber22ReverseRow_6_ok :
    mmRowReverseValid mmFiber22Key mmFiber22Expected (mmFiber22RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber22Chunk3_ok
  change (mmRowReverseValid mmFiber22Key mmFiber22Expected (mmFiber22RowAt 6) &&
    mmRowReverseValid mmFiber22Key mmFiber22Expected (mmFiber22RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber22ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber22StateAt 2) (mmFiber22StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber22StateAt 2) (mmFiber22StateAt 6)
    (mmFiber22RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber22Key mmFiber22Expected
        (mmFiber22RowAt 6) (by decide) mmFiber22ReverseRow_6_ok
      simpa [mmFiber22StateAt, mmFiber22RowAt, mmFiber22Rows, listGetD, directRow] using h)

theorem mmFiber22ReverseRow_7_ok :
    mmRowReverseValid mmFiber22Key mmFiber22Expected (mmFiber22RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber22Chunk3_ok
  change (mmRowReverseValid mmFiber22Key mmFiber22Expected (mmFiber22RowAt 6) &&
    mmRowReverseValid mmFiber22Key mmFiber22Expected (mmFiber22RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber22ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber22StateAt 3) (mmFiber22StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber22StateAt 3) (mmFiber22StateAt 7)
    (mmFiber22RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber22Key mmFiber22Expected
        (mmFiber22RowAt 7) (by decide) mmFiber22ReverseRow_7_ok
      simpa [mmFiber22StateAt, mmFiber22RowAt, mmFiber22Rows, listGetD, directRow] using h)

theorem mmFiber22State0_in_close :
    mmFiber22StateAt 0 ∈ closeChainFiber mmWord mmFiber22DirectStates mmFiber22DirectStates.length [mmFiber22StateAt 0] := by
  change mmFiber22StateAt 0 ∈ closeChainFiber mmWord mmFiber22DirectStates 8 [mmFiber22StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber22DirectStates 0 8 [mmFiber22StateAt 0] (mmFiber22StateAt 0) (by simp [closeChainFiber])

theorem mmFiber22State1_in_close :
    mmFiber22StateAt 1 ∈ closeChainFiber mmWord mmFiber22DirectStates mmFiber22DirectStates.length [mmFiber22StateAt 0] := by
  have h0 : mmFiber22StateAt 0 ∈ closeChainFiber mmWord mmFiber22DirectStates 0 [mmFiber22StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber22StateAt 1 ∈ closeChainFiber mmWord mmFiber22DirectStates 1 [mmFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber22DirectStates 0 [mmFiber22StateAt 0]
      (mmFiber22StateAt 0) (mmFiber22StateAt 1) (by decide) h0 (by decide)
      mmFiber22ReverseSingleStep1
  change mmFiber22StateAt 1 ∈ closeChainFiber mmWord mmFiber22DirectStates (1 + 7) [mmFiber22StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber22DirectStates 1 7 [mmFiber22StateAt 0] (mmFiber22StateAt 1) h1

theorem mmFiber22State2_in_close :
    mmFiber22StateAt 2 ∈ closeChainFiber mmWord mmFiber22DirectStates mmFiber22DirectStates.length [mmFiber22StateAt 0] := by
  have h0 : mmFiber22StateAt 0 ∈ closeChainFiber mmWord mmFiber22DirectStates 0 [mmFiber22StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber22StateAt 2 ∈ closeChainFiber mmWord mmFiber22DirectStates 1 [mmFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber22DirectStates 0 [mmFiber22StateAt 0]
      (mmFiber22StateAt 0) (mmFiber22StateAt 2) (by decide) h0 (by decide)
      mmFiber22ReverseSingleStep2
  change mmFiber22StateAt 2 ∈ closeChainFiber mmWord mmFiber22DirectStates (1 + 7) [mmFiber22StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber22DirectStates 1 7 [mmFiber22StateAt 0] (mmFiber22StateAt 2) h1

theorem mmFiber22State3_in_close :
    mmFiber22StateAt 3 ∈ closeChainFiber mmWord mmFiber22DirectStates mmFiber22DirectStates.length [mmFiber22StateAt 0] := by
  have h0 : mmFiber22StateAt 0 ∈ closeChainFiber mmWord mmFiber22DirectStates 0 [mmFiber22StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber22StateAt 1 ∈ closeChainFiber mmWord mmFiber22DirectStates 1 [mmFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber22DirectStates 0 [mmFiber22StateAt 0]
      (mmFiber22StateAt 0) (mmFiber22StateAt 1) (by decide) h0 (by decide)
      mmFiber22ReverseSingleStep1
  have h2 : mmFiber22StateAt 3 ∈ closeChainFiber mmWord mmFiber22DirectStates 2 [mmFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber22DirectStates 1 [mmFiber22StateAt 0]
      (mmFiber22StateAt 1) (mmFiber22StateAt 3) (by decide) h1 (by decide)
      mmFiber22ReverseSingleStep3
  change mmFiber22StateAt 3 ∈ closeChainFiber mmWord mmFiber22DirectStates (2 + 6) [mmFiber22StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber22DirectStates 2 6 [mmFiber22StateAt 0] (mmFiber22StateAt 3) h2

theorem mmFiber22State4_in_close :
    mmFiber22StateAt 4 ∈ closeChainFiber mmWord mmFiber22DirectStates mmFiber22DirectStates.length [mmFiber22StateAt 0] := by
  have h0 : mmFiber22StateAt 0 ∈ closeChainFiber mmWord mmFiber22DirectStates 0 [mmFiber22StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber22StateAt 4 ∈ closeChainFiber mmWord mmFiber22DirectStates 1 [mmFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber22DirectStates 0 [mmFiber22StateAt 0]
      (mmFiber22StateAt 0) (mmFiber22StateAt 4) (by decide) h0 (by decide)
      mmFiber22ReverseSingleStep4
  change mmFiber22StateAt 4 ∈ closeChainFiber mmWord mmFiber22DirectStates (1 + 7) [mmFiber22StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber22DirectStates 1 7 [mmFiber22StateAt 0] (mmFiber22StateAt 4) h1

theorem mmFiber22State5_in_close :
    mmFiber22StateAt 5 ∈ closeChainFiber mmWord mmFiber22DirectStates mmFiber22DirectStates.length [mmFiber22StateAt 0] := by
  have h0 : mmFiber22StateAt 0 ∈ closeChainFiber mmWord mmFiber22DirectStates 0 [mmFiber22StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber22StateAt 1 ∈ closeChainFiber mmWord mmFiber22DirectStates 1 [mmFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber22DirectStates 0 [mmFiber22StateAt 0]
      (mmFiber22StateAt 0) (mmFiber22StateAt 1) (by decide) h0 (by decide)
      mmFiber22ReverseSingleStep1
  have h2 : mmFiber22StateAt 5 ∈ closeChainFiber mmWord mmFiber22DirectStates 2 [mmFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber22DirectStates 1 [mmFiber22StateAt 0]
      (mmFiber22StateAt 1) (mmFiber22StateAt 5) (by decide) h1 (by decide)
      mmFiber22ReverseSingleStep5
  change mmFiber22StateAt 5 ∈ closeChainFiber mmWord mmFiber22DirectStates (2 + 6) [mmFiber22StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber22DirectStates 2 6 [mmFiber22StateAt 0] (mmFiber22StateAt 5) h2

theorem mmFiber22State6_in_close :
    mmFiber22StateAt 6 ∈ closeChainFiber mmWord mmFiber22DirectStates mmFiber22DirectStates.length [mmFiber22StateAt 0] := by
  have h0 : mmFiber22StateAt 0 ∈ closeChainFiber mmWord mmFiber22DirectStates 0 [mmFiber22StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber22StateAt 2 ∈ closeChainFiber mmWord mmFiber22DirectStates 1 [mmFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber22DirectStates 0 [mmFiber22StateAt 0]
      (mmFiber22StateAt 0) (mmFiber22StateAt 2) (by decide) h0 (by decide)
      mmFiber22ReverseSingleStep2
  have h2 : mmFiber22StateAt 6 ∈ closeChainFiber mmWord mmFiber22DirectStates 2 [mmFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber22DirectStates 1 [mmFiber22StateAt 0]
      (mmFiber22StateAt 2) (mmFiber22StateAt 6) (by decide) h1 (by decide)
      mmFiber22ReverseSingleStep6
  change mmFiber22StateAt 6 ∈ closeChainFiber mmWord mmFiber22DirectStates (2 + 6) [mmFiber22StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber22DirectStates 2 6 [mmFiber22StateAt 0] (mmFiber22StateAt 6) h2

theorem mmFiber22State7_in_close :
    mmFiber22StateAt 7 ∈ closeChainFiber mmWord mmFiber22DirectStates mmFiber22DirectStates.length [mmFiber22StateAt 0] := by
  have h0 : mmFiber22StateAt 0 ∈ closeChainFiber mmWord mmFiber22DirectStates 0 [mmFiber22StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber22StateAt 1 ∈ closeChainFiber mmWord mmFiber22DirectStates 1 [mmFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber22DirectStates 0 [mmFiber22StateAt 0]
      (mmFiber22StateAt 0) (mmFiber22StateAt 1) (by decide) h0 (by decide)
      mmFiber22ReverseSingleStep1
  have h2 : mmFiber22StateAt 3 ∈ closeChainFiber mmWord mmFiber22DirectStates 2 [mmFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber22DirectStates 1 [mmFiber22StateAt 0]
      (mmFiber22StateAt 1) (mmFiber22StateAt 3) (by decide) h1 (by decide)
      mmFiber22ReverseSingleStep3
  have h3 : mmFiber22StateAt 7 ∈ closeChainFiber mmWord mmFiber22DirectStates 3 [mmFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber22DirectStates 2 [mmFiber22StateAt 0]
      (mmFiber22StateAt 3) (mmFiber22StateAt 7) (by decide) h2 (by decide)
      mmFiber22ReverseSingleStep7
  change mmFiber22StateAt 7 ∈ closeChainFiber mmWord mmFiber22DirectStates (3 + 5) [mmFiber22StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber22DirectStates 3 5 [mmFiber22StateAt 0] (mmFiber22StateAt 7) h3

theorem mmFiber22DirectConnected :
    chainFiberConnected mmWord mmFiber22DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber22DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber22State0_in_close
  · subst state
    exact mmFiber22State1_in_close
  · subst state
    exact mmFiber22State2_in_close
  · subst state
    exact mmFiber22State3_in_close
  · subst state
    exact mmFiber22State4_in_close
  · subst state
    exact mmFiber22State5_in_close
  · subst state
    exact mmFiber22State6_in_close
  · subst state
    exact mmFiber22State7_in_close
  · cases h
def mmFiber23StateAt (i : Nat) : List TauState :=
  directStates (mmFiber23RowAt i).sourceLeft (mmFiber23RowAt i).sourceRight

def mmFiber23DirectStates : List (List TauState) :=
  [mmFiber23StateAt 0, mmFiber23StateAt 1, mmFiber23StateAt 2, mmFiber23StateAt 3, mmFiber23StateAt 4, mmFiber23StateAt 5, mmFiber23StateAt 6, mmFiber23StateAt 7]

theorem mmFiber23ReverseRow_1_ok :
    mmRowReverseValid mmFiber23Key mmFiber23Expected (mmFiber23RowAt 1) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber23Chunk0_ok
  change (mmRowReverseValid mmFiber23Key mmFiber23Expected (mmFiber23RowAt 0) &&
    mmRowReverseValid mmFiber23Key mmFiber23Expected (mmFiber23RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber23ReverseSingleStep1 :
    chainSingleKempeStep mmWord (mmFiber23StateAt 0) (mmFiber23StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber23StateAt 0) (mmFiber23StateAt 1)
    (mmFiber23RowAt 1).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber23Key mmFiber23Expected
        (mmFiber23RowAt 1) (by decide) mmFiber23ReverseRow_1_ok
      simpa [mmFiber23StateAt, mmFiber23RowAt, mmFiber23Rows, listGetD, directRow] using h)

theorem mmFiber23ReverseRow_2_ok :
    mmRowReverseValid mmFiber23Key mmFiber23Expected (mmFiber23RowAt 2) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber23Chunk1_ok
  change (mmRowReverseValid mmFiber23Key mmFiber23Expected (mmFiber23RowAt 2) &&
    mmRowReverseValid mmFiber23Key mmFiber23Expected (mmFiber23RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber23ReverseSingleStep2 :
    chainSingleKempeStep mmWord (mmFiber23StateAt 1) (mmFiber23StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber23StateAt 1) (mmFiber23StateAt 2)
    (mmFiber23RowAt 2).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber23Key mmFiber23Expected
        (mmFiber23RowAt 2) (by decide) mmFiber23ReverseRow_2_ok
      simpa [mmFiber23StateAt, mmFiber23RowAt, mmFiber23Rows, listGetD, directRow] using h)

theorem mmFiber23ReverseRow_3_ok :
    mmRowReverseValid mmFiber23Key mmFiber23Expected (mmFiber23RowAt 3) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber23Chunk1_ok
  change (mmRowReverseValid mmFiber23Key mmFiber23Expected (mmFiber23RowAt 2) &&
    mmRowReverseValid mmFiber23Key mmFiber23Expected (mmFiber23RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber23ReverseSingleStep3 :
    chainSingleKempeStep mmWord (mmFiber23StateAt 0) (mmFiber23StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber23StateAt 0) (mmFiber23StateAt 3)
    (mmFiber23RowAt 3).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber23Key mmFiber23Expected
        (mmFiber23RowAt 3) (by decide) mmFiber23ReverseRow_3_ok
      simpa [mmFiber23StateAt, mmFiber23RowAt, mmFiber23Rows, listGetD, directRow] using h)

theorem mmFiber23ReverseRow_4_ok :
    mmRowReverseValid mmFiber23Key mmFiber23Expected (mmFiber23RowAt 4) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber23Chunk2_ok
  change (mmRowReverseValid mmFiber23Key mmFiber23Expected (mmFiber23RowAt 4) &&
    mmRowReverseValid mmFiber23Key mmFiber23Expected (mmFiber23RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber23ReverseSingleStep4 :
    chainSingleKempeStep mmWord (mmFiber23StateAt 0) (mmFiber23StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber23StateAt 0) (mmFiber23StateAt 4)
    (mmFiber23RowAt 4).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber23Key mmFiber23Expected
        (mmFiber23RowAt 4) (by decide) mmFiber23ReverseRow_4_ok
      simpa [mmFiber23StateAt, mmFiber23RowAt, mmFiber23Rows, listGetD, directRow] using h)

theorem mmFiber23ReverseRow_5_ok :
    mmRowReverseValid mmFiber23Key mmFiber23Expected (mmFiber23RowAt 5) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber23Chunk2_ok
  change (mmRowReverseValid mmFiber23Key mmFiber23Expected (mmFiber23RowAt 4) &&
    mmRowReverseValid mmFiber23Key mmFiber23Expected (mmFiber23RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber23ReverseSingleStep5 :
    chainSingleKempeStep mmWord (mmFiber23StateAt 1) (mmFiber23StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber23StateAt 1) (mmFiber23StateAt 5)
    (mmFiber23RowAt 5).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber23Key mmFiber23Expected
        (mmFiber23RowAt 5) (by decide) mmFiber23ReverseRow_5_ok
      simpa [mmFiber23StateAt, mmFiber23RowAt, mmFiber23Rows, listGetD, directRow] using h)

theorem mmFiber23ReverseRow_6_ok :
    mmRowReverseValid mmFiber23Key mmFiber23Expected (mmFiber23RowAt 6) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber23Chunk3_ok
  change (mmRowReverseValid mmFiber23Key mmFiber23Expected (mmFiber23RowAt 6) &&
    mmRowReverseValid mmFiber23Key mmFiber23Expected (mmFiber23RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mmFiber23ReverseSingleStep6 :
    chainSingleKempeStep mmWord (mmFiber23StateAt 2) (mmFiber23StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber23StateAt 2) (mmFiber23StateAt 6)
    (mmFiber23RowAt 6).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber23Key mmFiber23Expected
        (mmFiber23RowAt 6) (by decide) mmFiber23ReverseRow_6_ok
      simpa [mmFiber23StateAt, mmFiber23RowAt, mmFiber23Rows, listGetD, directRow] using h)

theorem mmFiber23ReverseRow_7_ok :
    mmRowReverseValid mmFiber23Key mmFiber23Expected (mmFiber23RowAt 7) = true := by
  have h := GoertzelLemma818MirrorMirrorReverseAudit.mmReverseFiber23Chunk3_ok
  change (mmRowReverseValid mmFiber23Key mmFiber23Expected (mmFiber23RowAt 6) &&
    mmRowReverseValid mmFiber23Key mmFiber23Expected (mmFiber23RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mmFiber23ReverseSingleStep7 :
    chainSingleKempeStep mmWord (mmFiber23StateAt 3) (mmFiber23StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mmWord (mmFiber23StateAt 3) (mmFiber23StateAt 7)
    (mmFiber23RowAt 7).move (by decide) (by decide) (by
      have h := mmRowReverseValid_step_of_ne mmFiber23Key mmFiber23Expected
        (mmFiber23RowAt 7) (by decide) mmFiber23ReverseRow_7_ok
      simpa [mmFiber23StateAt, mmFiber23RowAt, mmFiber23Rows, listGetD, directRow] using h)

theorem mmFiber23State0_in_close :
    mmFiber23StateAt 0 ∈ closeChainFiber mmWord mmFiber23DirectStates mmFiber23DirectStates.length [mmFiber23StateAt 0] := by
  change mmFiber23StateAt 0 ∈ closeChainFiber mmWord mmFiber23DirectStates 8 [mmFiber23StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber23DirectStates 0 8 [mmFiber23StateAt 0] (mmFiber23StateAt 0) (by simp [closeChainFiber])

theorem mmFiber23State1_in_close :
    mmFiber23StateAt 1 ∈ closeChainFiber mmWord mmFiber23DirectStates mmFiber23DirectStates.length [mmFiber23StateAt 0] := by
  have h0 : mmFiber23StateAt 0 ∈ closeChainFiber mmWord mmFiber23DirectStates 0 [mmFiber23StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber23StateAt 1 ∈ closeChainFiber mmWord mmFiber23DirectStates 1 [mmFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber23DirectStates 0 [mmFiber23StateAt 0]
      (mmFiber23StateAt 0) (mmFiber23StateAt 1) (by decide) h0 (by decide)
      mmFiber23ReverseSingleStep1
  change mmFiber23StateAt 1 ∈ closeChainFiber mmWord mmFiber23DirectStates (1 + 7) [mmFiber23StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber23DirectStates 1 7 [mmFiber23StateAt 0] (mmFiber23StateAt 1) h1

theorem mmFiber23State2_in_close :
    mmFiber23StateAt 2 ∈ closeChainFiber mmWord mmFiber23DirectStates mmFiber23DirectStates.length [mmFiber23StateAt 0] := by
  have h0 : mmFiber23StateAt 0 ∈ closeChainFiber mmWord mmFiber23DirectStates 0 [mmFiber23StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber23StateAt 1 ∈ closeChainFiber mmWord mmFiber23DirectStates 1 [mmFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber23DirectStates 0 [mmFiber23StateAt 0]
      (mmFiber23StateAt 0) (mmFiber23StateAt 1) (by decide) h0 (by decide)
      mmFiber23ReverseSingleStep1
  have h2 : mmFiber23StateAt 2 ∈ closeChainFiber mmWord mmFiber23DirectStates 2 [mmFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber23DirectStates 1 [mmFiber23StateAt 0]
      (mmFiber23StateAt 1) (mmFiber23StateAt 2) (by decide) h1 (by decide)
      mmFiber23ReverseSingleStep2
  change mmFiber23StateAt 2 ∈ closeChainFiber mmWord mmFiber23DirectStates (2 + 6) [mmFiber23StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber23DirectStates 2 6 [mmFiber23StateAt 0] (mmFiber23StateAt 2) h2

theorem mmFiber23State3_in_close :
    mmFiber23StateAt 3 ∈ closeChainFiber mmWord mmFiber23DirectStates mmFiber23DirectStates.length [mmFiber23StateAt 0] := by
  have h0 : mmFiber23StateAt 0 ∈ closeChainFiber mmWord mmFiber23DirectStates 0 [mmFiber23StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber23StateAt 3 ∈ closeChainFiber mmWord mmFiber23DirectStates 1 [mmFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber23DirectStates 0 [mmFiber23StateAt 0]
      (mmFiber23StateAt 0) (mmFiber23StateAt 3) (by decide) h0 (by decide)
      mmFiber23ReverseSingleStep3
  change mmFiber23StateAt 3 ∈ closeChainFiber mmWord mmFiber23DirectStates (1 + 7) [mmFiber23StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber23DirectStates 1 7 [mmFiber23StateAt 0] (mmFiber23StateAt 3) h1

theorem mmFiber23State4_in_close :
    mmFiber23StateAt 4 ∈ closeChainFiber mmWord mmFiber23DirectStates mmFiber23DirectStates.length [mmFiber23StateAt 0] := by
  have h0 : mmFiber23StateAt 0 ∈ closeChainFiber mmWord mmFiber23DirectStates 0 [mmFiber23StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber23StateAt 4 ∈ closeChainFiber mmWord mmFiber23DirectStates 1 [mmFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber23DirectStates 0 [mmFiber23StateAt 0]
      (mmFiber23StateAt 0) (mmFiber23StateAt 4) (by decide) h0 (by decide)
      mmFiber23ReverseSingleStep4
  change mmFiber23StateAt 4 ∈ closeChainFiber mmWord mmFiber23DirectStates (1 + 7) [mmFiber23StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber23DirectStates 1 7 [mmFiber23StateAt 0] (mmFiber23StateAt 4) h1

theorem mmFiber23State5_in_close :
    mmFiber23StateAt 5 ∈ closeChainFiber mmWord mmFiber23DirectStates mmFiber23DirectStates.length [mmFiber23StateAt 0] := by
  have h0 : mmFiber23StateAt 0 ∈ closeChainFiber mmWord mmFiber23DirectStates 0 [mmFiber23StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber23StateAt 1 ∈ closeChainFiber mmWord mmFiber23DirectStates 1 [mmFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber23DirectStates 0 [mmFiber23StateAt 0]
      (mmFiber23StateAt 0) (mmFiber23StateAt 1) (by decide) h0 (by decide)
      mmFiber23ReverseSingleStep1
  have h2 : mmFiber23StateAt 5 ∈ closeChainFiber mmWord mmFiber23DirectStates 2 [mmFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber23DirectStates 1 [mmFiber23StateAt 0]
      (mmFiber23StateAt 1) (mmFiber23StateAt 5) (by decide) h1 (by decide)
      mmFiber23ReverseSingleStep5
  change mmFiber23StateAt 5 ∈ closeChainFiber mmWord mmFiber23DirectStates (2 + 6) [mmFiber23StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber23DirectStates 2 6 [mmFiber23StateAt 0] (mmFiber23StateAt 5) h2

theorem mmFiber23State6_in_close :
    mmFiber23StateAt 6 ∈ closeChainFiber mmWord mmFiber23DirectStates mmFiber23DirectStates.length [mmFiber23StateAt 0] := by
  have h0 : mmFiber23StateAt 0 ∈ closeChainFiber mmWord mmFiber23DirectStates 0 [mmFiber23StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber23StateAt 1 ∈ closeChainFiber mmWord mmFiber23DirectStates 1 [mmFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber23DirectStates 0 [mmFiber23StateAt 0]
      (mmFiber23StateAt 0) (mmFiber23StateAt 1) (by decide) h0 (by decide)
      mmFiber23ReverseSingleStep1
  have h2 : mmFiber23StateAt 2 ∈ closeChainFiber mmWord mmFiber23DirectStates 2 [mmFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber23DirectStates 1 [mmFiber23StateAt 0]
      (mmFiber23StateAt 1) (mmFiber23StateAt 2) (by decide) h1 (by decide)
      mmFiber23ReverseSingleStep2
  have h3 : mmFiber23StateAt 6 ∈ closeChainFiber mmWord mmFiber23DirectStates 3 [mmFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber23DirectStates 2 [mmFiber23StateAt 0]
      (mmFiber23StateAt 2) (mmFiber23StateAt 6) (by decide) h2 (by decide)
      mmFiber23ReverseSingleStep6
  change mmFiber23StateAt 6 ∈ closeChainFiber mmWord mmFiber23DirectStates (3 + 5) [mmFiber23StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber23DirectStates 3 5 [mmFiber23StateAt 0] (mmFiber23StateAt 6) h3

theorem mmFiber23State7_in_close :
    mmFiber23StateAt 7 ∈ closeChainFiber mmWord mmFiber23DirectStates mmFiber23DirectStates.length [mmFiber23StateAt 0] := by
  have h0 : mmFiber23StateAt 0 ∈ closeChainFiber mmWord mmFiber23DirectStates 0 [mmFiber23StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mmFiber23StateAt 3 ∈ closeChainFiber mmWord mmFiber23DirectStates 1 [mmFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber23DirectStates 0 [mmFiber23StateAt 0]
      (mmFiber23StateAt 0) (mmFiber23StateAt 3) (by decide) h0 (by decide)
      mmFiber23ReverseSingleStep3
  have h2 : mmFiber23StateAt 7 ∈ closeChainFiber mmWord mmFiber23DirectStates 2 [mmFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mmWord mmFiber23DirectStates 1 [mmFiber23StateAt 0]
      (mmFiber23StateAt 3) (mmFiber23StateAt 7) (by decide) h1 (by decide)
      mmFiber23ReverseSingleStep7
  change mmFiber23StateAt 7 ∈ closeChainFiber mmWord mmFiber23DirectStates (2 + 6) [mmFiber23StateAt 0]
  exact closeChainFiber_mem_mono_add mmWord mmFiber23DirectStates 2 6 [mmFiber23StateAt 0] (mmFiber23StateAt 7) h2

theorem mmFiber23DirectConnected :
    chainFiberConnected mmWord mmFiber23DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mmFiber23DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · subst state
    exact mmFiber23State0_in_close
  · subst state
    exact mmFiber23State1_in_close
  · subst state
    exact mmFiber23State2_in_close
  · subst state
    exact mmFiber23State3_in_close
  · subst state
    exact mmFiber23State4_in_close
  · subst state
    exact mmFiber23State5_in_close
  · subst state
    exact mmFiber23State6_in_close
  · subst state
    exact mmFiber23State7_in_close
  · cases h
end GoertzelLemma818LengthTwoMMBridge

end Mettapedia.GraphTheory.FourColor
