import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for size-16 `mirror,normal` length-two fibers, group 4

This module proves direct connectedness for generated `mirror,normal` size-16 fibers from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMTBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorTauCertificate
open GoertzelLemma818MirrorTauReverseAudit

def mtFiber57StateAt (i : Nat) : List TauState :=
  directStates (mtFiber57RowAt i).sourceLeft (mtFiber57RowAt i).sourceRight

def mtFiber57DirectStates : List (List TauState) :=
  [mtFiber57StateAt 0, mtFiber57StateAt 1, mtFiber57StateAt 2, mtFiber57StateAt 3, mtFiber57StateAt 4, mtFiber57StateAt 5, mtFiber57StateAt 6, mtFiber57StateAt 7, mtFiber57StateAt 8, mtFiber57StateAt 9, mtFiber57StateAt 10, mtFiber57StateAt 11, mtFiber57StateAt 12, mtFiber57StateAt 13, mtFiber57StateAt 14, mtFiber57StateAt 15]

theorem mtFiber57ReverseRow_1_ok :
    mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber57Chunk0_ok
  change (mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 0) &&
    mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber57ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber57StateAt 0) (mtFiber57StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber57StateAt 0) (mtFiber57StateAt 1)
    (mtFiber57RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber57Key mtFiber57Expected
        (mtFiber57RowAt 1) (by decide) mtFiber57ReverseRow_1_ok
      simpa [mtFiber57StateAt, mtFiber57RowAt, mtFiber57Rows, listGetD, directRow] using h)

theorem mtFiber57ReverseRow_2_ok :
    mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber57Chunk1_ok
  change (mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 2) &&
    mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber57ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber57StateAt 1) (mtFiber57StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber57StateAt 1) (mtFiber57StateAt 2)
    (mtFiber57RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber57Key mtFiber57Expected
        (mtFiber57RowAt 2) (by decide) mtFiber57ReverseRow_2_ok
      simpa [mtFiber57StateAt, mtFiber57RowAt, mtFiber57Rows, listGetD, directRow] using h)

theorem mtFiber57ReverseRow_3_ok :
    mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber57Chunk1_ok
  change (mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 2) &&
    mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber57ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber57StateAt 0) (mtFiber57StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber57StateAt 0) (mtFiber57StateAt 3)
    (mtFiber57RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber57Key mtFiber57Expected
        (mtFiber57RowAt 3) (by decide) mtFiber57ReverseRow_3_ok
      simpa [mtFiber57StateAt, mtFiber57RowAt, mtFiber57Rows, listGetD, directRow] using h)

theorem mtFiber57ReverseRow_4_ok :
    mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber57Chunk2_ok
  change (mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 4) &&
    mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber57ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber57StateAt 0) (mtFiber57StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber57StateAt 0) (mtFiber57StateAt 4)
    (mtFiber57RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber57Key mtFiber57Expected
        (mtFiber57RowAt 4) (by decide) mtFiber57ReverseRow_4_ok
      simpa [mtFiber57StateAt, mtFiber57RowAt, mtFiber57Rows, listGetD, directRow] using h)

theorem mtFiber57ReverseRow_5_ok :
    mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber57Chunk2_ok
  change (mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 4) &&
    mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber57ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber57StateAt 1) (mtFiber57StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber57StateAt 1) (mtFiber57StateAt 5)
    (mtFiber57RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber57Key mtFiber57Expected
        (mtFiber57RowAt 5) (by decide) mtFiber57ReverseRow_5_ok
      simpa [mtFiber57StateAt, mtFiber57RowAt, mtFiber57Rows, listGetD, directRow] using h)

theorem mtFiber57ReverseRow_6_ok :
    mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber57Chunk3_ok
  change (mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 6) &&
    mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber57ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber57StateAt 2) (mtFiber57StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber57StateAt 2) (mtFiber57StateAt 6)
    (mtFiber57RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber57Key mtFiber57Expected
        (mtFiber57RowAt 6) (by decide) mtFiber57ReverseRow_6_ok
      simpa [mtFiber57StateAt, mtFiber57RowAt, mtFiber57Rows, listGetD, directRow] using h)

theorem mtFiber57ReverseRow_7_ok :
    mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber57Chunk3_ok
  change (mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 6) &&
    mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber57ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber57StateAt 3) (mtFiber57StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber57StateAt 3) (mtFiber57StateAt 7)
    (mtFiber57RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber57Key mtFiber57Expected
        (mtFiber57RowAt 7) (by decide) mtFiber57ReverseRow_7_ok
      simpa [mtFiber57StateAt, mtFiber57RowAt, mtFiber57Rows, listGetD, directRow] using h)

theorem mtFiber57ReverseRow_8_ok :
    mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber57Chunk4_ok
  change (mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 8) &&
    mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber57ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber57StateAt 0) (mtFiber57StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber57StateAt 0) (mtFiber57StateAt 8)
    (mtFiber57RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber57Key mtFiber57Expected
        (mtFiber57RowAt 8) (by decide) mtFiber57ReverseRow_8_ok
      simpa [mtFiber57StateAt, mtFiber57RowAt, mtFiber57Rows, listGetD, directRow] using h)

theorem mtFiber57ReverseRow_9_ok :
    mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber57Chunk4_ok
  change (mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 8) &&
    mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber57ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber57StateAt 1) (mtFiber57StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber57StateAt 1) (mtFiber57StateAt 9)
    (mtFiber57RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber57Key mtFiber57Expected
        (mtFiber57RowAt 9) (by decide) mtFiber57ReverseRow_9_ok
      simpa [mtFiber57StateAt, mtFiber57RowAt, mtFiber57Rows, listGetD, directRow] using h)

theorem mtFiber57ReverseRow_10_ok :
    mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber57Chunk5_ok
  change (mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 10) &&
    mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber57ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber57StateAt 2) (mtFiber57StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber57StateAt 2) (mtFiber57StateAt 10)
    (mtFiber57RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber57Key mtFiber57Expected
        (mtFiber57RowAt 10) (by decide) mtFiber57ReverseRow_10_ok
      simpa [mtFiber57StateAt, mtFiber57RowAt, mtFiber57Rows, listGetD, directRow] using h)

theorem mtFiber57ReverseRow_11_ok :
    mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber57Chunk5_ok
  change (mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 10) &&
    mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber57ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber57StateAt 3) (mtFiber57StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber57StateAt 3) (mtFiber57StateAt 11)
    (mtFiber57RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber57Key mtFiber57Expected
        (mtFiber57RowAt 11) (by decide) mtFiber57ReverseRow_11_ok
      simpa [mtFiber57StateAt, mtFiber57RowAt, mtFiber57Rows, listGetD, directRow] using h)

theorem mtFiber57ReverseRow_12_ok :
    mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber57Chunk6_ok
  change (mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 12) &&
    mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber57ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber57StateAt 4) (mtFiber57StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber57StateAt 4) (mtFiber57StateAt 12)
    (mtFiber57RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber57Key mtFiber57Expected
        (mtFiber57RowAt 12) (by decide) mtFiber57ReverseRow_12_ok
      simpa [mtFiber57StateAt, mtFiber57RowAt, mtFiber57Rows, listGetD, directRow] using h)

theorem mtFiber57ReverseRow_13_ok :
    mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber57Chunk6_ok
  change (mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 12) &&
    mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber57ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber57StateAt 5) (mtFiber57StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber57StateAt 5) (mtFiber57StateAt 13)
    (mtFiber57RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber57Key mtFiber57Expected
        (mtFiber57RowAt 13) (by decide) mtFiber57ReverseRow_13_ok
      simpa [mtFiber57StateAt, mtFiber57RowAt, mtFiber57Rows, listGetD, directRow] using h)

theorem mtFiber57ReverseRow_14_ok :
    mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber57Chunk7_ok
  change (mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 14) &&
    mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber57ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber57StateAt 6) (mtFiber57StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber57StateAt 6) (mtFiber57StateAt 14)
    (mtFiber57RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber57Key mtFiber57Expected
        (mtFiber57RowAt 14) (by decide) mtFiber57ReverseRow_14_ok
      simpa [mtFiber57StateAt, mtFiber57RowAt, mtFiber57Rows, listGetD, directRow] using h)

theorem mtFiber57ReverseRow_15_ok :
    mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber57Chunk7_ok
  change (mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 14) &&
    mtRowReverseValid mtFiber57Key mtFiber57Expected (mtFiber57RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber57ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber57StateAt 7) (mtFiber57StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber57StateAt 7) (mtFiber57StateAt 15)
    (mtFiber57RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber57Key mtFiber57Expected
        (mtFiber57RowAt 15) (by decide) mtFiber57ReverseRow_15_ok
      simpa [mtFiber57StateAt, mtFiber57RowAt, mtFiber57Rows, listGetD, directRow] using h)

theorem mtFiber57State0_in_close :
    mtFiber57StateAt 0 ∈ closeChainFiber mtWord mtFiber57DirectStates mtFiber57DirectStates.length [mtFiber57StateAt 0] := by
  change mtFiber57StateAt 0 ∈ closeChainFiber mtWord mtFiber57DirectStates 16 [mtFiber57StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber57DirectStates 0 16 [mtFiber57StateAt 0] (mtFiber57StateAt 0) (by simp [closeChainFiber])

theorem mtFiber57State1_in_close :
    mtFiber57StateAt 1 ∈ closeChainFiber mtWord mtFiber57DirectStates mtFiber57DirectStates.length [mtFiber57StateAt 0] := by
  have h0 : mtFiber57StateAt 0 ∈ closeChainFiber mtWord mtFiber57DirectStates 0 [mtFiber57StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber57StateAt 1 ∈ closeChainFiber mtWord mtFiber57DirectStates 1 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 0 [mtFiber57StateAt 0]
      (mtFiber57StateAt 0) (mtFiber57StateAt 1) (by decide) h0 (by decide)
      mtFiber57ReverseSingleStep1
  change mtFiber57StateAt 1 ∈ closeChainFiber mtWord mtFiber57DirectStates (1 + 15) [mtFiber57StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber57DirectStates 1 15 [mtFiber57StateAt 0] (mtFiber57StateAt 1) h1

theorem mtFiber57State2_in_close :
    mtFiber57StateAt 2 ∈ closeChainFiber mtWord mtFiber57DirectStates mtFiber57DirectStates.length [mtFiber57StateAt 0] := by
  have h0 : mtFiber57StateAt 0 ∈ closeChainFiber mtWord mtFiber57DirectStates 0 [mtFiber57StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber57StateAt 1 ∈ closeChainFiber mtWord mtFiber57DirectStates 1 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 0 [mtFiber57StateAt 0]
      (mtFiber57StateAt 0) (mtFiber57StateAt 1) (by decide) h0 (by decide)
      mtFiber57ReverseSingleStep1
  have h2 : mtFiber57StateAt 2 ∈ closeChainFiber mtWord mtFiber57DirectStates 2 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 1 [mtFiber57StateAt 0]
      (mtFiber57StateAt 1) (mtFiber57StateAt 2) (by decide) h1 (by decide)
      mtFiber57ReverseSingleStep2
  change mtFiber57StateAt 2 ∈ closeChainFiber mtWord mtFiber57DirectStates (2 + 14) [mtFiber57StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber57DirectStates 2 14 [mtFiber57StateAt 0] (mtFiber57StateAt 2) h2

theorem mtFiber57State3_in_close :
    mtFiber57StateAt 3 ∈ closeChainFiber mtWord mtFiber57DirectStates mtFiber57DirectStates.length [mtFiber57StateAt 0] := by
  have h0 : mtFiber57StateAt 0 ∈ closeChainFiber mtWord mtFiber57DirectStates 0 [mtFiber57StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber57StateAt 3 ∈ closeChainFiber mtWord mtFiber57DirectStates 1 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 0 [mtFiber57StateAt 0]
      (mtFiber57StateAt 0) (mtFiber57StateAt 3) (by decide) h0 (by decide)
      mtFiber57ReverseSingleStep3
  change mtFiber57StateAt 3 ∈ closeChainFiber mtWord mtFiber57DirectStates (1 + 15) [mtFiber57StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber57DirectStates 1 15 [mtFiber57StateAt 0] (mtFiber57StateAt 3) h1

theorem mtFiber57State4_in_close :
    mtFiber57StateAt 4 ∈ closeChainFiber mtWord mtFiber57DirectStates mtFiber57DirectStates.length [mtFiber57StateAt 0] := by
  have h0 : mtFiber57StateAt 0 ∈ closeChainFiber mtWord mtFiber57DirectStates 0 [mtFiber57StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber57StateAt 4 ∈ closeChainFiber mtWord mtFiber57DirectStates 1 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 0 [mtFiber57StateAt 0]
      (mtFiber57StateAt 0) (mtFiber57StateAt 4) (by decide) h0 (by decide)
      mtFiber57ReverseSingleStep4
  change mtFiber57StateAt 4 ∈ closeChainFiber mtWord mtFiber57DirectStates (1 + 15) [mtFiber57StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber57DirectStates 1 15 [mtFiber57StateAt 0] (mtFiber57StateAt 4) h1

theorem mtFiber57State5_in_close :
    mtFiber57StateAt 5 ∈ closeChainFiber mtWord mtFiber57DirectStates mtFiber57DirectStates.length [mtFiber57StateAt 0] := by
  have h0 : mtFiber57StateAt 0 ∈ closeChainFiber mtWord mtFiber57DirectStates 0 [mtFiber57StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber57StateAt 1 ∈ closeChainFiber mtWord mtFiber57DirectStates 1 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 0 [mtFiber57StateAt 0]
      (mtFiber57StateAt 0) (mtFiber57StateAt 1) (by decide) h0 (by decide)
      mtFiber57ReverseSingleStep1
  have h2 : mtFiber57StateAt 5 ∈ closeChainFiber mtWord mtFiber57DirectStates 2 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 1 [mtFiber57StateAt 0]
      (mtFiber57StateAt 1) (mtFiber57StateAt 5) (by decide) h1 (by decide)
      mtFiber57ReverseSingleStep5
  change mtFiber57StateAt 5 ∈ closeChainFiber mtWord mtFiber57DirectStates (2 + 14) [mtFiber57StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber57DirectStates 2 14 [mtFiber57StateAt 0] (mtFiber57StateAt 5) h2

theorem mtFiber57State6_in_close :
    mtFiber57StateAt 6 ∈ closeChainFiber mtWord mtFiber57DirectStates mtFiber57DirectStates.length [mtFiber57StateAt 0] := by
  have h0 : mtFiber57StateAt 0 ∈ closeChainFiber mtWord mtFiber57DirectStates 0 [mtFiber57StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber57StateAt 1 ∈ closeChainFiber mtWord mtFiber57DirectStates 1 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 0 [mtFiber57StateAt 0]
      (mtFiber57StateAt 0) (mtFiber57StateAt 1) (by decide) h0 (by decide)
      mtFiber57ReverseSingleStep1
  have h2 : mtFiber57StateAt 2 ∈ closeChainFiber mtWord mtFiber57DirectStates 2 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 1 [mtFiber57StateAt 0]
      (mtFiber57StateAt 1) (mtFiber57StateAt 2) (by decide) h1 (by decide)
      mtFiber57ReverseSingleStep2
  have h3 : mtFiber57StateAt 6 ∈ closeChainFiber mtWord mtFiber57DirectStates 3 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 2 [mtFiber57StateAt 0]
      (mtFiber57StateAt 2) (mtFiber57StateAt 6) (by decide) h2 (by decide)
      mtFiber57ReverseSingleStep6
  change mtFiber57StateAt 6 ∈ closeChainFiber mtWord mtFiber57DirectStates (3 + 13) [mtFiber57StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber57DirectStates 3 13 [mtFiber57StateAt 0] (mtFiber57StateAt 6) h3

theorem mtFiber57State7_in_close :
    mtFiber57StateAt 7 ∈ closeChainFiber mtWord mtFiber57DirectStates mtFiber57DirectStates.length [mtFiber57StateAt 0] := by
  have h0 : mtFiber57StateAt 0 ∈ closeChainFiber mtWord mtFiber57DirectStates 0 [mtFiber57StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber57StateAt 3 ∈ closeChainFiber mtWord mtFiber57DirectStates 1 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 0 [mtFiber57StateAt 0]
      (mtFiber57StateAt 0) (mtFiber57StateAt 3) (by decide) h0 (by decide)
      mtFiber57ReverseSingleStep3
  have h2 : mtFiber57StateAt 7 ∈ closeChainFiber mtWord mtFiber57DirectStates 2 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 1 [mtFiber57StateAt 0]
      (mtFiber57StateAt 3) (mtFiber57StateAt 7) (by decide) h1 (by decide)
      mtFiber57ReverseSingleStep7
  change mtFiber57StateAt 7 ∈ closeChainFiber mtWord mtFiber57DirectStates (2 + 14) [mtFiber57StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber57DirectStates 2 14 [mtFiber57StateAt 0] (mtFiber57StateAt 7) h2

theorem mtFiber57State8_in_close :
    mtFiber57StateAt 8 ∈ closeChainFiber mtWord mtFiber57DirectStates mtFiber57DirectStates.length [mtFiber57StateAt 0] := by
  have h0 : mtFiber57StateAt 0 ∈ closeChainFiber mtWord mtFiber57DirectStates 0 [mtFiber57StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber57StateAt 8 ∈ closeChainFiber mtWord mtFiber57DirectStates 1 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 0 [mtFiber57StateAt 0]
      (mtFiber57StateAt 0) (mtFiber57StateAt 8) (by decide) h0 (by decide)
      mtFiber57ReverseSingleStep8
  change mtFiber57StateAt 8 ∈ closeChainFiber mtWord mtFiber57DirectStates (1 + 15) [mtFiber57StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber57DirectStates 1 15 [mtFiber57StateAt 0] (mtFiber57StateAt 8) h1

theorem mtFiber57State9_in_close :
    mtFiber57StateAt 9 ∈ closeChainFiber mtWord mtFiber57DirectStates mtFiber57DirectStates.length [mtFiber57StateAt 0] := by
  have h0 : mtFiber57StateAt 0 ∈ closeChainFiber mtWord mtFiber57DirectStates 0 [mtFiber57StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber57StateAt 1 ∈ closeChainFiber mtWord mtFiber57DirectStates 1 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 0 [mtFiber57StateAt 0]
      (mtFiber57StateAt 0) (mtFiber57StateAt 1) (by decide) h0 (by decide)
      mtFiber57ReverseSingleStep1
  have h2 : mtFiber57StateAt 9 ∈ closeChainFiber mtWord mtFiber57DirectStates 2 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 1 [mtFiber57StateAt 0]
      (mtFiber57StateAt 1) (mtFiber57StateAt 9) (by decide) h1 (by decide)
      mtFiber57ReverseSingleStep9
  change mtFiber57StateAt 9 ∈ closeChainFiber mtWord mtFiber57DirectStates (2 + 14) [mtFiber57StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber57DirectStates 2 14 [mtFiber57StateAt 0] (mtFiber57StateAt 9) h2

theorem mtFiber57State10_in_close :
    mtFiber57StateAt 10 ∈ closeChainFiber mtWord mtFiber57DirectStates mtFiber57DirectStates.length [mtFiber57StateAt 0] := by
  have h0 : mtFiber57StateAt 0 ∈ closeChainFiber mtWord mtFiber57DirectStates 0 [mtFiber57StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber57StateAt 1 ∈ closeChainFiber mtWord mtFiber57DirectStates 1 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 0 [mtFiber57StateAt 0]
      (mtFiber57StateAt 0) (mtFiber57StateAt 1) (by decide) h0 (by decide)
      mtFiber57ReverseSingleStep1
  have h2 : mtFiber57StateAt 2 ∈ closeChainFiber mtWord mtFiber57DirectStates 2 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 1 [mtFiber57StateAt 0]
      (mtFiber57StateAt 1) (mtFiber57StateAt 2) (by decide) h1 (by decide)
      mtFiber57ReverseSingleStep2
  have h3 : mtFiber57StateAt 10 ∈ closeChainFiber mtWord mtFiber57DirectStates 3 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 2 [mtFiber57StateAt 0]
      (mtFiber57StateAt 2) (mtFiber57StateAt 10) (by decide) h2 (by decide)
      mtFiber57ReverseSingleStep10
  change mtFiber57StateAt 10 ∈ closeChainFiber mtWord mtFiber57DirectStates (3 + 13) [mtFiber57StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber57DirectStates 3 13 [mtFiber57StateAt 0] (mtFiber57StateAt 10) h3

theorem mtFiber57State11_in_close :
    mtFiber57StateAt 11 ∈ closeChainFiber mtWord mtFiber57DirectStates mtFiber57DirectStates.length [mtFiber57StateAt 0] := by
  have h0 : mtFiber57StateAt 0 ∈ closeChainFiber mtWord mtFiber57DirectStates 0 [mtFiber57StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber57StateAt 3 ∈ closeChainFiber mtWord mtFiber57DirectStates 1 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 0 [mtFiber57StateAt 0]
      (mtFiber57StateAt 0) (mtFiber57StateAt 3) (by decide) h0 (by decide)
      mtFiber57ReverseSingleStep3
  have h2 : mtFiber57StateAt 11 ∈ closeChainFiber mtWord mtFiber57DirectStates 2 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 1 [mtFiber57StateAt 0]
      (mtFiber57StateAt 3) (mtFiber57StateAt 11) (by decide) h1 (by decide)
      mtFiber57ReverseSingleStep11
  change mtFiber57StateAt 11 ∈ closeChainFiber mtWord mtFiber57DirectStates (2 + 14) [mtFiber57StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber57DirectStates 2 14 [mtFiber57StateAt 0] (mtFiber57StateAt 11) h2

theorem mtFiber57State12_in_close :
    mtFiber57StateAt 12 ∈ closeChainFiber mtWord mtFiber57DirectStates mtFiber57DirectStates.length [mtFiber57StateAt 0] := by
  have h0 : mtFiber57StateAt 0 ∈ closeChainFiber mtWord mtFiber57DirectStates 0 [mtFiber57StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber57StateAt 4 ∈ closeChainFiber mtWord mtFiber57DirectStates 1 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 0 [mtFiber57StateAt 0]
      (mtFiber57StateAt 0) (mtFiber57StateAt 4) (by decide) h0 (by decide)
      mtFiber57ReverseSingleStep4
  have h2 : mtFiber57StateAt 12 ∈ closeChainFiber mtWord mtFiber57DirectStates 2 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 1 [mtFiber57StateAt 0]
      (mtFiber57StateAt 4) (mtFiber57StateAt 12) (by decide) h1 (by decide)
      mtFiber57ReverseSingleStep12
  change mtFiber57StateAt 12 ∈ closeChainFiber mtWord mtFiber57DirectStates (2 + 14) [mtFiber57StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber57DirectStates 2 14 [mtFiber57StateAt 0] (mtFiber57StateAt 12) h2

theorem mtFiber57State13_in_close :
    mtFiber57StateAt 13 ∈ closeChainFiber mtWord mtFiber57DirectStates mtFiber57DirectStates.length [mtFiber57StateAt 0] := by
  have h0 : mtFiber57StateAt 0 ∈ closeChainFiber mtWord mtFiber57DirectStates 0 [mtFiber57StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber57StateAt 1 ∈ closeChainFiber mtWord mtFiber57DirectStates 1 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 0 [mtFiber57StateAt 0]
      (mtFiber57StateAt 0) (mtFiber57StateAt 1) (by decide) h0 (by decide)
      mtFiber57ReverseSingleStep1
  have h2 : mtFiber57StateAt 5 ∈ closeChainFiber mtWord mtFiber57DirectStates 2 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 1 [mtFiber57StateAt 0]
      (mtFiber57StateAt 1) (mtFiber57StateAt 5) (by decide) h1 (by decide)
      mtFiber57ReverseSingleStep5
  have h3 : mtFiber57StateAt 13 ∈ closeChainFiber mtWord mtFiber57DirectStates 3 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 2 [mtFiber57StateAt 0]
      (mtFiber57StateAt 5) (mtFiber57StateAt 13) (by decide) h2 (by decide)
      mtFiber57ReverseSingleStep13
  change mtFiber57StateAt 13 ∈ closeChainFiber mtWord mtFiber57DirectStates (3 + 13) [mtFiber57StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber57DirectStates 3 13 [mtFiber57StateAt 0] (mtFiber57StateAt 13) h3

theorem mtFiber57State14_in_close :
    mtFiber57StateAt 14 ∈ closeChainFiber mtWord mtFiber57DirectStates mtFiber57DirectStates.length [mtFiber57StateAt 0] := by
  have h0 : mtFiber57StateAt 0 ∈ closeChainFiber mtWord mtFiber57DirectStates 0 [mtFiber57StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber57StateAt 1 ∈ closeChainFiber mtWord mtFiber57DirectStates 1 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 0 [mtFiber57StateAt 0]
      (mtFiber57StateAt 0) (mtFiber57StateAt 1) (by decide) h0 (by decide)
      mtFiber57ReverseSingleStep1
  have h2 : mtFiber57StateAt 2 ∈ closeChainFiber mtWord mtFiber57DirectStates 2 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 1 [mtFiber57StateAt 0]
      (mtFiber57StateAt 1) (mtFiber57StateAt 2) (by decide) h1 (by decide)
      mtFiber57ReverseSingleStep2
  have h3 : mtFiber57StateAt 6 ∈ closeChainFiber mtWord mtFiber57DirectStates 3 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 2 [mtFiber57StateAt 0]
      (mtFiber57StateAt 2) (mtFiber57StateAt 6) (by decide) h2 (by decide)
      mtFiber57ReverseSingleStep6
  have h4 : mtFiber57StateAt 14 ∈ closeChainFiber mtWord mtFiber57DirectStates 4 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 3 [mtFiber57StateAt 0]
      (mtFiber57StateAt 6) (mtFiber57StateAt 14) (by decide) h3 (by decide)
      mtFiber57ReverseSingleStep14
  change mtFiber57StateAt 14 ∈ closeChainFiber mtWord mtFiber57DirectStates (4 + 12) [mtFiber57StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber57DirectStates 4 12 [mtFiber57StateAt 0] (mtFiber57StateAt 14) h4

theorem mtFiber57State15_in_close :
    mtFiber57StateAt 15 ∈ closeChainFiber mtWord mtFiber57DirectStates mtFiber57DirectStates.length [mtFiber57StateAt 0] := by
  have h0 : mtFiber57StateAt 0 ∈ closeChainFiber mtWord mtFiber57DirectStates 0 [mtFiber57StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber57StateAt 3 ∈ closeChainFiber mtWord mtFiber57DirectStates 1 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 0 [mtFiber57StateAt 0]
      (mtFiber57StateAt 0) (mtFiber57StateAt 3) (by decide) h0 (by decide)
      mtFiber57ReverseSingleStep3
  have h2 : mtFiber57StateAt 7 ∈ closeChainFiber mtWord mtFiber57DirectStates 2 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 1 [mtFiber57StateAt 0]
      (mtFiber57StateAt 3) (mtFiber57StateAt 7) (by decide) h1 (by decide)
      mtFiber57ReverseSingleStep7
  have h3 : mtFiber57StateAt 15 ∈ closeChainFiber mtWord mtFiber57DirectStates 3 [mtFiber57StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber57DirectStates 2 [mtFiber57StateAt 0]
      (mtFiber57StateAt 7) (mtFiber57StateAt 15) (by decide) h2 (by decide)
      mtFiber57ReverseSingleStep15
  change mtFiber57StateAt 15 ∈ closeChainFiber mtWord mtFiber57DirectStates (3 + 13) [mtFiber57StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber57DirectStates 3 13 [mtFiber57StateAt 0] (mtFiber57StateAt 15) h3

theorem mtFiber57DirectConnected :
    chainFiberConnected mtWord mtFiber57DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber57DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber57State0_in_close
  · subst state
    exact mtFiber57State1_in_close
  · subst state
    exact mtFiber57State2_in_close
  · subst state
    exact mtFiber57State3_in_close
  · subst state
    exact mtFiber57State4_in_close
  · subst state
    exact mtFiber57State5_in_close
  · subst state
    exact mtFiber57State6_in_close
  · subst state
    exact mtFiber57State7_in_close
  · subst state
    exact mtFiber57State8_in_close
  · subst state
    exact mtFiber57State9_in_close
  · subst state
    exact mtFiber57State10_in_close
  · subst state
    exact mtFiber57State11_in_close
  · subst state
    exact mtFiber57State12_in_close
  · subst state
    exact mtFiber57State13_in_close
  · subst state
    exact mtFiber57State14_in_close
  · subst state
    exact mtFiber57State15_in_close
  · cases h
def mtFiber58StateAt (i : Nat) : List TauState :=
  directStates (mtFiber58RowAt i).sourceLeft (mtFiber58RowAt i).sourceRight

def mtFiber58DirectStates : List (List TauState) :=
  [mtFiber58StateAt 0, mtFiber58StateAt 1, mtFiber58StateAt 2, mtFiber58StateAt 3, mtFiber58StateAt 4, mtFiber58StateAt 5, mtFiber58StateAt 6, mtFiber58StateAt 7, mtFiber58StateAt 8, mtFiber58StateAt 9, mtFiber58StateAt 10, mtFiber58StateAt 11, mtFiber58StateAt 12, mtFiber58StateAt 13, mtFiber58StateAt 14, mtFiber58StateAt 15]

theorem mtFiber58ReverseRow_1_ok :
    mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber58Chunk0_ok
  change (mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 0) &&
    mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber58ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber58StateAt 0) (mtFiber58StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber58StateAt 0) (mtFiber58StateAt 1)
    (mtFiber58RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber58Key mtFiber58Expected
        (mtFiber58RowAt 1) (by decide) mtFiber58ReverseRow_1_ok
      simpa [mtFiber58StateAt, mtFiber58RowAt, mtFiber58Rows, listGetD, directRow] using h)

theorem mtFiber58ReverseRow_2_ok :
    mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber58Chunk1_ok
  change (mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 2) &&
    mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber58ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber58StateAt 0) (mtFiber58StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber58StateAt 0) (mtFiber58StateAt 2)
    (mtFiber58RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber58Key mtFiber58Expected
        (mtFiber58RowAt 2) (by decide) mtFiber58ReverseRow_2_ok
      simpa [mtFiber58StateAt, mtFiber58RowAt, mtFiber58Rows, listGetD, directRow] using h)

theorem mtFiber58ReverseRow_3_ok :
    mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber58Chunk1_ok
  change (mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 2) &&
    mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber58ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber58StateAt 1) (mtFiber58StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber58StateAt 1) (mtFiber58StateAt 3)
    (mtFiber58RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber58Key mtFiber58Expected
        (mtFiber58RowAt 3) (by decide) mtFiber58ReverseRow_3_ok
      simpa [mtFiber58StateAt, mtFiber58RowAt, mtFiber58Rows, listGetD, directRow] using h)

theorem mtFiber58ReverseRow_4_ok :
    mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber58Chunk2_ok
  change (mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 4) &&
    mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber58ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber58StateAt 0) (mtFiber58StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber58StateAt 0) (mtFiber58StateAt 4)
    (mtFiber58RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber58Key mtFiber58Expected
        (mtFiber58RowAt 4) (by decide) mtFiber58ReverseRow_4_ok
      simpa [mtFiber58StateAt, mtFiber58RowAt, mtFiber58Rows, listGetD, directRow] using h)

theorem mtFiber58ReverseRow_5_ok :
    mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber58Chunk2_ok
  change (mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 4) &&
    mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber58ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber58StateAt 1) (mtFiber58StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber58StateAt 1) (mtFiber58StateAt 5)
    (mtFiber58RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber58Key mtFiber58Expected
        (mtFiber58RowAt 5) (by decide) mtFiber58ReverseRow_5_ok
      simpa [mtFiber58StateAt, mtFiber58RowAt, mtFiber58Rows, listGetD, directRow] using h)

theorem mtFiber58ReverseRow_6_ok :
    mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber58Chunk3_ok
  change (mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 6) &&
    mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber58ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber58StateAt 2) (mtFiber58StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber58StateAt 2) (mtFiber58StateAt 6)
    (mtFiber58RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber58Key mtFiber58Expected
        (mtFiber58RowAt 6) (by decide) mtFiber58ReverseRow_6_ok
      simpa [mtFiber58StateAt, mtFiber58RowAt, mtFiber58Rows, listGetD, directRow] using h)

theorem mtFiber58ReverseRow_7_ok :
    mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber58Chunk3_ok
  change (mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 6) &&
    mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber58ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber58StateAt 3) (mtFiber58StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber58StateAt 3) (mtFiber58StateAt 7)
    (mtFiber58RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber58Key mtFiber58Expected
        (mtFiber58RowAt 7) (by decide) mtFiber58ReverseRow_7_ok
      simpa [mtFiber58StateAt, mtFiber58RowAt, mtFiber58Rows, listGetD, directRow] using h)

theorem mtFiber58ReverseRow_8_ok :
    mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber58Chunk4_ok
  change (mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 8) &&
    mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber58ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber58StateAt 0) (mtFiber58StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber58StateAt 0) (mtFiber58StateAt 8)
    (mtFiber58RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber58Key mtFiber58Expected
        (mtFiber58RowAt 8) (by decide) mtFiber58ReverseRow_8_ok
      simpa [mtFiber58StateAt, mtFiber58RowAt, mtFiber58Rows, listGetD, directRow] using h)

theorem mtFiber58ReverseRow_9_ok :
    mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber58Chunk4_ok
  change (mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 8) &&
    mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber58ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber58StateAt 1) (mtFiber58StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber58StateAt 1) (mtFiber58StateAt 9)
    (mtFiber58RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber58Key mtFiber58Expected
        (mtFiber58RowAt 9) (by decide) mtFiber58ReverseRow_9_ok
      simpa [mtFiber58StateAt, mtFiber58RowAt, mtFiber58Rows, listGetD, directRow] using h)

theorem mtFiber58ReverseRow_10_ok :
    mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber58Chunk5_ok
  change (mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 10) &&
    mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber58ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber58StateAt 2) (mtFiber58StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber58StateAt 2) (mtFiber58StateAt 10)
    (mtFiber58RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber58Key mtFiber58Expected
        (mtFiber58RowAt 10) (by decide) mtFiber58ReverseRow_10_ok
      simpa [mtFiber58StateAt, mtFiber58RowAt, mtFiber58Rows, listGetD, directRow] using h)

theorem mtFiber58ReverseRow_11_ok :
    mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber58Chunk5_ok
  change (mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 10) &&
    mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber58ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber58StateAt 3) (mtFiber58StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber58StateAt 3) (mtFiber58StateAt 11)
    (mtFiber58RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber58Key mtFiber58Expected
        (mtFiber58RowAt 11) (by decide) mtFiber58ReverseRow_11_ok
      simpa [mtFiber58StateAt, mtFiber58RowAt, mtFiber58Rows, listGetD, directRow] using h)

theorem mtFiber58ReverseRow_12_ok :
    mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber58Chunk6_ok
  change (mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 12) &&
    mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber58ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber58StateAt 4) (mtFiber58StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber58StateAt 4) (mtFiber58StateAt 12)
    (mtFiber58RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber58Key mtFiber58Expected
        (mtFiber58RowAt 12) (by decide) mtFiber58ReverseRow_12_ok
      simpa [mtFiber58StateAt, mtFiber58RowAt, mtFiber58Rows, listGetD, directRow] using h)

theorem mtFiber58ReverseRow_13_ok :
    mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber58Chunk6_ok
  change (mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 12) &&
    mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber58ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber58StateAt 5) (mtFiber58StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber58StateAt 5) (mtFiber58StateAt 13)
    (mtFiber58RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber58Key mtFiber58Expected
        (mtFiber58RowAt 13) (by decide) mtFiber58ReverseRow_13_ok
      simpa [mtFiber58StateAt, mtFiber58RowAt, mtFiber58Rows, listGetD, directRow] using h)

theorem mtFiber58ReverseRow_14_ok :
    mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber58Chunk7_ok
  change (mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 14) &&
    mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber58ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber58StateAt 6) (mtFiber58StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber58StateAt 6) (mtFiber58StateAt 14)
    (mtFiber58RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber58Key mtFiber58Expected
        (mtFiber58RowAt 14) (by decide) mtFiber58ReverseRow_14_ok
      simpa [mtFiber58StateAt, mtFiber58RowAt, mtFiber58Rows, listGetD, directRow] using h)

theorem mtFiber58ReverseRow_15_ok :
    mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber58Chunk7_ok
  change (mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 14) &&
    mtRowReverseValid mtFiber58Key mtFiber58Expected (mtFiber58RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber58ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber58StateAt 7) (mtFiber58StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber58StateAt 7) (mtFiber58StateAt 15)
    (mtFiber58RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber58Key mtFiber58Expected
        (mtFiber58RowAt 15) (by decide) mtFiber58ReverseRow_15_ok
      simpa [mtFiber58StateAt, mtFiber58RowAt, mtFiber58Rows, listGetD, directRow] using h)

theorem mtFiber58State0_in_close :
    mtFiber58StateAt 0 ∈ closeChainFiber mtWord mtFiber58DirectStates mtFiber58DirectStates.length [mtFiber58StateAt 0] := by
  change mtFiber58StateAt 0 ∈ closeChainFiber mtWord mtFiber58DirectStates 16 [mtFiber58StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber58DirectStates 0 16 [mtFiber58StateAt 0] (mtFiber58StateAt 0) (by simp [closeChainFiber])

theorem mtFiber58State1_in_close :
    mtFiber58StateAt 1 ∈ closeChainFiber mtWord mtFiber58DirectStates mtFiber58DirectStates.length [mtFiber58StateAt 0] := by
  have h0 : mtFiber58StateAt 0 ∈ closeChainFiber mtWord mtFiber58DirectStates 0 [mtFiber58StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber58StateAt 1 ∈ closeChainFiber mtWord mtFiber58DirectStates 1 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 0 [mtFiber58StateAt 0]
      (mtFiber58StateAt 0) (mtFiber58StateAt 1) (by decide) h0 (by decide)
      mtFiber58ReverseSingleStep1
  change mtFiber58StateAt 1 ∈ closeChainFiber mtWord mtFiber58DirectStates (1 + 15) [mtFiber58StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber58DirectStates 1 15 [mtFiber58StateAt 0] (mtFiber58StateAt 1) h1

theorem mtFiber58State2_in_close :
    mtFiber58StateAt 2 ∈ closeChainFiber mtWord mtFiber58DirectStates mtFiber58DirectStates.length [mtFiber58StateAt 0] := by
  have h0 : mtFiber58StateAt 0 ∈ closeChainFiber mtWord mtFiber58DirectStates 0 [mtFiber58StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber58StateAt 2 ∈ closeChainFiber mtWord mtFiber58DirectStates 1 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 0 [mtFiber58StateAt 0]
      (mtFiber58StateAt 0) (mtFiber58StateAt 2) (by decide) h0 (by decide)
      mtFiber58ReverseSingleStep2
  change mtFiber58StateAt 2 ∈ closeChainFiber mtWord mtFiber58DirectStates (1 + 15) [mtFiber58StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber58DirectStates 1 15 [mtFiber58StateAt 0] (mtFiber58StateAt 2) h1

theorem mtFiber58State3_in_close :
    mtFiber58StateAt 3 ∈ closeChainFiber mtWord mtFiber58DirectStates mtFiber58DirectStates.length [mtFiber58StateAt 0] := by
  have h0 : mtFiber58StateAt 0 ∈ closeChainFiber mtWord mtFiber58DirectStates 0 [mtFiber58StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber58StateAt 1 ∈ closeChainFiber mtWord mtFiber58DirectStates 1 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 0 [mtFiber58StateAt 0]
      (mtFiber58StateAt 0) (mtFiber58StateAt 1) (by decide) h0 (by decide)
      mtFiber58ReverseSingleStep1
  have h2 : mtFiber58StateAt 3 ∈ closeChainFiber mtWord mtFiber58DirectStates 2 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 1 [mtFiber58StateAt 0]
      (mtFiber58StateAt 1) (mtFiber58StateAt 3) (by decide) h1 (by decide)
      mtFiber58ReverseSingleStep3
  change mtFiber58StateAt 3 ∈ closeChainFiber mtWord mtFiber58DirectStates (2 + 14) [mtFiber58StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber58DirectStates 2 14 [mtFiber58StateAt 0] (mtFiber58StateAt 3) h2

theorem mtFiber58State4_in_close :
    mtFiber58StateAt 4 ∈ closeChainFiber mtWord mtFiber58DirectStates mtFiber58DirectStates.length [mtFiber58StateAt 0] := by
  have h0 : mtFiber58StateAt 0 ∈ closeChainFiber mtWord mtFiber58DirectStates 0 [mtFiber58StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber58StateAt 4 ∈ closeChainFiber mtWord mtFiber58DirectStates 1 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 0 [mtFiber58StateAt 0]
      (mtFiber58StateAt 0) (mtFiber58StateAt 4) (by decide) h0 (by decide)
      mtFiber58ReverseSingleStep4
  change mtFiber58StateAt 4 ∈ closeChainFiber mtWord mtFiber58DirectStates (1 + 15) [mtFiber58StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber58DirectStates 1 15 [mtFiber58StateAt 0] (mtFiber58StateAt 4) h1

theorem mtFiber58State5_in_close :
    mtFiber58StateAt 5 ∈ closeChainFiber mtWord mtFiber58DirectStates mtFiber58DirectStates.length [mtFiber58StateAt 0] := by
  have h0 : mtFiber58StateAt 0 ∈ closeChainFiber mtWord mtFiber58DirectStates 0 [mtFiber58StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber58StateAt 1 ∈ closeChainFiber mtWord mtFiber58DirectStates 1 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 0 [mtFiber58StateAt 0]
      (mtFiber58StateAt 0) (mtFiber58StateAt 1) (by decide) h0 (by decide)
      mtFiber58ReverseSingleStep1
  have h2 : mtFiber58StateAt 5 ∈ closeChainFiber mtWord mtFiber58DirectStates 2 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 1 [mtFiber58StateAt 0]
      (mtFiber58StateAt 1) (mtFiber58StateAt 5) (by decide) h1 (by decide)
      mtFiber58ReverseSingleStep5
  change mtFiber58StateAt 5 ∈ closeChainFiber mtWord mtFiber58DirectStates (2 + 14) [mtFiber58StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber58DirectStates 2 14 [mtFiber58StateAt 0] (mtFiber58StateAt 5) h2

theorem mtFiber58State6_in_close :
    mtFiber58StateAt 6 ∈ closeChainFiber mtWord mtFiber58DirectStates mtFiber58DirectStates.length [mtFiber58StateAt 0] := by
  have h0 : mtFiber58StateAt 0 ∈ closeChainFiber mtWord mtFiber58DirectStates 0 [mtFiber58StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber58StateAt 2 ∈ closeChainFiber mtWord mtFiber58DirectStates 1 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 0 [mtFiber58StateAt 0]
      (mtFiber58StateAt 0) (mtFiber58StateAt 2) (by decide) h0 (by decide)
      mtFiber58ReverseSingleStep2
  have h2 : mtFiber58StateAt 6 ∈ closeChainFiber mtWord mtFiber58DirectStates 2 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 1 [mtFiber58StateAt 0]
      (mtFiber58StateAt 2) (mtFiber58StateAt 6) (by decide) h1 (by decide)
      mtFiber58ReverseSingleStep6
  change mtFiber58StateAt 6 ∈ closeChainFiber mtWord mtFiber58DirectStates (2 + 14) [mtFiber58StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber58DirectStates 2 14 [mtFiber58StateAt 0] (mtFiber58StateAt 6) h2

theorem mtFiber58State7_in_close :
    mtFiber58StateAt 7 ∈ closeChainFiber mtWord mtFiber58DirectStates mtFiber58DirectStates.length [mtFiber58StateAt 0] := by
  have h0 : mtFiber58StateAt 0 ∈ closeChainFiber mtWord mtFiber58DirectStates 0 [mtFiber58StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber58StateAt 1 ∈ closeChainFiber mtWord mtFiber58DirectStates 1 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 0 [mtFiber58StateAt 0]
      (mtFiber58StateAt 0) (mtFiber58StateAt 1) (by decide) h0 (by decide)
      mtFiber58ReverseSingleStep1
  have h2 : mtFiber58StateAt 3 ∈ closeChainFiber mtWord mtFiber58DirectStates 2 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 1 [mtFiber58StateAt 0]
      (mtFiber58StateAt 1) (mtFiber58StateAt 3) (by decide) h1 (by decide)
      mtFiber58ReverseSingleStep3
  have h3 : mtFiber58StateAt 7 ∈ closeChainFiber mtWord mtFiber58DirectStates 3 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 2 [mtFiber58StateAt 0]
      (mtFiber58StateAt 3) (mtFiber58StateAt 7) (by decide) h2 (by decide)
      mtFiber58ReverseSingleStep7
  change mtFiber58StateAt 7 ∈ closeChainFiber mtWord mtFiber58DirectStates (3 + 13) [mtFiber58StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber58DirectStates 3 13 [mtFiber58StateAt 0] (mtFiber58StateAt 7) h3

theorem mtFiber58State8_in_close :
    mtFiber58StateAt 8 ∈ closeChainFiber mtWord mtFiber58DirectStates mtFiber58DirectStates.length [mtFiber58StateAt 0] := by
  have h0 : mtFiber58StateAt 0 ∈ closeChainFiber mtWord mtFiber58DirectStates 0 [mtFiber58StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber58StateAt 8 ∈ closeChainFiber mtWord mtFiber58DirectStates 1 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 0 [mtFiber58StateAt 0]
      (mtFiber58StateAt 0) (mtFiber58StateAt 8) (by decide) h0 (by decide)
      mtFiber58ReverseSingleStep8
  change mtFiber58StateAt 8 ∈ closeChainFiber mtWord mtFiber58DirectStates (1 + 15) [mtFiber58StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber58DirectStates 1 15 [mtFiber58StateAt 0] (mtFiber58StateAt 8) h1

theorem mtFiber58State9_in_close :
    mtFiber58StateAt 9 ∈ closeChainFiber mtWord mtFiber58DirectStates mtFiber58DirectStates.length [mtFiber58StateAt 0] := by
  have h0 : mtFiber58StateAt 0 ∈ closeChainFiber mtWord mtFiber58DirectStates 0 [mtFiber58StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber58StateAt 1 ∈ closeChainFiber mtWord mtFiber58DirectStates 1 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 0 [mtFiber58StateAt 0]
      (mtFiber58StateAt 0) (mtFiber58StateAt 1) (by decide) h0 (by decide)
      mtFiber58ReverseSingleStep1
  have h2 : mtFiber58StateAt 9 ∈ closeChainFiber mtWord mtFiber58DirectStates 2 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 1 [mtFiber58StateAt 0]
      (mtFiber58StateAt 1) (mtFiber58StateAt 9) (by decide) h1 (by decide)
      mtFiber58ReverseSingleStep9
  change mtFiber58StateAt 9 ∈ closeChainFiber mtWord mtFiber58DirectStates (2 + 14) [mtFiber58StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber58DirectStates 2 14 [mtFiber58StateAt 0] (mtFiber58StateAt 9) h2

theorem mtFiber58State10_in_close :
    mtFiber58StateAt 10 ∈ closeChainFiber mtWord mtFiber58DirectStates mtFiber58DirectStates.length [mtFiber58StateAt 0] := by
  have h0 : mtFiber58StateAt 0 ∈ closeChainFiber mtWord mtFiber58DirectStates 0 [mtFiber58StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber58StateAt 2 ∈ closeChainFiber mtWord mtFiber58DirectStates 1 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 0 [mtFiber58StateAt 0]
      (mtFiber58StateAt 0) (mtFiber58StateAt 2) (by decide) h0 (by decide)
      mtFiber58ReverseSingleStep2
  have h2 : mtFiber58StateAt 10 ∈ closeChainFiber mtWord mtFiber58DirectStates 2 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 1 [mtFiber58StateAt 0]
      (mtFiber58StateAt 2) (mtFiber58StateAt 10) (by decide) h1 (by decide)
      mtFiber58ReverseSingleStep10
  change mtFiber58StateAt 10 ∈ closeChainFiber mtWord mtFiber58DirectStates (2 + 14) [mtFiber58StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber58DirectStates 2 14 [mtFiber58StateAt 0] (mtFiber58StateAt 10) h2

theorem mtFiber58State11_in_close :
    mtFiber58StateAt 11 ∈ closeChainFiber mtWord mtFiber58DirectStates mtFiber58DirectStates.length [mtFiber58StateAt 0] := by
  have h0 : mtFiber58StateAt 0 ∈ closeChainFiber mtWord mtFiber58DirectStates 0 [mtFiber58StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber58StateAt 1 ∈ closeChainFiber mtWord mtFiber58DirectStates 1 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 0 [mtFiber58StateAt 0]
      (mtFiber58StateAt 0) (mtFiber58StateAt 1) (by decide) h0 (by decide)
      mtFiber58ReverseSingleStep1
  have h2 : mtFiber58StateAt 3 ∈ closeChainFiber mtWord mtFiber58DirectStates 2 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 1 [mtFiber58StateAt 0]
      (mtFiber58StateAt 1) (mtFiber58StateAt 3) (by decide) h1 (by decide)
      mtFiber58ReverseSingleStep3
  have h3 : mtFiber58StateAt 11 ∈ closeChainFiber mtWord mtFiber58DirectStates 3 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 2 [mtFiber58StateAt 0]
      (mtFiber58StateAt 3) (mtFiber58StateAt 11) (by decide) h2 (by decide)
      mtFiber58ReverseSingleStep11
  change mtFiber58StateAt 11 ∈ closeChainFiber mtWord mtFiber58DirectStates (3 + 13) [mtFiber58StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber58DirectStates 3 13 [mtFiber58StateAt 0] (mtFiber58StateAt 11) h3

theorem mtFiber58State12_in_close :
    mtFiber58StateAt 12 ∈ closeChainFiber mtWord mtFiber58DirectStates mtFiber58DirectStates.length [mtFiber58StateAt 0] := by
  have h0 : mtFiber58StateAt 0 ∈ closeChainFiber mtWord mtFiber58DirectStates 0 [mtFiber58StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber58StateAt 4 ∈ closeChainFiber mtWord mtFiber58DirectStates 1 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 0 [mtFiber58StateAt 0]
      (mtFiber58StateAt 0) (mtFiber58StateAt 4) (by decide) h0 (by decide)
      mtFiber58ReverseSingleStep4
  have h2 : mtFiber58StateAt 12 ∈ closeChainFiber mtWord mtFiber58DirectStates 2 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 1 [mtFiber58StateAt 0]
      (mtFiber58StateAt 4) (mtFiber58StateAt 12) (by decide) h1 (by decide)
      mtFiber58ReverseSingleStep12
  change mtFiber58StateAt 12 ∈ closeChainFiber mtWord mtFiber58DirectStates (2 + 14) [mtFiber58StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber58DirectStates 2 14 [mtFiber58StateAt 0] (mtFiber58StateAt 12) h2

theorem mtFiber58State13_in_close :
    mtFiber58StateAt 13 ∈ closeChainFiber mtWord mtFiber58DirectStates mtFiber58DirectStates.length [mtFiber58StateAt 0] := by
  have h0 : mtFiber58StateAt 0 ∈ closeChainFiber mtWord mtFiber58DirectStates 0 [mtFiber58StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber58StateAt 1 ∈ closeChainFiber mtWord mtFiber58DirectStates 1 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 0 [mtFiber58StateAt 0]
      (mtFiber58StateAt 0) (mtFiber58StateAt 1) (by decide) h0 (by decide)
      mtFiber58ReverseSingleStep1
  have h2 : mtFiber58StateAt 5 ∈ closeChainFiber mtWord mtFiber58DirectStates 2 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 1 [mtFiber58StateAt 0]
      (mtFiber58StateAt 1) (mtFiber58StateAt 5) (by decide) h1 (by decide)
      mtFiber58ReverseSingleStep5
  have h3 : mtFiber58StateAt 13 ∈ closeChainFiber mtWord mtFiber58DirectStates 3 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 2 [mtFiber58StateAt 0]
      (mtFiber58StateAt 5) (mtFiber58StateAt 13) (by decide) h2 (by decide)
      mtFiber58ReverseSingleStep13
  change mtFiber58StateAt 13 ∈ closeChainFiber mtWord mtFiber58DirectStates (3 + 13) [mtFiber58StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber58DirectStates 3 13 [mtFiber58StateAt 0] (mtFiber58StateAt 13) h3

theorem mtFiber58State14_in_close :
    mtFiber58StateAt 14 ∈ closeChainFiber mtWord mtFiber58DirectStates mtFiber58DirectStates.length [mtFiber58StateAt 0] := by
  have h0 : mtFiber58StateAt 0 ∈ closeChainFiber mtWord mtFiber58DirectStates 0 [mtFiber58StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber58StateAt 2 ∈ closeChainFiber mtWord mtFiber58DirectStates 1 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 0 [mtFiber58StateAt 0]
      (mtFiber58StateAt 0) (mtFiber58StateAt 2) (by decide) h0 (by decide)
      mtFiber58ReverseSingleStep2
  have h2 : mtFiber58StateAt 6 ∈ closeChainFiber mtWord mtFiber58DirectStates 2 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 1 [mtFiber58StateAt 0]
      (mtFiber58StateAt 2) (mtFiber58StateAt 6) (by decide) h1 (by decide)
      mtFiber58ReverseSingleStep6
  have h3 : mtFiber58StateAt 14 ∈ closeChainFiber mtWord mtFiber58DirectStates 3 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 2 [mtFiber58StateAt 0]
      (mtFiber58StateAt 6) (mtFiber58StateAt 14) (by decide) h2 (by decide)
      mtFiber58ReverseSingleStep14
  change mtFiber58StateAt 14 ∈ closeChainFiber mtWord mtFiber58DirectStates (3 + 13) [mtFiber58StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber58DirectStates 3 13 [mtFiber58StateAt 0] (mtFiber58StateAt 14) h3

theorem mtFiber58State15_in_close :
    mtFiber58StateAt 15 ∈ closeChainFiber mtWord mtFiber58DirectStates mtFiber58DirectStates.length [mtFiber58StateAt 0] := by
  have h0 : mtFiber58StateAt 0 ∈ closeChainFiber mtWord mtFiber58DirectStates 0 [mtFiber58StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber58StateAt 1 ∈ closeChainFiber mtWord mtFiber58DirectStates 1 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 0 [mtFiber58StateAt 0]
      (mtFiber58StateAt 0) (mtFiber58StateAt 1) (by decide) h0 (by decide)
      mtFiber58ReverseSingleStep1
  have h2 : mtFiber58StateAt 3 ∈ closeChainFiber mtWord mtFiber58DirectStates 2 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 1 [mtFiber58StateAt 0]
      (mtFiber58StateAt 1) (mtFiber58StateAt 3) (by decide) h1 (by decide)
      mtFiber58ReverseSingleStep3
  have h3 : mtFiber58StateAt 7 ∈ closeChainFiber mtWord mtFiber58DirectStates 3 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 2 [mtFiber58StateAt 0]
      (mtFiber58StateAt 3) (mtFiber58StateAt 7) (by decide) h2 (by decide)
      mtFiber58ReverseSingleStep7
  have h4 : mtFiber58StateAt 15 ∈ closeChainFiber mtWord mtFiber58DirectStates 4 [mtFiber58StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber58DirectStates 3 [mtFiber58StateAt 0]
      (mtFiber58StateAt 7) (mtFiber58StateAt 15) (by decide) h3 (by decide)
      mtFiber58ReverseSingleStep15
  change mtFiber58StateAt 15 ∈ closeChainFiber mtWord mtFiber58DirectStates (4 + 12) [mtFiber58StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber58DirectStates 4 12 [mtFiber58StateAt 0] (mtFiber58StateAt 15) h4

theorem mtFiber58DirectConnected :
    chainFiberConnected mtWord mtFiber58DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber58DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber58State0_in_close
  · subst state
    exact mtFiber58State1_in_close
  · subst state
    exact mtFiber58State2_in_close
  · subst state
    exact mtFiber58State3_in_close
  · subst state
    exact mtFiber58State4_in_close
  · subst state
    exact mtFiber58State5_in_close
  · subst state
    exact mtFiber58State6_in_close
  · subst state
    exact mtFiber58State7_in_close
  · subst state
    exact mtFiber58State8_in_close
  · subst state
    exact mtFiber58State9_in_close
  · subst state
    exact mtFiber58State10_in_close
  · subst state
    exact mtFiber58State11_in_close
  · subst state
    exact mtFiber58State12_in_close
  · subst state
    exact mtFiber58State13_in_close
  · subst state
    exact mtFiber58State14_in_close
  · subst state
    exact mtFiber58State15_in_close
  · cases h
def mtFiber62StateAt (i : Nat) : List TauState :=
  directStates (mtFiber62RowAt i).sourceLeft (mtFiber62RowAt i).sourceRight

def mtFiber62DirectStates : List (List TauState) :=
  [mtFiber62StateAt 0, mtFiber62StateAt 1, mtFiber62StateAt 2, mtFiber62StateAt 3, mtFiber62StateAt 4, mtFiber62StateAt 5, mtFiber62StateAt 6, mtFiber62StateAt 7, mtFiber62StateAt 8, mtFiber62StateAt 9, mtFiber62StateAt 10, mtFiber62StateAt 11, mtFiber62StateAt 12, mtFiber62StateAt 13, mtFiber62StateAt 14, mtFiber62StateAt 15]

theorem mtFiber62ReverseRow_1_ok :
    mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber62Chunk0_ok
  change (mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 0) &&
    mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber62ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber62StateAt 0) (mtFiber62StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber62StateAt 0) (mtFiber62StateAt 1)
    (mtFiber62RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber62Key mtFiber62Expected
        (mtFiber62RowAt 1) (by decide) mtFiber62ReverseRow_1_ok
      simpa [mtFiber62StateAt, mtFiber62RowAt, mtFiber62Rows, listGetD, directRow] using h)

theorem mtFiber62ReverseRow_2_ok :
    mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber62Chunk1_ok
  change (mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 2) &&
    mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber62ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber62StateAt 0) (mtFiber62StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber62StateAt 0) (mtFiber62StateAt 2)
    (mtFiber62RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber62Key mtFiber62Expected
        (mtFiber62RowAt 2) (by decide) mtFiber62ReverseRow_2_ok
      simpa [mtFiber62StateAt, mtFiber62RowAt, mtFiber62Rows, listGetD, directRow] using h)

theorem mtFiber62ReverseRow_3_ok :
    mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber62Chunk1_ok
  change (mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 2) &&
    mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber62ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber62StateAt 1) (mtFiber62StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber62StateAt 1) (mtFiber62StateAt 3)
    (mtFiber62RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber62Key mtFiber62Expected
        (mtFiber62RowAt 3) (by decide) mtFiber62ReverseRow_3_ok
      simpa [mtFiber62StateAt, mtFiber62RowAt, mtFiber62Rows, listGetD, directRow] using h)

theorem mtFiber62ReverseRow_4_ok :
    mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber62Chunk2_ok
  change (mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 4) &&
    mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber62ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber62StateAt 0) (mtFiber62StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber62StateAt 0) (mtFiber62StateAt 4)
    (mtFiber62RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber62Key mtFiber62Expected
        (mtFiber62RowAt 4) (by decide) mtFiber62ReverseRow_4_ok
      simpa [mtFiber62StateAt, mtFiber62RowAt, mtFiber62Rows, listGetD, directRow] using h)

theorem mtFiber62ReverseRow_5_ok :
    mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber62Chunk2_ok
  change (mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 4) &&
    mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber62ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber62StateAt 1) (mtFiber62StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber62StateAt 1) (mtFiber62StateAt 5)
    (mtFiber62RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber62Key mtFiber62Expected
        (mtFiber62RowAt 5) (by decide) mtFiber62ReverseRow_5_ok
      simpa [mtFiber62StateAt, mtFiber62RowAt, mtFiber62Rows, listGetD, directRow] using h)

theorem mtFiber62ReverseRow_6_ok :
    mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber62Chunk3_ok
  change (mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 6) &&
    mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber62ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber62StateAt 2) (mtFiber62StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber62StateAt 2) (mtFiber62StateAt 6)
    (mtFiber62RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber62Key mtFiber62Expected
        (mtFiber62RowAt 6) (by decide) mtFiber62ReverseRow_6_ok
      simpa [mtFiber62StateAt, mtFiber62RowAt, mtFiber62Rows, listGetD, directRow] using h)

theorem mtFiber62ReverseRow_7_ok :
    mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber62Chunk3_ok
  change (mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 6) &&
    mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber62ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber62StateAt 3) (mtFiber62StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber62StateAt 3) (mtFiber62StateAt 7)
    (mtFiber62RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber62Key mtFiber62Expected
        (mtFiber62RowAt 7) (by decide) mtFiber62ReverseRow_7_ok
      simpa [mtFiber62StateAt, mtFiber62RowAt, mtFiber62Rows, listGetD, directRow] using h)

theorem mtFiber62ReverseRow_8_ok :
    mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber62Chunk4_ok
  change (mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 8) &&
    mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber62ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber62StateAt 0) (mtFiber62StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber62StateAt 0) (mtFiber62StateAt 8)
    (mtFiber62RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber62Key mtFiber62Expected
        (mtFiber62RowAt 8) (by decide) mtFiber62ReverseRow_8_ok
      simpa [mtFiber62StateAt, mtFiber62RowAt, mtFiber62Rows, listGetD, directRow] using h)

theorem mtFiber62ReverseRow_9_ok :
    mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber62Chunk4_ok
  change (mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 8) &&
    mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber62ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber62StateAt 1) (mtFiber62StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber62StateAt 1) (mtFiber62StateAt 9)
    (mtFiber62RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber62Key mtFiber62Expected
        (mtFiber62RowAt 9) (by decide) mtFiber62ReverseRow_9_ok
      simpa [mtFiber62StateAt, mtFiber62RowAt, mtFiber62Rows, listGetD, directRow] using h)

theorem mtFiber62ReverseRow_10_ok :
    mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber62Chunk5_ok
  change (mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 10) &&
    mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber62ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber62StateAt 2) (mtFiber62StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber62StateAt 2) (mtFiber62StateAt 10)
    (mtFiber62RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber62Key mtFiber62Expected
        (mtFiber62RowAt 10) (by decide) mtFiber62ReverseRow_10_ok
      simpa [mtFiber62StateAt, mtFiber62RowAt, mtFiber62Rows, listGetD, directRow] using h)

theorem mtFiber62ReverseRow_11_ok :
    mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber62Chunk5_ok
  change (mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 10) &&
    mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber62ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber62StateAt 3) (mtFiber62StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber62StateAt 3) (mtFiber62StateAt 11)
    (mtFiber62RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber62Key mtFiber62Expected
        (mtFiber62RowAt 11) (by decide) mtFiber62ReverseRow_11_ok
      simpa [mtFiber62StateAt, mtFiber62RowAt, mtFiber62Rows, listGetD, directRow] using h)

theorem mtFiber62ReverseRow_12_ok :
    mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber62Chunk6_ok
  change (mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 12) &&
    mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber62ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber62StateAt 4) (mtFiber62StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber62StateAt 4) (mtFiber62StateAt 12)
    (mtFiber62RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber62Key mtFiber62Expected
        (mtFiber62RowAt 12) (by decide) mtFiber62ReverseRow_12_ok
      simpa [mtFiber62StateAt, mtFiber62RowAt, mtFiber62Rows, listGetD, directRow] using h)

theorem mtFiber62ReverseRow_13_ok :
    mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber62Chunk6_ok
  change (mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 12) &&
    mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber62ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber62StateAt 5) (mtFiber62StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber62StateAt 5) (mtFiber62StateAt 13)
    (mtFiber62RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber62Key mtFiber62Expected
        (mtFiber62RowAt 13) (by decide) mtFiber62ReverseRow_13_ok
      simpa [mtFiber62StateAt, mtFiber62RowAt, mtFiber62Rows, listGetD, directRow] using h)

theorem mtFiber62ReverseRow_14_ok :
    mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber62Chunk7_ok
  change (mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 14) &&
    mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber62ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber62StateAt 6) (mtFiber62StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber62StateAt 6) (mtFiber62StateAt 14)
    (mtFiber62RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber62Key mtFiber62Expected
        (mtFiber62RowAt 14) (by decide) mtFiber62ReverseRow_14_ok
      simpa [mtFiber62StateAt, mtFiber62RowAt, mtFiber62Rows, listGetD, directRow] using h)

theorem mtFiber62ReverseRow_15_ok :
    mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber62Chunk7_ok
  change (mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 14) &&
    mtRowReverseValid mtFiber62Key mtFiber62Expected (mtFiber62RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber62ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber62StateAt 7) (mtFiber62StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber62StateAt 7) (mtFiber62StateAt 15)
    (mtFiber62RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber62Key mtFiber62Expected
        (mtFiber62RowAt 15) (by decide) mtFiber62ReverseRow_15_ok
      simpa [mtFiber62StateAt, mtFiber62RowAt, mtFiber62Rows, listGetD, directRow] using h)

theorem mtFiber62State0_in_close :
    mtFiber62StateAt 0 ∈ closeChainFiber mtWord mtFiber62DirectStates mtFiber62DirectStates.length [mtFiber62StateAt 0] := by
  change mtFiber62StateAt 0 ∈ closeChainFiber mtWord mtFiber62DirectStates 16 [mtFiber62StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber62DirectStates 0 16 [mtFiber62StateAt 0] (mtFiber62StateAt 0) (by simp [closeChainFiber])

theorem mtFiber62State1_in_close :
    mtFiber62StateAt 1 ∈ closeChainFiber mtWord mtFiber62DirectStates mtFiber62DirectStates.length [mtFiber62StateAt 0] := by
  have h0 : mtFiber62StateAt 0 ∈ closeChainFiber mtWord mtFiber62DirectStates 0 [mtFiber62StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber62StateAt 1 ∈ closeChainFiber mtWord mtFiber62DirectStates 1 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 0 [mtFiber62StateAt 0]
      (mtFiber62StateAt 0) (mtFiber62StateAt 1) (by decide) h0 (by decide)
      mtFiber62ReverseSingleStep1
  change mtFiber62StateAt 1 ∈ closeChainFiber mtWord mtFiber62DirectStates (1 + 15) [mtFiber62StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber62DirectStates 1 15 [mtFiber62StateAt 0] (mtFiber62StateAt 1) h1

theorem mtFiber62State2_in_close :
    mtFiber62StateAt 2 ∈ closeChainFiber mtWord mtFiber62DirectStates mtFiber62DirectStates.length [mtFiber62StateAt 0] := by
  have h0 : mtFiber62StateAt 0 ∈ closeChainFiber mtWord mtFiber62DirectStates 0 [mtFiber62StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber62StateAt 2 ∈ closeChainFiber mtWord mtFiber62DirectStates 1 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 0 [mtFiber62StateAt 0]
      (mtFiber62StateAt 0) (mtFiber62StateAt 2) (by decide) h0 (by decide)
      mtFiber62ReverseSingleStep2
  change mtFiber62StateAt 2 ∈ closeChainFiber mtWord mtFiber62DirectStates (1 + 15) [mtFiber62StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber62DirectStates 1 15 [mtFiber62StateAt 0] (mtFiber62StateAt 2) h1

theorem mtFiber62State3_in_close :
    mtFiber62StateAt 3 ∈ closeChainFiber mtWord mtFiber62DirectStates mtFiber62DirectStates.length [mtFiber62StateAt 0] := by
  have h0 : mtFiber62StateAt 0 ∈ closeChainFiber mtWord mtFiber62DirectStates 0 [mtFiber62StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber62StateAt 1 ∈ closeChainFiber mtWord mtFiber62DirectStates 1 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 0 [mtFiber62StateAt 0]
      (mtFiber62StateAt 0) (mtFiber62StateAt 1) (by decide) h0 (by decide)
      mtFiber62ReverseSingleStep1
  have h2 : mtFiber62StateAt 3 ∈ closeChainFiber mtWord mtFiber62DirectStates 2 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 1 [mtFiber62StateAt 0]
      (mtFiber62StateAt 1) (mtFiber62StateAt 3) (by decide) h1 (by decide)
      mtFiber62ReverseSingleStep3
  change mtFiber62StateAt 3 ∈ closeChainFiber mtWord mtFiber62DirectStates (2 + 14) [mtFiber62StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber62DirectStates 2 14 [mtFiber62StateAt 0] (mtFiber62StateAt 3) h2

theorem mtFiber62State4_in_close :
    mtFiber62StateAt 4 ∈ closeChainFiber mtWord mtFiber62DirectStates mtFiber62DirectStates.length [mtFiber62StateAt 0] := by
  have h0 : mtFiber62StateAt 0 ∈ closeChainFiber mtWord mtFiber62DirectStates 0 [mtFiber62StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber62StateAt 4 ∈ closeChainFiber mtWord mtFiber62DirectStates 1 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 0 [mtFiber62StateAt 0]
      (mtFiber62StateAt 0) (mtFiber62StateAt 4) (by decide) h0 (by decide)
      mtFiber62ReverseSingleStep4
  change mtFiber62StateAt 4 ∈ closeChainFiber mtWord mtFiber62DirectStates (1 + 15) [mtFiber62StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber62DirectStates 1 15 [mtFiber62StateAt 0] (mtFiber62StateAt 4) h1

theorem mtFiber62State5_in_close :
    mtFiber62StateAt 5 ∈ closeChainFiber mtWord mtFiber62DirectStates mtFiber62DirectStates.length [mtFiber62StateAt 0] := by
  have h0 : mtFiber62StateAt 0 ∈ closeChainFiber mtWord mtFiber62DirectStates 0 [mtFiber62StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber62StateAt 1 ∈ closeChainFiber mtWord mtFiber62DirectStates 1 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 0 [mtFiber62StateAt 0]
      (mtFiber62StateAt 0) (mtFiber62StateAt 1) (by decide) h0 (by decide)
      mtFiber62ReverseSingleStep1
  have h2 : mtFiber62StateAt 5 ∈ closeChainFiber mtWord mtFiber62DirectStates 2 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 1 [mtFiber62StateAt 0]
      (mtFiber62StateAt 1) (mtFiber62StateAt 5) (by decide) h1 (by decide)
      mtFiber62ReverseSingleStep5
  change mtFiber62StateAt 5 ∈ closeChainFiber mtWord mtFiber62DirectStates (2 + 14) [mtFiber62StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber62DirectStates 2 14 [mtFiber62StateAt 0] (mtFiber62StateAt 5) h2

theorem mtFiber62State6_in_close :
    mtFiber62StateAt 6 ∈ closeChainFiber mtWord mtFiber62DirectStates mtFiber62DirectStates.length [mtFiber62StateAt 0] := by
  have h0 : mtFiber62StateAt 0 ∈ closeChainFiber mtWord mtFiber62DirectStates 0 [mtFiber62StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber62StateAt 2 ∈ closeChainFiber mtWord mtFiber62DirectStates 1 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 0 [mtFiber62StateAt 0]
      (mtFiber62StateAt 0) (mtFiber62StateAt 2) (by decide) h0 (by decide)
      mtFiber62ReverseSingleStep2
  have h2 : mtFiber62StateAt 6 ∈ closeChainFiber mtWord mtFiber62DirectStates 2 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 1 [mtFiber62StateAt 0]
      (mtFiber62StateAt 2) (mtFiber62StateAt 6) (by decide) h1 (by decide)
      mtFiber62ReverseSingleStep6
  change mtFiber62StateAt 6 ∈ closeChainFiber mtWord mtFiber62DirectStates (2 + 14) [mtFiber62StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber62DirectStates 2 14 [mtFiber62StateAt 0] (mtFiber62StateAt 6) h2

theorem mtFiber62State7_in_close :
    mtFiber62StateAt 7 ∈ closeChainFiber mtWord mtFiber62DirectStates mtFiber62DirectStates.length [mtFiber62StateAt 0] := by
  have h0 : mtFiber62StateAt 0 ∈ closeChainFiber mtWord mtFiber62DirectStates 0 [mtFiber62StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber62StateAt 1 ∈ closeChainFiber mtWord mtFiber62DirectStates 1 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 0 [mtFiber62StateAt 0]
      (mtFiber62StateAt 0) (mtFiber62StateAt 1) (by decide) h0 (by decide)
      mtFiber62ReverseSingleStep1
  have h2 : mtFiber62StateAt 3 ∈ closeChainFiber mtWord mtFiber62DirectStates 2 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 1 [mtFiber62StateAt 0]
      (mtFiber62StateAt 1) (mtFiber62StateAt 3) (by decide) h1 (by decide)
      mtFiber62ReverseSingleStep3
  have h3 : mtFiber62StateAt 7 ∈ closeChainFiber mtWord mtFiber62DirectStates 3 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 2 [mtFiber62StateAt 0]
      (mtFiber62StateAt 3) (mtFiber62StateAt 7) (by decide) h2 (by decide)
      mtFiber62ReverseSingleStep7
  change mtFiber62StateAt 7 ∈ closeChainFiber mtWord mtFiber62DirectStates (3 + 13) [mtFiber62StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber62DirectStates 3 13 [mtFiber62StateAt 0] (mtFiber62StateAt 7) h3

theorem mtFiber62State8_in_close :
    mtFiber62StateAt 8 ∈ closeChainFiber mtWord mtFiber62DirectStates mtFiber62DirectStates.length [mtFiber62StateAt 0] := by
  have h0 : mtFiber62StateAt 0 ∈ closeChainFiber mtWord mtFiber62DirectStates 0 [mtFiber62StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber62StateAt 8 ∈ closeChainFiber mtWord mtFiber62DirectStates 1 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 0 [mtFiber62StateAt 0]
      (mtFiber62StateAt 0) (mtFiber62StateAt 8) (by decide) h0 (by decide)
      mtFiber62ReverseSingleStep8
  change mtFiber62StateAt 8 ∈ closeChainFiber mtWord mtFiber62DirectStates (1 + 15) [mtFiber62StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber62DirectStates 1 15 [mtFiber62StateAt 0] (mtFiber62StateAt 8) h1

theorem mtFiber62State9_in_close :
    mtFiber62StateAt 9 ∈ closeChainFiber mtWord mtFiber62DirectStates mtFiber62DirectStates.length [mtFiber62StateAt 0] := by
  have h0 : mtFiber62StateAt 0 ∈ closeChainFiber mtWord mtFiber62DirectStates 0 [mtFiber62StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber62StateAt 1 ∈ closeChainFiber mtWord mtFiber62DirectStates 1 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 0 [mtFiber62StateAt 0]
      (mtFiber62StateAt 0) (mtFiber62StateAt 1) (by decide) h0 (by decide)
      mtFiber62ReverseSingleStep1
  have h2 : mtFiber62StateAt 9 ∈ closeChainFiber mtWord mtFiber62DirectStates 2 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 1 [mtFiber62StateAt 0]
      (mtFiber62StateAt 1) (mtFiber62StateAt 9) (by decide) h1 (by decide)
      mtFiber62ReverseSingleStep9
  change mtFiber62StateAt 9 ∈ closeChainFiber mtWord mtFiber62DirectStates (2 + 14) [mtFiber62StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber62DirectStates 2 14 [mtFiber62StateAt 0] (mtFiber62StateAt 9) h2

theorem mtFiber62State10_in_close :
    mtFiber62StateAt 10 ∈ closeChainFiber mtWord mtFiber62DirectStates mtFiber62DirectStates.length [mtFiber62StateAt 0] := by
  have h0 : mtFiber62StateAt 0 ∈ closeChainFiber mtWord mtFiber62DirectStates 0 [mtFiber62StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber62StateAt 2 ∈ closeChainFiber mtWord mtFiber62DirectStates 1 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 0 [mtFiber62StateAt 0]
      (mtFiber62StateAt 0) (mtFiber62StateAt 2) (by decide) h0 (by decide)
      mtFiber62ReverseSingleStep2
  have h2 : mtFiber62StateAt 10 ∈ closeChainFiber mtWord mtFiber62DirectStates 2 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 1 [mtFiber62StateAt 0]
      (mtFiber62StateAt 2) (mtFiber62StateAt 10) (by decide) h1 (by decide)
      mtFiber62ReverseSingleStep10
  change mtFiber62StateAt 10 ∈ closeChainFiber mtWord mtFiber62DirectStates (2 + 14) [mtFiber62StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber62DirectStates 2 14 [mtFiber62StateAt 0] (mtFiber62StateAt 10) h2

theorem mtFiber62State11_in_close :
    mtFiber62StateAt 11 ∈ closeChainFiber mtWord mtFiber62DirectStates mtFiber62DirectStates.length [mtFiber62StateAt 0] := by
  have h0 : mtFiber62StateAt 0 ∈ closeChainFiber mtWord mtFiber62DirectStates 0 [mtFiber62StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber62StateAt 1 ∈ closeChainFiber mtWord mtFiber62DirectStates 1 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 0 [mtFiber62StateAt 0]
      (mtFiber62StateAt 0) (mtFiber62StateAt 1) (by decide) h0 (by decide)
      mtFiber62ReverseSingleStep1
  have h2 : mtFiber62StateAt 3 ∈ closeChainFiber mtWord mtFiber62DirectStates 2 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 1 [mtFiber62StateAt 0]
      (mtFiber62StateAt 1) (mtFiber62StateAt 3) (by decide) h1 (by decide)
      mtFiber62ReverseSingleStep3
  have h3 : mtFiber62StateAt 11 ∈ closeChainFiber mtWord mtFiber62DirectStates 3 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 2 [mtFiber62StateAt 0]
      (mtFiber62StateAt 3) (mtFiber62StateAt 11) (by decide) h2 (by decide)
      mtFiber62ReverseSingleStep11
  change mtFiber62StateAt 11 ∈ closeChainFiber mtWord mtFiber62DirectStates (3 + 13) [mtFiber62StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber62DirectStates 3 13 [mtFiber62StateAt 0] (mtFiber62StateAt 11) h3

theorem mtFiber62State12_in_close :
    mtFiber62StateAt 12 ∈ closeChainFiber mtWord mtFiber62DirectStates mtFiber62DirectStates.length [mtFiber62StateAt 0] := by
  have h0 : mtFiber62StateAt 0 ∈ closeChainFiber mtWord mtFiber62DirectStates 0 [mtFiber62StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber62StateAt 4 ∈ closeChainFiber mtWord mtFiber62DirectStates 1 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 0 [mtFiber62StateAt 0]
      (mtFiber62StateAt 0) (mtFiber62StateAt 4) (by decide) h0 (by decide)
      mtFiber62ReverseSingleStep4
  have h2 : mtFiber62StateAt 12 ∈ closeChainFiber mtWord mtFiber62DirectStates 2 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 1 [mtFiber62StateAt 0]
      (mtFiber62StateAt 4) (mtFiber62StateAt 12) (by decide) h1 (by decide)
      mtFiber62ReverseSingleStep12
  change mtFiber62StateAt 12 ∈ closeChainFiber mtWord mtFiber62DirectStates (2 + 14) [mtFiber62StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber62DirectStates 2 14 [mtFiber62StateAt 0] (mtFiber62StateAt 12) h2

theorem mtFiber62State13_in_close :
    mtFiber62StateAt 13 ∈ closeChainFiber mtWord mtFiber62DirectStates mtFiber62DirectStates.length [mtFiber62StateAt 0] := by
  have h0 : mtFiber62StateAt 0 ∈ closeChainFiber mtWord mtFiber62DirectStates 0 [mtFiber62StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber62StateAt 1 ∈ closeChainFiber mtWord mtFiber62DirectStates 1 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 0 [mtFiber62StateAt 0]
      (mtFiber62StateAt 0) (mtFiber62StateAt 1) (by decide) h0 (by decide)
      mtFiber62ReverseSingleStep1
  have h2 : mtFiber62StateAt 5 ∈ closeChainFiber mtWord mtFiber62DirectStates 2 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 1 [mtFiber62StateAt 0]
      (mtFiber62StateAt 1) (mtFiber62StateAt 5) (by decide) h1 (by decide)
      mtFiber62ReverseSingleStep5
  have h3 : mtFiber62StateAt 13 ∈ closeChainFiber mtWord mtFiber62DirectStates 3 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 2 [mtFiber62StateAt 0]
      (mtFiber62StateAt 5) (mtFiber62StateAt 13) (by decide) h2 (by decide)
      mtFiber62ReverseSingleStep13
  change mtFiber62StateAt 13 ∈ closeChainFiber mtWord mtFiber62DirectStates (3 + 13) [mtFiber62StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber62DirectStates 3 13 [mtFiber62StateAt 0] (mtFiber62StateAt 13) h3

theorem mtFiber62State14_in_close :
    mtFiber62StateAt 14 ∈ closeChainFiber mtWord mtFiber62DirectStates mtFiber62DirectStates.length [mtFiber62StateAt 0] := by
  have h0 : mtFiber62StateAt 0 ∈ closeChainFiber mtWord mtFiber62DirectStates 0 [mtFiber62StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber62StateAt 2 ∈ closeChainFiber mtWord mtFiber62DirectStates 1 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 0 [mtFiber62StateAt 0]
      (mtFiber62StateAt 0) (mtFiber62StateAt 2) (by decide) h0 (by decide)
      mtFiber62ReverseSingleStep2
  have h2 : mtFiber62StateAt 6 ∈ closeChainFiber mtWord mtFiber62DirectStates 2 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 1 [mtFiber62StateAt 0]
      (mtFiber62StateAt 2) (mtFiber62StateAt 6) (by decide) h1 (by decide)
      mtFiber62ReverseSingleStep6
  have h3 : mtFiber62StateAt 14 ∈ closeChainFiber mtWord mtFiber62DirectStates 3 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 2 [mtFiber62StateAt 0]
      (mtFiber62StateAt 6) (mtFiber62StateAt 14) (by decide) h2 (by decide)
      mtFiber62ReverseSingleStep14
  change mtFiber62StateAt 14 ∈ closeChainFiber mtWord mtFiber62DirectStates (3 + 13) [mtFiber62StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber62DirectStates 3 13 [mtFiber62StateAt 0] (mtFiber62StateAt 14) h3

theorem mtFiber62State15_in_close :
    mtFiber62StateAt 15 ∈ closeChainFiber mtWord mtFiber62DirectStates mtFiber62DirectStates.length [mtFiber62StateAt 0] := by
  have h0 : mtFiber62StateAt 0 ∈ closeChainFiber mtWord mtFiber62DirectStates 0 [mtFiber62StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber62StateAt 1 ∈ closeChainFiber mtWord mtFiber62DirectStates 1 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 0 [mtFiber62StateAt 0]
      (mtFiber62StateAt 0) (mtFiber62StateAt 1) (by decide) h0 (by decide)
      mtFiber62ReverseSingleStep1
  have h2 : mtFiber62StateAt 3 ∈ closeChainFiber mtWord mtFiber62DirectStates 2 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 1 [mtFiber62StateAt 0]
      (mtFiber62StateAt 1) (mtFiber62StateAt 3) (by decide) h1 (by decide)
      mtFiber62ReverseSingleStep3
  have h3 : mtFiber62StateAt 7 ∈ closeChainFiber mtWord mtFiber62DirectStates 3 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 2 [mtFiber62StateAt 0]
      (mtFiber62StateAt 3) (mtFiber62StateAt 7) (by decide) h2 (by decide)
      mtFiber62ReverseSingleStep7
  have h4 : mtFiber62StateAt 15 ∈ closeChainFiber mtWord mtFiber62DirectStates 4 [mtFiber62StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber62DirectStates 3 [mtFiber62StateAt 0]
      (mtFiber62StateAt 7) (mtFiber62StateAt 15) (by decide) h3 (by decide)
      mtFiber62ReverseSingleStep15
  change mtFiber62StateAt 15 ∈ closeChainFiber mtWord mtFiber62DirectStates (4 + 12) [mtFiber62StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber62DirectStates 4 12 [mtFiber62StateAt 0] (mtFiber62StateAt 15) h4

theorem mtFiber62DirectConnected :
    chainFiberConnected mtWord mtFiber62DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber62DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber62State0_in_close
  · subst state
    exact mtFiber62State1_in_close
  · subst state
    exact mtFiber62State2_in_close
  · subst state
    exact mtFiber62State3_in_close
  · subst state
    exact mtFiber62State4_in_close
  · subst state
    exact mtFiber62State5_in_close
  · subst state
    exact mtFiber62State6_in_close
  · subst state
    exact mtFiber62State7_in_close
  · subst state
    exact mtFiber62State8_in_close
  · subst state
    exact mtFiber62State9_in_close
  · subst state
    exact mtFiber62State10_in_close
  · subst state
    exact mtFiber62State11_in_close
  · subst state
    exact mtFiber62State12_in_close
  · subst state
    exact mtFiber62State13_in_close
  · subst state
    exact mtFiber62State14_in_close
  · subst state
    exact mtFiber62State15_in_close
  · cases h
def mtFiber63StateAt (i : Nat) : List TauState :=
  directStates (mtFiber63RowAt i).sourceLeft (mtFiber63RowAt i).sourceRight

def mtFiber63DirectStates : List (List TauState) :=
  [mtFiber63StateAt 0, mtFiber63StateAt 1, mtFiber63StateAt 2, mtFiber63StateAt 3, mtFiber63StateAt 4, mtFiber63StateAt 5, mtFiber63StateAt 6, mtFiber63StateAt 7, mtFiber63StateAt 8, mtFiber63StateAt 9, mtFiber63StateAt 10, mtFiber63StateAt 11, mtFiber63StateAt 12, mtFiber63StateAt 13, mtFiber63StateAt 14, mtFiber63StateAt 15]

theorem mtFiber63ReverseRow_1_ok :
    mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber63Chunk0_ok
  change (mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 0) &&
    mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber63ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber63StateAt 0) (mtFiber63StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber63StateAt 0) (mtFiber63StateAt 1)
    (mtFiber63RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber63Key mtFiber63Expected
        (mtFiber63RowAt 1) (by decide) mtFiber63ReverseRow_1_ok
      simpa [mtFiber63StateAt, mtFiber63RowAt, mtFiber63Rows, listGetD, directRow] using h)

theorem mtFiber63ReverseRow_2_ok :
    mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber63Chunk1_ok
  change (mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 2) &&
    mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber63ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber63StateAt 1) (mtFiber63StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber63StateAt 1) (mtFiber63StateAt 2)
    (mtFiber63RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber63Key mtFiber63Expected
        (mtFiber63RowAt 2) (by decide) mtFiber63ReverseRow_2_ok
      simpa [mtFiber63StateAt, mtFiber63RowAt, mtFiber63Rows, listGetD, directRow] using h)

theorem mtFiber63ReverseRow_3_ok :
    mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber63Chunk1_ok
  change (mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 2) &&
    mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber63ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber63StateAt 0) (mtFiber63StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber63StateAt 0) (mtFiber63StateAt 3)
    (mtFiber63RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber63Key mtFiber63Expected
        (mtFiber63RowAt 3) (by decide) mtFiber63ReverseRow_3_ok
      simpa [mtFiber63StateAt, mtFiber63RowAt, mtFiber63Rows, listGetD, directRow] using h)

theorem mtFiber63ReverseRow_4_ok :
    mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber63Chunk2_ok
  change (mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 4) &&
    mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber63ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber63StateAt 0) (mtFiber63StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber63StateAt 0) (mtFiber63StateAt 4)
    (mtFiber63RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber63Key mtFiber63Expected
        (mtFiber63RowAt 4) (by decide) mtFiber63ReverseRow_4_ok
      simpa [mtFiber63StateAt, mtFiber63RowAt, mtFiber63Rows, listGetD, directRow] using h)

theorem mtFiber63ReverseRow_5_ok :
    mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber63Chunk2_ok
  change (mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 4) &&
    mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber63ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber63StateAt 1) (mtFiber63StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber63StateAt 1) (mtFiber63StateAt 5)
    (mtFiber63RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber63Key mtFiber63Expected
        (mtFiber63RowAt 5) (by decide) mtFiber63ReverseRow_5_ok
      simpa [mtFiber63StateAt, mtFiber63RowAt, mtFiber63Rows, listGetD, directRow] using h)

theorem mtFiber63ReverseRow_6_ok :
    mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber63Chunk3_ok
  change (mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 6) &&
    mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber63ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber63StateAt 2) (mtFiber63StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber63StateAt 2) (mtFiber63StateAt 6)
    (mtFiber63RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber63Key mtFiber63Expected
        (mtFiber63RowAt 6) (by decide) mtFiber63ReverseRow_6_ok
      simpa [mtFiber63StateAt, mtFiber63RowAt, mtFiber63Rows, listGetD, directRow] using h)

theorem mtFiber63ReverseRow_7_ok :
    mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber63Chunk3_ok
  change (mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 6) &&
    mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber63ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber63StateAt 3) (mtFiber63StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber63StateAt 3) (mtFiber63StateAt 7)
    (mtFiber63RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber63Key mtFiber63Expected
        (mtFiber63RowAt 7) (by decide) mtFiber63ReverseRow_7_ok
      simpa [mtFiber63StateAt, mtFiber63RowAt, mtFiber63Rows, listGetD, directRow] using h)

theorem mtFiber63ReverseRow_8_ok :
    mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber63Chunk4_ok
  change (mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 8) &&
    mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber63ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber63StateAt 0) (mtFiber63StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber63StateAt 0) (mtFiber63StateAt 8)
    (mtFiber63RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber63Key mtFiber63Expected
        (mtFiber63RowAt 8) (by decide) mtFiber63ReverseRow_8_ok
      simpa [mtFiber63StateAt, mtFiber63RowAt, mtFiber63Rows, listGetD, directRow] using h)

theorem mtFiber63ReverseRow_9_ok :
    mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber63Chunk4_ok
  change (mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 8) &&
    mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber63ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber63StateAt 1) (mtFiber63StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber63StateAt 1) (mtFiber63StateAt 9)
    (mtFiber63RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber63Key mtFiber63Expected
        (mtFiber63RowAt 9) (by decide) mtFiber63ReverseRow_9_ok
      simpa [mtFiber63StateAt, mtFiber63RowAt, mtFiber63Rows, listGetD, directRow] using h)

theorem mtFiber63ReverseRow_10_ok :
    mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber63Chunk5_ok
  change (mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 10) &&
    mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber63ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber63StateAt 2) (mtFiber63StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber63StateAt 2) (mtFiber63StateAt 10)
    (mtFiber63RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber63Key mtFiber63Expected
        (mtFiber63RowAt 10) (by decide) mtFiber63ReverseRow_10_ok
      simpa [mtFiber63StateAt, mtFiber63RowAt, mtFiber63Rows, listGetD, directRow] using h)

theorem mtFiber63ReverseRow_11_ok :
    mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber63Chunk5_ok
  change (mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 10) &&
    mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber63ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber63StateAt 3) (mtFiber63StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber63StateAt 3) (mtFiber63StateAt 11)
    (mtFiber63RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber63Key mtFiber63Expected
        (mtFiber63RowAt 11) (by decide) mtFiber63ReverseRow_11_ok
      simpa [mtFiber63StateAt, mtFiber63RowAt, mtFiber63Rows, listGetD, directRow] using h)

theorem mtFiber63ReverseRow_12_ok :
    mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber63Chunk6_ok
  change (mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 12) &&
    mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber63ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber63StateAt 4) (mtFiber63StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber63StateAt 4) (mtFiber63StateAt 12)
    (mtFiber63RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber63Key mtFiber63Expected
        (mtFiber63RowAt 12) (by decide) mtFiber63ReverseRow_12_ok
      simpa [mtFiber63StateAt, mtFiber63RowAt, mtFiber63Rows, listGetD, directRow] using h)

theorem mtFiber63ReverseRow_13_ok :
    mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber63Chunk6_ok
  change (mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 12) &&
    mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber63ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber63StateAt 5) (mtFiber63StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber63StateAt 5) (mtFiber63StateAt 13)
    (mtFiber63RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber63Key mtFiber63Expected
        (mtFiber63RowAt 13) (by decide) mtFiber63ReverseRow_13_ok
      simpa [mtFiber63StateAt, mtFiber63RowAt, mtFiber63Rows, listGetD, directRow] using h)

theorem mtFiber63ReverseRow_14_ok :
    mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber63Chunk7_ok
  change (mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 14) &&
    mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber63ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber63StateAt 6) (mtFiber63StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber63StateAt 6) (mtFiber63StateAt 14)
    (mtFiber63RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber63Key mtFiber63Expected
        (mtFiber63RowAt 14) (by decide) mtFiber63ReverseRow_14_ok
      simpa [mtFiber63StateAt, mtFiber63RowAt, mtFiber63Rows, listGetD, directRow] using h)

theorem mtFiber63ReverseRow_15_ok :
    mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber63Chunk7_ok
  change (mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 14) &&
    mtRowReverseValid mtFiber63Key mtFiber63Expected (mtFiber63RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber63ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber63StateAt 7) (mtFiber63StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber63StateAt 7) (mtFiber63StateAt 15)
    (mtFiber63RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber63Key mtFiber63Expected
        (mtFiber63RowAt 15) (by decide) mtFiber63ReverseRow_15_ok
      simpa [mtFiber63StateAt, mtFiber63RowAt, mtFiber63Rows, listGetD, directRow] using h)

theorem mtFiber63State0_in_close :
    mtFiber63StateAt 0 ∈ closeChainFiber mtWord mtFiber63DirectStates mtFiber63DirectStates.length [mtFiber63StateAt 0] := by
  change mtFiber63StateAt 0 ∈ closeChainFiber mtWord mtFiber63DirectStates 16 [mtFiber63StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber63DirectStates 0 16 [mtFiber63StateAt 0] (mtFiber63StateAt 0) (by simp [closeChainFiber])

theorem mtFiber63State1_in_close :
    mtFiber63StateAt 1 ∈ closeChainFiber mtWord mtFiber63DirectStates mtFiber63DirectStates.length [mtFiber63StateAt 0] := by
  have h0 : mtFiber63StateAt 0 ∈ closeChainFiber mtWord mtFiber63DirectStates 0 [mtFiber63StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber63StateAt 1 ∈ closeChainFiber mtWord mtFiber63DirectStates 1 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 0 [mtFiber63StateAt 0]
      (mtFiber63StateAt 0) (mtFiber63StateAt 1) (by decide) h0 (by decide)
      mtFiber63ReverseSingleStep1
  change mtFiber63StateAt 1 ∈ closeChainFiber mtWord mtFiber63DirectStates (1 + 15) [mtFiber63StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber63DirectStates 1 15 [mtFiber63StateAt 0] (mtFiber63StateAt 1) h1

theorem mtFiber63State2_in_close :
    mtFiber63StateAt 2 ∈ closeChainFiber mtWord mtFiber63DirectStates mtFiber63DirectStates.length [mtFiber63StateAt 0] := by
  have h0 : mtFiber63StateAt 0 ∈ closeChainFiber mtWord mtFiber63DirectStates 0 [mtFiber63StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber63StateAt 1 ∈ closeChainFiber mtWord mtFiber63DirectStates 1 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 0 [mtFiber63StateAt 0]
      (mtFiber63StateAt 0) (mtFiber63StateAt 1) (by decide) h0 (by decide)
      mtFiber63ReverseSingleStep1
  have h2 : mtFiber63StateAt 2 ∈ closeChainFiber mtWord mtFiber63DirectStates 2 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 1 [mtFiber63StateAt 0]
      (mtFiber63StateAt 1) (mtFiber63StateAt 2) (by decide) h1 (by decide)
      mtFiber63ReverseSingleStep2
  change mtFiber63StateAt 2 ∈ closeChainFiber mtWord mtFiber63DirectStates (2 + 14) [mtFiber63StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber63DirectStates 2 14 [mtFiber63StateAt 0] (mtFiber63StateAt 2) h2

theorem mtFiber63State3_in_close :
    mtFiber63StateAt 3 ∈ closeChainFiber mtWord mtFiber63DirectStates mtFiber63DirectStates.length [mtFiber63StateAt 0] := by
  have h0 : mtFiber63StateAt 0 ∈ closeChainFiber mtWord mtFiber63DirectStates 0 [mtFiber63StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber63StateAt 3 ∈ closeChainFiber mtWord mtFiber63DirectStates 1 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 0 [mtFiber63StateAt 0]
      (mtFiber63StateAt 0) (mtFiber63StateAt 3) (by decide) h0 (by decide)
      mtFiber63ReverseSingleStep3
  change mtFiber63StateAt 3 ∈ closeChainFiber mtWord mtFiber63DirectStates (1 + 15) [mtFiber63StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber63DirectStates 1 15 [mtFiber63StateAt 0] (mtFiber63StateAt 3) h1

theorem mtFiber63State4_in_close :
    mtFiber63StateAt 4 ∈ closeChainFiber mtWord mtFiber63DirectStates mtFiber63DirectStates.length [mtFiber63StateAt 0] := by
  have h0 : mtFiber63StateAt 0 ∈ closeChainFiber mtWord mtFiber63DirectStates 0 [mtFiber63StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber63StateAt 4 ∈ closeChainFiber mtWord mtFiber63DirectStates 1 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 0 [mtFiber63StateAt 0]
      (mtFiber63StateAt 0) (mtFiber63StateAt 4) (by decide) h0 (by decide)
      mtFiber63ReverseSingleStep4
  change mtFiber63StateAt 4 ∈ closeChainFiber mtWord mtFiber63DirectStates (1 + 15) [mtFiber63StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber63DirectStates 1 15 [mtFiber63StateAt 0] (mtFiber63StateAt 4) h1

theorem mtFiber63State5_in_close :
    mtFiber63StateAt 5 ∈ closeChainFiber mtWord mtFiber63DirectStates mtFiber63DirectStates.length [mtFiber63StateAt 0] := by
  have h0 : mtFiber63StateAt 0 ∈ closeChainFiber mtWord mtFiber63DirectStates 0 [mtFiber63StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber63StateAt 1 ∈ closeChainFiber mtWord mtFiber63DirectStates 1 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 0 [mtFiber63StateAt 0]
      (mtFiber63StateAt 0) (mtFiber63StateAt 1) (by decide) h0 (by decide)
      mtFiber63ReverseSingleStep1
  have h2 : mtFiber63StateAt 5 ∈ closeChainFiber mtWord mtFiber63DirectStates 2 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 1 [mtFiber63StateAt 0]
      (mtFiber63StateAt 1) (mtFiber63StateAt 5) (by decide) h1 (by decide)
      mtFiber63ReverseSingleStep5
  change mtFiber63StateAt 5 ∈ closeChainFiber mtWord mtFiber63DirectStates (2 + 14) [mtFiber63StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber63DirectStates 2 14 [mtFiber63StateAt 0] (mtFiber63StateAt 5) h2

theorem mtFiber63State6_in_close :
    mtFiber63StateAt 6 ∈ closeChainFiber mtWord mtFiber63DirectStates mtFiber63DirectStates.length [mtFiber63StateAt 0] := by
  have h0 : mtFiber63StateAt 0 ∈ closeChainFiber mtWord mtFiber63DirectStates 0 [mtFiber63StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber63StateAt 1 ∈ closeChainFiber mtWord mtFiber63DirectStates 1 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 0 [mtFiber63StateAt 0]
      (mtFiber63StateAt 0) (mtFiber63StateAt 1) (by decide) h0 (by decide)
      mtFiber63ReverseSingleStep1
  have h2 : mtFiber63StateAt 2 ∈ closeChainFiber mtWord mtFiber63DirectStates 2 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 1 [mtFiber63StateAt 0]
      (mtFiber63StateAt 1) (mtFiber63StateAt 2) (by decide) h1 (by decide)
      mtFiber63ReverseSingleStep2
  have h3 : mtFiber63StateAt 6 ∈ closeChainFiber mtWord mtFiber63DirectStates 3 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 2 [mtFiber63StateAt 0]
      (mtFiber63StateAt 2) (mtFiber63StateAt 6) (by decide) h2 (by decide)
      mtFiber63ReverseSingleStep6
  change mtFiber63StateAt 6 ∈ closeChainFiber mtWord mtFiber63DirectStates (3 + 13) [mtFiber63StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber63DirectStates 3 13 [mtFiber63StateAt 0] (mtFiber63StateAt 6) h3

theorem mtFiber63State7_in_close :
    mtFiber63StateAt 7 ∈ closeChainFiber mtWord mtFiber63DirectStates mtFiber63DirectStates.length [mtFiber63StateAt 0] := by
  have h0 : mtFiber63StateAt 0 ∈ closeChainFiber mtWord mtFiber63DirectStates 0 [mtFiber63StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber63StateAt 3 ∈ closeChainFiber mtWord mtFiber63DirectStates 1 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 0 [mtFiber63StateAt 0]
      (mtFiber63StateAt 0) (mtFiber63StateAt 3) (by decide) h0 (by decide)
      mtFiber63ReverseSingleStep3
  have h2 : mtFiber63StateAt 7 ∈ closeChainFiber mtWord mtFiber63DirectStates 2 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 1 [mtFiber63StateAt 0]
      (mtFiber63StateAt 3) (mtFiber63StateAt 7) (by decide) h1 (by decide)
      mtFiber63ReverseSingleStep7
  change mtFiber63StateAt 7 ∈ closeChainFiber mtWord mtFiber63DirectStates (2 + 14) [mtFiber63StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber63DirectStates 2 14 [mtFiber63StateAt 0] (mtFiber63StateAt 7) h2

theorem mtFiber63State8_in_close :
    mtFiber63StateAt 8 ∈ closeChainFiber mtWord mtFiber63DirectStates mtFiber63DirectStates.length [mtFiber63StateAt 0] := by
  have h0 : mtFiber63StateAt 0 ∈ closeChainFiber mtWord mtFiber63DirectStates 0 [mtFiber63StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber63StateAt 8 ∈ closeChainFiber mtWord mtFiber63DirectStates 1 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 0 [mtFiber63StateAt 0]
      (mtFiber63StateAt 0) (mtFiber63StateAt 8) (by decide) h0 (by decide)
      mtFiber63ReverseSingleStep8
  change mtFiber63StateAt 8 ∈ closeChainFiber mtWord mtFiber63DirectStates (1 + 15) [mtFiber63StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber63DirectStates 1 15 [mtFiber63StateAt 0] (mtFiber63StateAt 8) h1

theorem mtFiber63State9_in_close :
    mtFiber63StateAt 9 ∈ closeChainFiber mtWord mtFiber63DirectStates mtFiber63DirectStates.length [mtFiber63StateAt 0] := by
  have h0 : mtFiber63StateAt 0 ∈ closeChainFiber mtWord mtFiber63DirectStates 0 [mtFiber63StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber63StateAt 1 ∈ closeChainFiber mtWord mtFiber63DirectStates 1 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 0 [mtFiber63StateAt 0]
      (mtFiber63StateAt 0) (mtFiber63StateAt 1) (by decide) h0 (by decide)
      mtFiber63ReverseSingleStep1
  have h2 : mtFiber63StateAt 9 ∈ closeChainFiber mtWord mtFiber63DirectStates 2 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 1 [mtFiber63StateAt 0]
      (mtFiber63StateAt 1) (mtFiber63StateAt 9) (by decide) h1 (by decide)
      mtFiber63ReverseSingleStep9
  change mtFiber63StateAt 9 ∈ closeChainFiber mtWord mtFiber63DirectStates (2 + 14) [mtFiber63StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber63DirectStates 2 14 [mtFiber63StateAt 0] (mtFiber63StateAt 9) h2

theorem mtFiber63State10_in_close :
    mtFiber63StateAt 10 ∈ closeChainFiber mtWord mtFiber63DirectStates mtFiber63DirectStates.length [mtFiber63StateAt 0] := by
  have h0 : mtFiber63StateAt 0 ∈ closeChainFiber mtWord mtFiber63DirectStates 0 [mtFiber63StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber63StateAt 1 ∈ closeChainFiber mtWord mtFiber63DirectStates 1 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 0 [mtFiber63StateAt 0]
      (mtFiber63StateAt 0) (mtFiber63StateAt 1) (by decide) h0 (by decide)
      mtFiber63ReverseSingleStep1
  have h2 : mtFiber63StateAt 2 ∈ closeChainFiber mtWord mtFiber63DirectStates 2 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 1 [mtFiber63StateAt 0]
      (mtFiber63StateAt 1) (mtFiber63StateAt 2) (by decide) h1 (by decide)
      mtFiber63ReverseSingleStep2
  have h3 : mtFiber63StateAt 10 ∈ closeChainFiber mtWord mtFiber63DirectStates 3 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 2 [mtFiber63StateAt 0]
      (mtFiber63StateAt 2) (mtFiber63StateAt 10) (by decide) h2 (by decide)
      mtFiber63ReverseSingleStep10
  change mtFiber63StateAt 10 ∈ closeChainFiber mtWord mtFiber63DirectStates (3 + 13) [mtFiber63StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber63DirectStates 3 13 [mtFiber63StateAt 0] (mtFiber63StateAt 10) h3

theorem mtFiber63State11_in_close :
    mtFiber63StateAt 11 ∈ closeChainFiber mtWord mtFiber63DirectStates mtFiber63DirectStates.length [mtFiber63StateAt 0] := by
  have h0 : mtFiber63StateAt 0 ∈ closeChainFiber mtWord mtFiber63DirectStates 0 [mtFiber63StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber63StateAt 3 ∈ closeChainFiber mtWord mtFiber63DirectStates 1 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 0 [mtFiber63StateAt 0]
      (mtFiber63StateAt 0) (mtFiber63StateAt 3) (by decide) h0 (by decide)
      mtFiber63ReverseSingleStep3
  have h2 : mtFiber63StateAt 11 ∈ closeChainFiber mtWord mtFiber63DirectStates 2 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 1 [mtFiber63StateAt 0]
      (mtFiber63StateAt 3) (mtFiber63StateAt 11) (by decide) h1 (by decide)
      mtFiber63ReverseSingleStep11
  change mtFiber63StateAt 11 ∈ closeChainFiber mtWord mtFiber63DirectStates (2 + 14) [mtFiber63StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber63DirectStates 2 14 [mtFiber63StateAt 0] (mtFiber63StateAt 11) h2

theorem mtFiber63State12_in_close :
    mtFiber63StateAt 12 ∈ closeChainFiber mtWord mtFiber63DirectStates mtFiber63DirectStates.length [mtFiber63StateAt 0] := by
  have h0 : mtFiber63StateAt 0 ∈ closeChainFiber mtWord mtFiber63DirectStates 0 [mtFiber63StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber63StateAt 4 ∈ closeChainFiber mtWord mtFiber63DirectStates 1 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 0 [mtFiber63StateAt 0]
      (mtFiber63StateAt 0) (mtFiber63StateAt 4) (by decide) h0 (by decide)
      mtFiber63ReverseSingleStep4
  have h2 : mtFiber63StateAt 12 ∈ closeChainFiber mtWord mtFiber63DirectStates 2 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 1 [mtFiber63StateAt 0]
      (mtFiber63StateAt 4) (mtFiber63StateAt 12) (by decide) h1 (by decide)
      mtFiber63ReverseSingleStep12
  change mtFiber63StateAt 12 ∈ closeChainFiber mtWord mtFiber63DirectStates (2 + 14) [mtFiber63StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber63DirectStates 2 14 [mtFiber63StateAt 0] (mtFiber63StateAt 12) h2

theorem mtFiber63State13_in_close :
    mtFiber63StateAt 13 ∈ closeChainFiber mtWord mtFiber63DirectStates mtFiber63DirectStates.length [mtFiber63StateAt 0] := by
  have h0 : mtFiber63StateAt 0 ∈ closeChainFiber mtWord mtFiber63DirectStates 0 [mtFiber63StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber63StateAt 1 ∈ closeChainFiber mtWord mtFiber63DirectStates 1 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 0 [mtFiber63StateAt 0]
      (mtFiber63StateAt 0) (mtFiber63StateAt 1) (by decide) h0 (by decide)
      mtFiber63ReverseSingleStep1
  have h2 : mtFiber63StateAt 5 ∈ closeChainFiber mtWord mtFiber63DirectStates 2 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 1 [mtFiber63StateAt 0]
      (mtFiber63StateAt 1) (mtFiber63StateAt 5) (by decide) h1 (by decide)
      mtFiber63ReverseSingleStep5
  have h3 : mtFiber63StateAt 13 ∈ closeChainFiber mtWord mtFiber63DirectStates 3 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 2 [mtFiber63StateAt 0]
      (mtFiber63StateAt 5) (mtFiber63StateAt 13) (by decide) h2 (by decide)
      mtFiber63ReverseSingleStep13
  change mtFiber63StateAt 13 ∈ closeChainFiber mtWord mtFiber63DirectStates (3 + 13) [mtFiber63StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber63DirectStates 3 13 [mtFiber63StateAt 0] (mtFiber63StateAt 13) h3

theorem mtFiber63State14_in_close :
    mtFiber63StateAt 14 ∈ closeChainFiber mtWord mtFiber63DirectStates mtFiber63DirectStates.length [mtFiber63StateAt 0] := by
  have h0 : mtFiber63StateAt 0 ∈ closeChainFiber mtWord mtFiber63DirectStates 0 [mtFiber63StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber63StateAt 1 ∈ closeChainFiber mtWord mtFiber63DirectStates 1 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 0 [mtFiber63StateAt 0]
      (mtFiber63StateAt 0) (mtFiber63StateAt 1) (by decide) h0 (by decide)
      mtFiber63ReverseSingleStep1
  have h2 : mtFiber63StateAt 2 ∈ closeChainFiber mtWord mtFiber63DirectStates 2 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 1 [mtFiber63StateAt 0]
      (mtFiber63StateAt 1) (mtFiber63StateAt 2) (by decide) h1 (by decide)
      mtFiber63ReverseSingleStep2
  have h3 : mtFiber63StateAt 6 ∈ closeChainFiber mtWord mtFiber63DirectStates 3 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 2 [mtFiber63StateAt 0]
      (mtFiber63StateAt 2) (mtFiber63StateAt 6) (by decide) h2 (by decide)
      mtFiber63ReverseSingleStep6
  have h4 : mtFiber63StateAt 14 ∈ closeChainFiber mtWord mtFiber63DirectStates 4 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 3 [mtFiber63StateAt 0]
      (mtFiber63StateAt 6) (mtFiber63StateAt 14) (by decide) h3 (by decide)
      mtFiber63ReverseSingleStep14
  change mtFiber63StateAt 14 ∈ closeChainFiber mtWord mtFiber63DirectStates (4 + 12) [mtFiber63StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber63DirectStates 4 12 [mtFiber63StateAt 0] (mtFiber63StateAt 14) h4

theorem mtFiber63State15_in_close :
    mtFiber63StateAt 15 ∈ closeChainFiber mtWord mtFiber63DirectStates mtFiber63DirectStates.length [mtFiber63StateAt 0] := by
  have h0 : mtFiber63StateAt 0 ∈ closeChainFiber mtWord mtFiber63DirectStates 0 [mtFiber63StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber63StateAt 3 ∈ closeChainFiber mtWord mtFiber63DirectStates 1 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 0 [mtFiber63StateAt 0]
      (mtFiber63StateAt 0) (mtFiber63StateAt 3) (by decide) h0 (by decide)
      mtFiber63ReverseSingleStep3
  have h2 : mtFiber63StateAt 7 ∈ closeChainFiber mtWord mtFiber63DirectStates 2 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 1 [mtFiber63StateAt 0]
      (mtFiber63StateAt 3) (mtFiber63StateAt 7) (by decide) h1 (by decide)
      mtFiber63ReverseSingleStep7
  have h3 : mtFiber63StateAt 15 ∈ closeChainFiber mtWord mtFiber63DirectStates 3 [mtFiber63StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber63DirectStates 2 [mtFiber63StateAt 0]
      (mtFiber63StateAt 7) (mtFiber63StateAt 15) (by decide) h2 (by decide)
      mtFiber63ReverseSingleStep15
  change mtFiber63StateAt 15 ∈ closeChainFiber mtWord mtFiber63DirectStates (3 + 13) [mtFiber63StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber63DirectStates 3 13 [mtFiber63StateAt 0] (mtFiber63StateAt 15) h3

theorem mtFiber63DirectConnected :
    chainFiberConnected mtWord mtFiber63DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber63DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber63State0_in_close
  · subst state
    exact mtFiber63State1_in_close
  · subst state
    exact mtFiber63State2_in_close
  · subst state
    exact mtFiber63State3_in_close
  · subst state
    exact mtFiber63State4_in_close
  · subst state
    exact mtFiber63State5_in_close
  · subst state
    exact mtFiber63State6_in_close
  · subst state
    exact mtFiber63State7_in_close
  · subst state
    exact mtFiber63State8_in_close
  · subst state
    exact mtFiber63State9_in_close
  · subst state
    exact mtFiber63State10_in_close
  · subst state
    exact mtFiber63State11_in_close
  · subst state
    exact mtFiber63State12_in_close
  · subst state
    exact mtFiber63State13_in_close
  · subst state
    exact mtFiber63State14_in_close
  · subst state
    exact mtFiber63State15_in_close
  · cases h
end GoertzelLemma818LengthTwoMTBridge

end Mettapedia.GraphTheory.FourColor
