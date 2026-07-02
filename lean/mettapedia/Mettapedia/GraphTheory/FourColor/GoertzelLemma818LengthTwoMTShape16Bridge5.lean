import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for size-16 `mirror,normal` length-two fibers, group 5

This module proves direct connectedness for generated `mirror,normal` size-16 fibers from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMTBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorTauCertificate
open GoertzelLemma818MirrorTauReverseAudit

def mtFiber64StateAt (i : Nat) : List TauState :=
  directStates (mtFiber64RowAt i).sourceLeft (mtFiber64RowAt i).sourceRight

def mtFiber64DirectStates : List (List TauState) :=
  [mtFiber64StateAt 0, mtFiber64StateAt 1, mtFiber64StateAt 2, mtFiber64StateAt 3, mtFiber64StateAt 4, mtFiber64StateAt 5, mtFiber64StateAt 6, mtFiber64StateAt 7, mtFiber64StateAt 8, mtFiber64StateAt 9, mtFiber64StateAt 10, mtFiber64StateAt 11, mtFiber64StateAt 12, mtFiber64StateAt 13, mtFiber64StateAt 14, mtFiber64StateAt 15]

theorem mtFiber64ReverseRow_1_ok :
    mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber64Chunk0_ok
  change (mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 0) &&
    mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber64ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber64StateAt 0) (mtFiber64StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber64StateAt 0) (mtFiber64StateAt 1)
    (mtFiber64RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber64Key mtFiber64Expected
        (mtFiber64RowAt 1) (by decide) mtFiber64ReverseRow_1_ok
      simpa [mtFiber64StateAt, mtFiber64RowAt, mtFiber64Rows, listGetD, directRow] using h)

theorem mtFiber64ReverseRow_2_ok :
    mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber64Chunk1_ok
  change (mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 2) &&
    mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber64ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber64StateAt 0) (mtFiber64StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber64StateAt 0) (mtFiber64StateAt 2)
    (mtFiber64RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber64Key mtFiber64Expected
        (mtFiber64RowAt 2) (by decide) mtFiber64ReverseRow_2_ok
      simpa [mtFiber64StateAt, mtFiber64RowAt, mtFiber64Rows, listGetD, directRow] using h)

theorem mtFiber64ReverseRow_3_ok :
    mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber64Chunk1_ok
  change (mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 2) &&
    mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber64ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber64StateAt 1) (mtFiber64StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber64StateAt 1) (mtFiber64StateAt 3)
    (mtFiber64RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber64Key mtFiber64Expected
        (mtFiber64RowAt 3) (by decide) mtFiber64ReverseRow_3_ok
      simpa [mtFiber64StateAt, mtFiber64RowAt, mtFiber64Rows, listGetD, directRow] using h)

theorem mtFiber64ReverseRow_4_ok :
    mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber64Chunk2_ok
  change (mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 4) &&
    mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber64ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber64StateAt 0) (mtFiber64StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber64StateAt 0) (mtFiber64StateAt 4)
    (mtFiber64RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber64Key mtFiber64Expected
        (mtFiber64RowAt 4) (by decide) mtFiber64ReverseRow_4_ok
      simpa [mtFiber64StateAt, mtFiber64RowAt, mtFiber64Rows, listGetD, directRow] using h)

theorem mtFiber64ReverseRow_5_ok :
    mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber64Chunk2_ok
  change (mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 4) &&
    mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber64ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber64StateAt 1) (mtFiber64StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber64StateAt 1) (mtFiber64StateAt 5)
    (mtFiber64RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber64Key mtFiber64Expected
        (mtFiber64RowAt 5) (by decide) mtFiber64ReverseRow_5_ok
      simpa [mtFiber64StateAt, mtFiber64RowAt, mtFiber64Rows, listGetD, directRow] using h)

theorem mtFiber64ReverseRow_6_ok :
    mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber64Chunk3_ok
  change (mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 6) &&
    mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber64ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber64StateAt 2) (mtFiber64StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber64StateAt 2) (mtFiber64StateAt 6)
    (mtFiber64RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber64Key mtFiber64Expected
        (mtFiber64RowAt 6) (by decide) mtFiber64ReverseRow_6_ok
      simpa [mtFiber64StateAt, mtFiber64RowAt, mtFiber64Rows, listGetD, directRow] using h)

theorem mtFiber64ReverseRow_7_ok :
    mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber64Chunk3_ok
  change (mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 6) &&
    mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber64ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber64StateAt 3) (mtFiber64StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber64StateAt 3) (mtFiber64StateAt 7)
    (mtFiber64RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber64Key mtFiber64Expected
        (mtFiber64RowAt 7) (by decide) mtFiber64ReverseRow_7_ok
      simpa [mtFiber64StateAt, mtFiber64RowAt, mtFiber64Rows, listGetD, directRow] using h)

theorem mtFiber64ReverseRow_8_ok :
    mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber64Chunk4_ok
  change (mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 8) &&
    mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber64ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber64StateAt 0) (mtFiber64StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber64StateAt 0) (mtFiber64StateAt 8)
    (mtFiber64RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber64Key mtFiber64Expected
        (mtFiber64RowAt 8) (by decide) mtFiber64ReverseRow_8_ok
      simpa [mtFiber64StateAt, mtFiber64RowAt, mtFiber64Rows, listGetD, directRow] using h)

theorem mtFiber64ReverseRow_9_ok :
    mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber64Chunk4_ok
  change (mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 8) &&
    mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber64ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber64StateAt 1) (mtFiber64StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber64StateAt 1) (mtFiber64StateAt 9)
    (mtFiber64RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber64Key mtFiber64Expected
        (mtFiber64RowAt 9) (by decide) mtFiber64ReverseRow_9_ok
      simpa [mtFiber64StateAt, mtFiber64RowAt, mtFiber64Rows, listGetD, directRow] using h)

theorem mtFiber64ReverseRow_10_ok :
    mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber64Chunk5_ok
  change (mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 10) &&
    mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber64ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber64StateAt 2) (mtFiber64StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber64StateAt 2) (mtFiber64StateAt 10)
    (mtFiber64RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber64Key mtFiber64Expected
        (mtFiber64RowAt 10) (by decide) mtFiber64ReverseRow_10_ok
      simpa [mtFiber64StateAt, mtFiber64RowAt, mtFiber64Rows, listGetD, directRow] using h)

theorem mtFiber64ReverseRow_11_ok :
    mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber64Chunk5_ok
  change (mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 10) &&
    mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber64ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber64StateAt 3) (mtFiber64StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber64StateAt 3) (mtFiber64StateAt 11)
    (mtFiber64RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber64Key mtFiber64Expected
        (mtFiber64RowAt 11) (by decide) mtFiber64ReverseRow_11_ok
      simpa [mtFiber64StateAt, mtFiber64RowAt, mtFiber64Rows, listGetD, directRow] using h)

theorem mtFiber64ReverseRow_12_ok :
    mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber64Chunk6_ok
  change (mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 12) &&
    mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber64ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber64StateAt 4) (mtFiber64StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber64StateAt 4) (mtFiber64StateAt 12)
    (mtFiber64RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber64Key mtFiber64Expected
        (mtFiber64RowAt 12) (by decide) mtFiber64ReverseRow_12_ok
      simpa [mtFiber64StateAt, mtFiber64RowAt, mtFiber64Rows, listGetD, directRow] using h)

theorem mtFiber64ReverseRow_13_ok :
    mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber64Chunk6_ok
  change (mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 12) &&
    mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber64ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber64StateAt 5) (mtFiber64StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber64StateAt 5) (mtFiber64StateAt 13)
    (mtFiber64RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber64Key mtFiber64Expected
        (mtFiber64RowAt 13) (by decide) mtFiber64ReverseRow_13_ok
      simpa [mtFiber64StateAt, mtFiber64RowAt, mtFiber64Rows, listGetD, directRow] using h)

theorem mtFiber64ReverseRow_14_ok :
    mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber64Chunk7_ok
  change (mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 14) &&
    mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber64ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber64StateAt 6) (mtFiber64StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber64StateAt 6) (mtFiber64StateAt 14)
    (mtFiber64RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber64Key mtFiber64Expected
        (mtFiber64RowAt 14) (by decide) mtFiber64ReverseRow_14_ok
      simpa [mtFiber64StateAt, mtFiber64RowAt, mtFiber64Rows, listGetD, directRow] using h)

theorem mtFiber64ReverseRow_15_ok :
    mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber64Chunk7_ok
  change (mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 14) &&
    mtRowReverseValid mtFiber64Key mtFiber64Expected (mtFiber64RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber64ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber64StateAt 7) (mtFiber64StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber64StateAt 7) (mtFiber64StateAt 15)
    (mtFiber64RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber64Key mtFiber64Expected
        (mtFiber64RowAt 15) (by decide) mtFiber64ReverseRow_15_ok
      simpa [mtFiber64StateAt, mtFiber64RowAt, mtFiber64Rows, listGetD, directRow] using h)

theorem mtFiber64State0_in_close :
    mtFiber64StateAt 0 ∈ closeChainFiber mtWord mtFiber64DirectStates mtFiber64DirectStates.length [mtFiber64StateAt 0] := by
  change mtFiber64StateAt 0 ∈ closeChainFiber mtWord mtFiber64DirectStates 16 [mtFiber64StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber64DirectStates 0 16 [mtFiber64StateAt 0] (mtFiber64StateAt 0) (by simp [closeChainFiber])

theorem mtFiber64State1_in_close :
    mtFiber64StateAt 1 ∈ closeChainFiber mtWord mtFiber64DirectStates mtFiber64DirectStates.length [mtFiber64StateAt 0] := by
  have h0 : mtFiber64StateAt 0 ∈ closeChainFiber mtWord mtFiber64DirectStates 0 [mtFiber64StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber64StateAt 1 ∈ closeChainFiber mtWord mtFiber64DirectStates 1 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 0 [mtFiber64StateAt 0]
      (mtFiber64StateAt 0) (mtFiber64StateAt 1) (by decide) h0 (by decide)
      mtFiber64ReverseSingleStep1
  change mtFiber64StateAt 1 ∈ closeChainFiber mtWord mtFiber64DirectStates (1 + 15) [mtFiber64StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber64DirectStates 1 15 [mtFiber64StateAt 0] (mtFiber64StateAt 1) h1

theorem mtFiber64State2_in_close :
    mtFiber64StateAt 2 ∈ closeChainFiber mtWord mtFiber64DirectStates mtFiber64DirectStates.length [mtFiber64StateAt 0] := by
  have h0 : mtFiber64StateAt 0 ∈ closeChainFiber mtWord mtFiber64DirectStates 0 [mtFiber64StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber64StateAt 2 ∈ closeChainFiber mtWord mtFiber64DirectStates 1 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 0 [mtFiber64StateAt 0]
      (mtFiber64StateAt 0) (mtFiber64StateAt 2) (by decide) h0 (by decide)
      mtFiber64ReverseSingleStep2
  change mtFiber64StateAt 2 ∈ closeChainFiber mtWord mtFiber64DirectStates (1 + 15) [mtFiber64StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber64DirectStates 1 15 [mtFiber64StateAt 0] (mtFiber64StateAt 2) h1

theorem mtFiber64State3_in_close :
    mtFiber64StateAt 3 ∈ closeChainFiber mtWord mtFiber64DirectStates mtFiber64DirectStates.length [mtFiber64StateAt 0] := by
  have h0 : mtFiber64StateAt 0 ∈ closeChainFiber mtWord mtFiber64DirectStates 0 [mtFiber64StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber64StateAt 1 ∈ closeChainFiber mtWord mtFiber64DirectStates 1 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 0 [mtFiber64StateAt 0]
      (mtFiber64StateAt 0) (mtFiber64StateAt 1) (by decide) h0 (by decide)
      mtFiber64ReverseSingleStep1
  have h2 : mtFiber64StateAt 3 ∈ closeChainFiber mtWord mtFiber64DirectStates 2 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 1 [mtFiber64StateAt 0]
      (mtFiber64StateAt 1) (mtFiber64StateAt 3) (by decide) h1 (by decide)
      mtFiber64ReverseSingleStep3
  change mtFiber64StateAt 3 ∈ closeChainFiber mtWord mtFiber64DirectStates (2 + 14) [mtFiber64StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber64DirectStates 2 14 [mtFiber64StateAt 0] (mtFiber64StateAt 3) h2

theorem mtFiber64State4_in_close :
    mtFiber64StateAt 4 ∈ closeChainFiber mtWord mtFiber64DirectStates mtFiber64DirectStates.length [mtFiber64StateAt 0] := by
  have h0 : mtFiber64StateAt 0 ∈ closeChainFiber mtWord mtFiber64DirectStates 0 [mtFiber64StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber64StateAt 4 ∈ closeChainFiber mtWord mtFiber64DirectStates 1 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 0 [mtFiber64StateAt 0]
      (mtFiber64StateAt 0) (mtFiber64StateAt 4) (by decide) h0 (by decide)
      mtFiber64ReverseSingleStep4
  change mtFiber64StateAt 4 ∈ closeChainFiber mtWord mtFiber64DirectStates (1 + 15) [mtFiber64StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber64DirectStates 1 15 [mtFiber64StateAt 0] (mtFiber64StateAt 4) h1

theorem mtFiber64State5_in_close :
    mtFiber64StateAt 5 ∈ closeChainFiber mtWord mtFiber64DirectStates mtFiber64DirectStates.length [mtFiber64StateAt 0] := by
  have h0 : mtFiber64StateAt 0 ∈ closeChainFiber mtWord mtFiber64DirectStates 0 [mtFiber64StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber64StateAt 1 ∈ closeChainFiber mtWord mtFiber64DirectStates 1 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 0 [mtFiber64StateAt 0]
      (mtFiber64StateAt 0) (mtFiber64StateAt 1) (by decide) h0 (by decide)
      mtFiber64ReverseSingleStep1
  have h2 : mtFiber64StateAt 5 ∈ closeChainFiber mtWord mtFiber64DirectStates 2 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 1 [mtFiber64StateAt 0]
      (mtFiber64StateAt 1) (mtFiber64StateAt 5) (by decide) h1 (by decide)
      mtFiber64ReverseSingleStep5
  change mtFiber64StateAt 5 ∈ closeChainFiber mtWord mtFiber64DirectStates (2 + 14) [mtFiber64StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber64DirectStates 2 14 [mtFiber64StateAt 0] (mtFiber64StateAt 5) h2

theorem mtFiber64State6_in_close :
    mtFiber64StateAt 6 ∈ closeChainFiber mtWord mtFiber64DirectStates mtFiber64DirectStates.length [mtFiber64StateAt 0] := by
  have h0 : mtFiber64StateAt 0 ∈ closeChainFiber mtWord mtFiber64DirectStates 0 [mtFiber64StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber64StateAt 2 ∈ closeChainFiber mtWord mtFiber64DirectStates 1 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 0 [mtFiber64StateAt 0]
      (mtFiber64StateAt 0) (mtFiber64StateAt 2) (by decide) h0 (by decide)
      mtFiber64ReverseSingleStep2
  have h2 : mtFiber64StateAt 6 ∈ closeChainFiber mtWord mtFiber64DirectStates 2 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 1 [mtFiber64StateAt 0]
      (mtFiber64StateAt 2) (mtFiber64StateAt 6) (by decide) h1 (by decide)
      mtFiber64ReverseSingleStep6
  change mtFiber64StateAt 6 ∈ closeChainFiber mtWord mtFiber64DirectStates (2 + 14) [mtFiber64StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber64DirectStates 2 14 [mtFiber64StateAt 0] (mtFiber64StateAt 6) h2

theorem mtFiber64State7_in_close :
    mtFiber64StateAt 7 ∈ closeChainFiber mtWord mtFiber64DirectStates mtFiber64DirectStates.length [mtFiber64StateAt 0] := by
  have h0 : mtFiber64StateAt 0 ∈ closeChainFiber mtWord mtFiber64DirectStates 0 [mtFiber64StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber64StateAt 1 ∈ closeChainFiber mtWord mtFiber64DirectStates 1 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 0 [mtFiber64StateAt 0]
      (mtFiber64StateAt 0) (mtFiber64StateAt 1) (by decide) h0 (by decide)
      mtFiber64ReverseSingleStep1
  have h2 : mtFiber64StateAt 3 ∈ closeChainFiber mtWord mtFiber64DirectStates 2 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 1 [mtFiber64StateAt 0]
      (mtFiber64StateAt 1) (mtFiber64StateAt 3) (by decide) h1 (by decide)
      mtFiber64ReverseSingleStep3
  have h3 : mtFiber64StateAt 7 ∈ closeChainFiber mtWord mtFiber64DirectStates 3 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 2 [mtFiber64StateAt 0]
      (mtFiber64StateAt 3) (mtFiber64StateAt 7) (by decide) h2 (by decide)
      mtFiber64ReverseSingleStep7
  change mtFiber64StateAt 7 ∈ closeChainFiber mtWord mtFiber64DirectStates (3 + 13) [mtFiber64StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber64DirectStates 3 13 [mtFiber64StateAt 0] (mtFiber64StateAt 7) h3

theorem mtFiber64State8_in_close :
    mtFiber64StateAt 8 ∈ closeChainFiber mtWord mtFiber64DirectStates mtFiber64DirectStates.length [mtFiber64StateAt 0] := by
  have h0 : mtFiber64StateAt 0 ∈ closeChainFiber mtWord mtFiber64DirectStates 0 [mtFiber64StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber64StateAt 8 ∈ closeChainFiber mtWord mtFiber64DirectStates 1 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 0 [mtFiber64StateAt 0]
      (mtFiber64StateAt 0) (mtFiber64StateAt 8) (by decide) h0 (by decide)
      mtFiber64ReverseSingleStep8
  change mtFiber64StateAt 8 ∈ closeChainFiber mtWord mtFiber64DirectStates (1 + 15) [mtFiber64StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber64DirectStates 1 15 [mtFiber64StateAt 0] (mtFiber64StateAt 8) h1

theorem mtFiber64State9_in_close :
    mtFiber64StateAt 9 ∈ closeChainFiber mtWord mtFiber64DirectStates mtFiber64DirectStates.length [mtFiber64StateAt 0] := by
  have h0 : mtFiber64StateAt 0 ∈ closeChainFiber mtWord mtFiber64DirectStates 0 [mtFiber64StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber64StateAt 1 ∈ closeChainFiber mtWord mtFiber64DirectStates 1 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 0 [mtFiber64StateAt 0]
      (mtFiber64StateAt 0) (mtFiber64StateAt 1) (by decide) h0 (by decide)
      mtFiber64ReverseSingleStep1
  have h2 : mtFiber64StateAt 9 ∈ closeChainFiber mtWord mtFiber64DirectStates 2 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 1 [mtFiber64StateAt 0]
      (mtFiber64StateAt 1) (mtFiber64StateAt 9) (by decide) h1 (by decide)
      mtFiber64ReverseSingleStep9
  change mtFiber64StateAt 9 ∈ closeChainFiber mtWord mtFiber64DirectStates (2 + 14) [mtFiber64StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber64DirectStates 2 14 [mtFiber64StateAt 0] (mtFiber64StateAt 9) h2

theorem mtFiber64State10_in_close :
    mtFiber64StateAt 10 ∈ closeChainFiber mtWord mtFiber64DirectStates mtFiber64DirectStates.length [mtFiber64StateAt 0] := by
  have h0 : mtFiber64StateAt 0 ∈ closeChainFiber mtWord mtFiber64DirectStates 0 [mtFiber64StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber64StateAt 2 ∈ closeChainFiber mtWord mtFiber64DirectStates 1 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 0 [mtFiber64StateAt 0]
      (mtFiber64StateAt 0) (mtFiber64StateAt 2) (by decide) h0 (by decide)
      mtFiber64ReverseSingleStep2
  have h2 : mtFiber64StateAt 10 ∈ closeChainFiber mtWord mtFiber64DirectStates 2 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 1 [mtFiber64StateAt 0]
      (mtFiber64StateAt 2) (mtFiber64StateAt 10) (by decide) h1 (by decide)
      mtFiber64ReverseSingleStep10
  change mtFiber64StateAt 10 ∈ closeChainFiber mtWord mtFiber64DirectStates (2 + 14) [mtFiber64StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber64DirectStates 2 14 [mtFiber64StateAt 0] (mtFiber64StateAt 10) h2

theorem mtFiber64State11_in_close :
    mtFiber64StateAt 11 ∈ closeChainFiber mtWord mtFiber64DirectStates mtFiber64DirectStates.length [mtFiber64StateAt 0] := by
  have h0 : mtFiber64StateAt 0 ∈ closeChainFiber mtWord mtFiber64DirectStates 0 [mtFiber64StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber64StateAt 1 ∈ closeChainFiber mtWord mtFiber64DirectStates 1 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 0 [mtFiber64StateAt 0]
      (mtFiber64StateAt 0) (mtFiber64StateAt 1) (by decide) h0 (by decide)
      mtFiber64ReverseSingleStep1
  have h2 : mtFiber64StateAt 3 ∈ closeChainFiber mtWord mtFiber64DirectStates 2 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 1 [mtFiber64StateAt 0]
      (mtFiber64StateAt 1) (mtFiber64StateAt 3) (by decide) h1 (by decide)
      mtFiber64ReverseSingleStep3
  have h3 : mtFiber64StateAt 11 ∈ closeChainFiber mtWord mtFiber64DirectStates 3 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 2 [mtFiber64StateAt 0]
      (mtFiber64StateAt 3) (mtFiber64StateAt 11) (by decide) h2 (by decide)
      mtFiber64ReverseSingleStep11
  change mtFiber64StateAt 11 ∈ closeChainFiber mtWord mtFiber64DirectStates (3 + 13) [mtFiber64StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber64DirectStates 3 13 [mtFiber64StateAt 0] (mtFiber64StateAt 11) h3

theorem mtFiber64State12_in_close :
    mtFiber64StateAt 12 ∈ closeChainFiber mtWord mtFiber64DirectStates mtFiber64DirectStates.length [mtFiber64StateAt 0] := by
  have h0 : mtFiber64StateAt 0 ∈ closeChainFiber mtWord mtFiber64DirectStates 0 [mtFiber64StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber64StateAt 4 ∈ closeChainFiber mtWord mtFiber64DirectStates 1 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 0 [mtFiber64StateAt 0]
      (mtFiber64StateAt 0) (mtFiber64StateAt 4) (by decide) h0 (by decide)
      mtFiber64ReverseSingleStep4
  have h2 : mtFiber64StateAt 12 ∈ closeChainFiber mtWord mtFiber64DirectStates 2 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 1 [mtFiber64StateAt 0]
      (mtFiber64StateAt 4) (mtFiber64StateAt 12) (by decide) h1 (by decide)
      mtFiber64ReverseSingleStep12
  change mtFiber64StateAt 12 ∈ closeChainFiber mtWord mtFiber64DirectStates (2 + 14) [mtFiber64StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber64DirectStates 2 14 [mtFiber64StateAt 0] (mtFiber64StateAt 12) h2

theorem mtFiber64State13_in_close :
    mtFiber64StateAt 13 ∈ closeChainFiber mtWord mtFiber64DirectStates mtFiber64DirectStates.length [mtFiber64StateAt 0] := by
  have h0 : mtFiber64StateAt 0 ∈ closeChainFiber mtWord mtFiber64DirectStates 0 [mtFiber64StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber64StateAt 1 ∈ closeChainFiber mtWord mtFiber64DirectStates 1 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 0 [mtFiber64StateAt 0]
      (mtFiber64StateAt 0) (mtFiber64StateAt 1) (by decide) h0 (by decide)
      mtFiber64ReverseSingleStep1
  have h2 : mtFiber64StateAt 5 ∈ closeChainFiber mtWord mtFiber64DirectStates 2 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 1 [mtFiber64StateAt 0]
      (mtFiber64StateAt 1) (mtFiber64StateAt 5) (by decide) h1 (by decide)
      mtFiber64ReverseSingleStep5
  have h3 : mtFiber64StateAt 13 ∈ closeChainFiber mtWord mtFiber64DirectStates 3 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 2 [mtFiber64StateAt 0]
      (mtFiber64StateAt 5) (mtFiber64StateAt 13) (by decide) h2 (by decide)
      mtFiber64ReverseSingleStep13
  change mtFiber64StateAt 13 ∈ closeChainFiber mtWord mtFiber64DirectStates (3 + 13) [mtFiber64StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber64DirectStates 3 13 [mtFiber64StateAt 0] (mtFiber64StateAt 13) h3

theorem mtFiber64State14_in_close :
    mtFiber64StateAt 14 ∈ closeChainFiber mtWord mtFiber64DirectStates mtFiber64DirectStates.length [mtFiber64StateAt 0] := by
  have h0 : mtFiber64StateAt 0 ∈ closeChainFiber mtWord mtFiber64DirectStates 0 [mtFiber64StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber64StateAt 2 ∈ closeChainFiber mtWord mtFiber64DirectStates 1 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 0 [mtFiber64StateAt 0]
      (mtFiber64StateAt 0) (mtFiber64StateAt 2) (by decide) h0 (by decide)
      mtFiber64ReverseSingleStep2
  have h2 : mtFiber64StateAt 6 ∈ closeChainFiber mtWord mtFiber64DirectStates 2 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 1 [mtFiber64StateAt 0]
      (mtFiber64StateAt 2) (mtFiber64StateAt 6) (by decide) h1 (by decide)
      mtFiber64ReverseSingleStep6
  have h3 : mtFiber64StateAt 14 ∈ closeChainFiber mtWord mtFiber64DirectStates 3 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 2 [mtFiber64StateAt 0]
      (mtFiber64StateAt 6) (mtFiber64StateAt 14) (by decide) h2 (by decide)
      mtFiber64ReverseSingleStep14
  change mtFiber64StateAt 14 ∈ closeChainFiber mtWord mtFiber64DirectStates (3 + 13) [mtFiber64StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber64DirectStates 3 13 [mtFiber64StateAt 0] (mtFiber64StateAt 14) h3

theorem mtFiber64State15_in_close :
    mtFiber64StateAt 15 ∈ closeChainFiber mtWord mtFiber64DirectStates mtFiber64DirectStates.length [mtFiber64StateAt 0] := by
  have h0 : mtFiber64StateAt 0 ∈ closeChainFiber mtWord mtFiber64DirectStates 0 [mtFiber64StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber64StateAt 1 ∈ closeChainFiber mtWord mtFiber64DirectStates 1 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 0 [mtFiber64StateAt 0]
      (mtFiber64StateAt 0) (mtFiber64StateAt 1) (by decide) h0 (by decide)
      mtFiber64ReverseSingleStep1
  have h2 : mtFiber64StateAt 3 ∈ closeChainFiber mtWord mtFiber64DirectStates 2 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 1 [mtFiber64StateAt 0]
      (mtFiber64StateAt 1) (mtFiber64StateAt 3) (by decide) h1 (by decide)
      mtFiber64ReverseSingleStep3
  have h3 : mtFiber64StateAt 7 ∈ closeChainFiber mtWord mtFiber64DirectStates 3 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 2 [mtFiber64StateAt 0]
      (mtFiber64StateAt 3) (mtFiber64StateAt 7) (by decide) h2 (by decide)
      mtFiber64ReverseSingleStep7
  have h4 : mtFiber64StateAt 15 ∈ closeChainFiber mtWord mtFiber64DirectStates 4 [mtFiber64StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber64DirectStates 3 [mtFiber64StateAt 0]
      (mtFiber64StateAt 7) (mtFiber64StateAt 15) (by decide) h3 (by decide)
      mtFiber64ReverseSingleStep15
  change mtFiber64StateAt 15 ∈ closeChainFiber mtWord mtFiber64DirectStates (4 + 12) [mtFiber64StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber64DirectStates 4 12 [mtFiber64StateAt 0] (mtFiber64StateAt 15) h4

theorem mtFiber64DirectConnected :
    chainFiberConnected mtWord mtFiber64DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber64DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber64State0_in_close
  · subst state
    exact mtFiber64State1_in_close
  · subst state
    exact mtFiber64State2_in_close
  · subst state
    exact mtFiber64State3_in_close
  · subst state
    exact mtFiber64State4_in_close
  · subst state
    exact mtFiber64State5_in_close
  · subst state
    exact mtFiber64State6_in_close
  · subst state
    exact mtFiber64State7_in_close
  · subst state
    exact mtFiber64State8_in_close
  · subst state
    exact mtFiber64State9_in_close
  · subst state
    exact mtFiber64State10_in_close
  · subst state
    exact mtFiber64State11_in_close
  · subst state
    exact mtFiber64State12_in_close
  · subst state
    exact mtFiber64State13_in_close
  · subst state
    exact mtFiber64State14_in_close
  · subst state
    exact mtFiber64State15_in_close
  · cases h
def mtFiber71StateAt (i : Nat) : List TauState :=
  directStates (mtFiber71RowAt i).sourceLeft (mtFiber71RowAt i).sourceRight

def mtFiber71DirectStates : List (List TauState) :=
  [mtFiber71StateAt 0, mtFiber71StateAt 1, mtFiber71StateAt 2, mtFiber71StateAt 3, mtFiber71StateAt 4, mtFiber71StateAt 5, mtFiber71StateAt 6, mtFiber71StateAt 7, mtFiber71StateAt 8, mtFiber71StateAt 9, mtFiber71StateAt 10, mtFiber71StateAt 11, mtFiber71StateAt 12, mtFiber71StateAt 13, mtFiber71StateAt 14, mtFiber71StateAt 15]

theorem mtFiber71ReverseRow_1_ok :
    mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber71Chunk0_ok
  change (mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 0) &&
    mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber71ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber71StateAt 0) (mtFiber71StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber71StateAt 0) (mtFiber71StateAt 1)
    (mtFiber71RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber71Key mtFiber71Expected
        (mtFiber71RowAt 1) (by decide) mtFiber71ReverseRow_1_ok
      simpa [mtFiber71StateAt, mtFiber71RowAt, mtFiber71Rows, listGetD, directRow] using h)

theorem mtFiber71ReverseRow_2_ok :
    mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber71Chunk1_ok
  change (mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 2) &&
    mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber71ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber71StateAt 1) (mtFiber71StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber71StateAt 1) (mtFiber71StateAt 2)
    (mtFiber71RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber71Key mtFiber71Expected
        (mtFiber71RowAt 2) (by decide) mtFiber71ReverseRow_2_ok
      simpa [mtFiber71StateAt, mtFiber71RowAt, mtFiber71Rows, listGetD, directRow] using h)

theorem mtFiber71ReverseRow_3_ok :
    mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber71Chunk1_ok
  change (mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 2) &&
    mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber71ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber71StateAt 0) (mtFiber71StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber71StateAt 0) (mtFiber71StateAt 3)
    (mtFiber71RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber71Key mtFiber71Expected
        (mtFiber71RowAt 3) (by decide) mtFiber71ReverseRow_3_ok
      simpa [mtFiber71StateAt, mtFiber71RowAt, mtFiber71Rows, listGetD, directRow] using h)

theorem mtFiber71ReverseRow_4_ok :
    mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber71Chunk2_ok
  change (mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 4) &&
    mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber71ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber71StateAt 0) (mtFiber71StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber71StateAt 0) (mtFiber71StateAt 4)
    (mtFiber71RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber71Key mtFiber71Expected
        (mtFiber71RowAt 4) (by decide) mtFiber71ReverseRow_4_ok
      simpa [mtFiber71StateAt, mtFiber71RowAt, mtFiber71Rows, listGetD, directRow] using h)

theorem mtFiber71ReverseRow_5_ok :
    mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber71Chunk2_ok
  change (mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 4) &&
    mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber71ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber71StateAt 1) (mtFiber71StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber71StateAt 1) (mtFiber71StateAt 5)
    (mtFiber71RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber71Key mtFiber71Expected
        (mtFiber71RowAt 5) (by decide) mtFiber71ReverseRow_5_ok
      simpa [mtFiber71StateAt, mtFiber71RowAt, mtFiber71Rows, listGetD, directRow] using h)

theorem mtFiber71ReverseRow_6_ok :
    mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber71Chunk3_ok
  change (mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 6) &&
    mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber71ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber71StateAt 2) (mtFiber71StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber71StateAt 2) (mtFiber71StateAt 6)
    (mtFiber71RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber71Key mtFiber71Expected
        (mtFiber71RowAt 6) (by decide) mtFiber71ReverseRow_6_ok
      simpa [mtFiber71StateAt, mtFiber71RowAt, mtFiber71Rows, listGetD, directRow] using h)

theorem mtFiber71ReverseRow_7_ok :
    mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber71Chunk3_ok
  change (mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 6) &&
    mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber71ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber71StateAt 3) (mtFiber71StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber71StateAt 3) (mtFiber71StateAt 7)
    (mtFiber71RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber71Key mtFiber71Expected
        (mtFiber71RowAt 7) (by decide) mtFiber71ReverseRow_7_ok
      simpa [mtFiber71StateAt, mtFiber71RowAt, mtFiber71Rows, listGetD, directRow] using h)

theorem mtFiber71ReverseRow_8_ok :
    mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber71Chunk4_ok
  change (mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 8) &&
    mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber71ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber71StateAt 0) (mtFiber71StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber71StateAt 0) (mtFiber71StateAt 8)
    (mtFiber71RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber71Key mtFiber71Expected
        (mtFiber71RowAt 8) (by decide) mtFiber71ReverseRow_8_ok
      simpa [mtFiber71StateAt, mtFiber71RowAt, mtFiber71Rows, listGetD, directRow] using h)

theorem mtFiber71ReverseRow_9_ok :
    mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber71Chunk4_ok
  change (mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 8) &&
    mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber71ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber71StateAt 1) (mtFiber71StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber71StateAt 1) (mtFiber71StateAt 9)
    (mtFiber71RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber71Key mtFiber71Expected
        (mtFiber71RowAt 9) (by decide) mtFiber71ReverseRow_9_ok
      simpa [mtFiber71StateAt, mtFiber71RowAt, mtFiber71Rows, listGetD, directRow] using h)

theorem mtFiber71ReverseRow_10_ok :
    mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber71Chunk5_ok
  change (mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 10) &&
    mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber71ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber71StateAt 2) (mtFiber71StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber71StateAt 2) (mtFiber71StateAt 10)
    (mtFiber71RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber71Key mtFiber71Expected
        (mtFiber71RowAt 10) (by decide) mtFiber71ReverseRow_10_ok
      simpa [mtFiber71StateAt, mtFiber71RowAt, mtFiber71Rows, listGetD, directRow] using h)

theorem mtFiber71ReverseRow_11_ok :
    mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber71Chunk5_ok
  change (mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 10) &&
    mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber71ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber71StateAt 3) (mtFiber71StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber71StateAt 3) (mtFiber71StateAt 11)
    (mtFiber71RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber71Key mtFiber71Expected
        (mtFiber71RowAt 11) (by decide) mtFiber71ReverseRow_11_ok
      simpa [mtFiber71StateAt, mtFiber71RowAt, mtFiber71Rows, listGetD, directRow] using h)

theorem mtFiber71ReverseRow_12_ok :
    mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber71Chunk6_ok
  change (mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 12) &&
    mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber71ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber71StateAt 4) (mtFiber71StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber71StateAt 4) (mtFiber71StateAt 12)
    (mtFiber71RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber71Key mtFiber71Expected
        (mtFiber71RowAt 12) (by decide) mtFiber71ReverseRow_12_ok
      simpa [mtFiber71StateAt, mtFiber71RowAt, mtFiber71Rows, listGetD, directRow] using h)

theorem mtFiber71ReverseRow_13_ok :
    mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber71Chunk6_ok
  change (mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 12) &&
    mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber71ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber71StateAt 5) (mtFiber71StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber71StateAt 5) (mtFiber71StateAt 13)
    (mtFiber71RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber71Key mtFiber71Expected
        (mtFiber71RowAt 13) (by decide) mtFiber71ReverseRow_13_ok
      simpa [mtFiber71StateAt, mtFiber71RowAt, mtFiber71Rows, listGetD, directRow] using h)

theorem mtFiber71ReverseRow_14_ok :
    mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber71Chunk7_ok
  change (mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 14) &&
    mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber71ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber71StateAt 6) (mtFiber71StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber71StateAt 6) (mtFiber71StateAt 14)
    (mtFiber71RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber71Key mtFiber71Expected
        (mtFiber71RowAt 14) (by decide) mtFiber71ReverseRow_14_ok
      simpa [mtFiber71StateAt, mtFiber71RowAt, mtFiber71Rows, listGetD, directRow] using h)

theorem mtFiber71ReverseRow_15_ok :
    mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber71Chunk7_ok
  change (mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 14) &&
    mtRowReverseValid mtFiber71Key mtFiber71Expected (mtFiber71RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber71ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber71StateAt 7) (mtFiber71StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber71StateAt 7) (mtFiber71StateAt 15)
    (mtFiber71RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber71Key mtFiber71Expected
        (mtFiber71RowAt 15) (by decide) mtFiber71ReverseRow_15_ok
      simpa [mtFiber71StateAt, mtFiber71RowAt, mtFiber71Rows, listGetD, directRow] using h)

theorem mtFiber71State0_in_close :
    mtFiber71StateAt 0 ∈ closeChainFiber mtWord mtFiber71DirectStates mtFiber71DirectStates.length [mtFiber71StateAt 0] := by
  change mtFiber71StateAt 0 ∈ closeChainFiber mtWord mtFiber71DirectStates 16 [mtFiber71StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber71DirectStates 0 16 [mtFiber71StateAt 0] (mtFiber71StateAt 0) (by simp [closeChainFiber])

theorem mtFiber71State1_in_close :
    mtFiber71StateAt 1 ∈ closeChainFiber mtWord mtFiber71DirectStates mtFiber71DirectStates.length [mtFiber71StateAt 0] := by
  have h0 : mtFiber71StateAt 0 ∈ closeChainFiber mtWord mtFiber71DirectStates 0 [mtFiber71StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber71StateAt 1 ∈ closeChainFiber mtWord mtFiber71DirectStates 1 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 0 [mtFiber71StateAt 0]
      (mtFiber71StateAt 0) (mtFiber71StateAt 1) (by decide) h0 (by decide)
      mtFiber71ReverseSingleStep1
  change mtFiber71StateAt 1 ∈ closeChainFiber mtWord mtFiber71DirectStates (1 + 15) [mtFiber71StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber71DirectStates 1 15 [mtFiber71StateAt 0] (mtFiber71StateAt 1) h1

theorem mtFiber71State2_in_close :
    mtFiber71StateAt 2 ∈ closeChainFiber mtWord mtFiber71DirectStates mtFiber71DirectStates.length [mtFiber71StateAt 0] := by
  have h0 : mtFiber71StateAt 0 ∈ closeChainFiber mtWord mtFiber71DirectStates 0 [mtFiber71StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber71StateAt 1 ∈ closeChainFiber mtWord mtFiber71DirectStates 1 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 0 [mtFiber71StateAt 0]
      (mtFiber71StateAt 0) (mtFiber71StateAt 1) (by decide) h0 (by decide)
      mtFiber71ReverseSingleStep1
  have h2 : mtFiber71StateAt 2 ∈ closeChainFiber mtWord mtFiber71DirectStates 2 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 1 [mtFiber71StateAt 0]
      (mtFiber71StateAt 1) (mtFiber71StateAt 2) (by decide) h1 (by decide)
      mtFiber71ReverseSingleStep2
  change mtFiber71StateAt 2 ∈ closeChainFiber mtWord mtFiber71DirectStates (2 + 14) [mtFiber71StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber71DirectStates 2 14 [mtFiber71StateAt 0] (mtFiber71StateAt 2) h2

theorem mtFiber71State3_in_close :
    mtFiber71StateAt 3 ∈ closeChainFiber mtWord mtFiber71DirectStates mtFiber71DirectStates.length [mtFiber71StateAt 0] := by
  have h0 : mtFiber71StateAt 0 ∈ closeChainFiber mtWord mtFiber71DirectStates 0 [mtFiber71StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber71StateAt 3 ∈ closeChainFiber mtWord mtFiber71DirectStates 1 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 0 [mtFiber71StateAt 0]
      (mtFiber71StateAt 0) (mtFiber71StateAt 3) (by decide) h0 (by decide)
      mtFiber71ReverseSingleStep3
  change mtFiber71StateAt 3 ∈ closeChainFiber mtWord mtFiber71DirectStates (1 + 15) [mtFiber71StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber71DirectStates 1 15 [mtFiber71StateAt 0] (mtFiber71StateAt 3) h1

theorem mtFiber71State4_in_close :
    mtFiber71StateAt 4 ∈ closeChainFiber mtWord mtFiber71DirectStates mtFiber71DirectStates.length [mtFiber71StateAt 0] := by
  have h0 : mtFiber71StateAt 0 ∈ closeChainFiber mtWord mtFiber71DirectStates 0 [mtFiber71StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber71StateAt 4 ∈ closeChainFiber mtWord mtFiber71DirectStates 1 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 0 [mtFiber71StateAt 0]
      (mtFiber71StateAt 0) (mtFiber71StateAt 4) (by decide) h0 (by decide)
      mtFiber71ReverseSingleStep4
  change mtFiber71StateAt 4 ∈ closeChainFiber mtWord mtFiber71DirectStates (1 + 15) [mtFiber71StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber71DirectStates 1 15 [mtFiber71StateAt 0] (mtFiber71StateAt 4) h1

theorem mtFiber71State5_in_close :
    mtFiber71StateAt 5 ∈ closeChainFiber mtWord mtFiber71DirectStates mtFiber71DirectStates.length [mtFiber71StateAt 0] := by
  have h0 : mtFiber71StateAt 0 ∈ closeChainFiber mtWord mtFiber71DirectStates 0 [mtFiber71StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber71StateAt 1 ∈ closeChainFiber mtWord mtFiber71DirectStates 1 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 0 [mtFiber71StateAt 0]
      (mtFiber71StateAt 0) (mtFiber71StateAt 1) (by decide) h0 (by decide)
      mtFiber71ReverseSingleStep1
  have h2 : mtFiber71StateAt 5 ∈ closeChainFiber mtWord mtFiber71DirectStates 2 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 1 [mtFiber71StateAt 0]
      (mtFiber71StateAt 1) (mtFiber71StateAt 5) (by decide) h1 (by decide)
      mtFiber71ReverseSingleStep5
  change mtFiber71StateAt 5 ∈ closeChainFiber mtWord mtFiber71DirectStates (2 + 14) [mtFiber71StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber71DirectStates 2 14 [mtFiber71StateAt 0] (mtFiber71StateAt 5) h2

theorem mtFiber71State6_in_close :
    mtFiber71StateAt 6 ∈ closeChainFiber mtWord mtFiber71DirectStates mtFiber71DirectStates.length [mtFiber71StateAt 0] := by
  have h0 : mtFiber71StateAt 0 ∈ closeChainFiber mtWord mtFiber71DirectStates 0 [mtFiber71StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber71StateAt 1 ∈ closeChainFiber mtWord mtFiber71DirectStates 1 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 0 [mtFiber71StateAt 0]
      (mtFiber71StateAt 0) (mtFiber71StateAt 1) (by decide) h0 (by decide)
      mtFiber71ReverseSingleStep1
  have h2 : mtFiber71StateAt 2 ∈ closeChainFiber mtWord mtFiber71DirectStates 2 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 1 [mtFiber71StateAt 0]
      (mtFiber71StateAt 1) (mtFiber71StateAt 2) (by decide) h1 (by decide)
      mtFiber71ReverseSingleStep2
  have h3 : mtFiber71StateAt 6 ∈ closeChainFiber mtWord mtFiber71DirectStates 3 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 2 [mtFiber71StateAt 0]
      (mtFiber71StateAt 2) (mtFiber71StateAt 6) (by decide) h2 (by decide)
      mtFiber71ReverseSingleStep6
  change mtFiber71StateAt 6 ∈ closeChainFiber mtWord mtFiber71DirectStates (3 + 13) [mtFiber71StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber71DirectStates 3 13 [mtFiber71StateAt 0] (mtFiber71StateAt 6) h3

theorem mtFiber71State7_in_close :
    mtFiber71StateAt 7 ∈ closeChainFiber mtWord mtFiber71DirectStates mtFiber71DirectStates.length [mtFiber71StateAt 0] := by
  have h0 : mtFiber71StateAt 0 ∈ closeChainFiber mtWord mtFiber71DirectStates 0 [mtFiber71StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber71StateAt 3 ∈ closeChainFiber mtWord mtFiber71DirectStates 1 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 0 [mtFiber71StateAt 0]
      (mtFiber71StateAt 0) (mtFiber71StateAt 3) (by decide) h0 (by decide)
      mtFiber71ReverseSingleStep3
  have h2 : mtFiber71StateAt 7 ∈ closeChainFiber mtWord mtFiber71DirectStates 2 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 1 [mtFiber71StateAt 0]
      (mtFiber71StateAt 3) (mtFiber71StateAt 7) (by decide) h1 (by decide)
      mtFiber71ReverseSingleStep7
  change mtFiber71StateAt 7 ∈ closeChainFiber mtWord mtFiber71DirectStates (2 + 14) [mtFiber71StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber71DirectStates 2 14 [mtFiber71StateAt 0] (mtFiber71StateAt 7) h2

theorem mtFiber71State8_in_close :
    mtFiber71StateAt 8 ∈ closeChainFiber mtWord mtFiber71DirectStates mtFiber71DirectStates.length [mtFiber71StateAt 0] := by
  have h0 : mtFiber71StateAt 0 ∈ closeChainFiber mtWord mtFiber71DirectStates 0 [mtFiber71StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber71StateAt 8 ∈ closeChainFiber mtWord mtFiber71DirectStates 1 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 0 [mtFiber71StateAt 0]
      (mtFiber71StateAt 0) (mtFiber71StateAt 8) (by decide) h0 (by decide)
      mtFiber71ReverseSingleStep8
  change mtFiber71StateAt 8 ∈ closeChainFiber mtWord mtFiber71DirectStates (1 + 15) [mtFiber71StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber71DirectStates 1 15 [mtFiber71StateAt 0] (mtFiber71StateAt 8) h1

theorem mtFiber71State9_in_close :
    mtFiber71StateAt 9 ∈ closeChainFiber mtWord mtFiber71DirectStates mtFiber71DirectStates.length [mtFiber71StateAt 0] := by
  have h0 : mtFiber71StateAt 0 ∈ closeChainFiber mtWord mtFiber71DirectStates 0 [mtFiber71StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber71StateAt 1 ∈ closeChainFiber mtWord mtFiber71DirectStates 1 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 0 [mtFiber71StateAt 0]
      (mtFiber71StateAt 0) (mtFiber71StateAt 1) (by decide) h0 (by decide)
      mtFiber71ReverseSingleStep1
  have h2 : mtFiber71StateAt 9 ∈ closeChainFiber mtWord mtFiber71DirectStates 2 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 1 [mtFiber71StateAt 0]
      (mtFiber71StateAt 1) (mtFiber71StateAt 9) (by decide) h1 (by decide)
      mtFiber71ReverseSingleStep9
  change mtFiber71StateAt 9 ∈ closeChainFiber mtWord mtFiber71DirectStates (2 + 14) [mtFiber71StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber71DirectStates 2 14 [mtFiber71StateAt 0] (mtFiber71StateAt 9) h2

theorem mtFiber71State10_in_close :
    mtFiber71StateAt 10 ∈ closeChainFiber mtWord mtFiber71DirectStates mtFiber71DirectStates.length [mtFiber71StateAt 0] := by
  have h0 : mtFiber71StateAt 0 ∈ closeChainFiber mtWord mtFiber71DirectStates 0 [mtFiber71StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber71StateAt 1 ∈ closeChainFiber mtWord mtFiber71DirectStates 1 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 0 [mtFiber71StateAt 0]
      (mtFiber71StateAt 0) (mtFiber71StateAt 1) (by decide) h0 (by decide)
      mtFiber71ReverseSingleStep1
  have h2 : mtFiber71StateAt 2 ∈ closeChainFiber mtWord mtFiber71DirectStates 2 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 1 [mtFiber71StateAt 0]
      (mtFiber71StateAt 1) (mtFiber71StateAt 2) (by decide) h1 (by decide)
      mtFiber71ReverseSingleStep2
  have h3 : mtFiber71StateAt 10 ∈ closeChainFiber mtWord mtFiber71DirectStates 3 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 2 [mtFiber71StateAt 0]
      (mtFiber71StateAt 2) (mtFiber71StateAt 10) (by decide) h2 (by decide)
      mtFiber71ReverseSingleStep10
  change mtFiber71StateAt 10 ∈ closeChainFiber mtWord mtFiber71DirectStates (3 + 13) [mtFiber71StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber71DirectStates 3 13 [mtFiber71StateAt 0] (mtFiber71StateAt 10) h3

theorem mtFiber71State11_in_close :
    mtFiber71StateAt 11 ∈ closeChainFiber mtWord mtFiber71DirectStates mtFiber71DirectStates.length [mtFiber71StateAt 0] := by
  have h0 : mtFiber71StateAt 0 ∈ closeChainFiber mtWord mtFiber71DirectStates 0 [mtFiber71StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber71StateAt 3 ∈ closeChainFiber mtWord mtFiber71DirectStates 1 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 0 [mtFiber71StateAt 0]
      (mtFiber71StateAt 0) (mtFiber71StateAt 3) (by decide) h0 (by decide)
      mtFiber71ReverseSingleStep3
  have h2 : mtFiber71StateAt 11 ∈ closeChainFiber mtWord mtFiber71DirectStates 2 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 1 [mtFiber71StateAt 0]
      (mtFiber71StateAt 3) (mtFiber71StateAt 11) (by decide) h1 (by decide)
      mtFiber71ReverseSingleStep11
  change mtFiber71StateAt 11 ∈ closeChainFiber mtWord mtFiber71DirectStates (2 + 14) [mtFiber71StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber71DirectStates 2 14 [mtFiber71StateAt 0] (mtFiber71StateAt 11) h2

theorem mtFiber71State12_in_close :
    mtFiber71StateAt 12 ∈ closeChainFiber mtWord mtFiber71DirectStates mtFiber71DirectStates.length [mtFiber71StateAt 0] := by
  have h0 : mtFiber71StateAt 0 ∈ closeChainFiber mtWord mtFiber71DirectStates 0 [mtFiber71StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber71StateAt 4 ∈ closeChainFiber mtWord mtFiber71DirectStates 1 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 0 [mtFiber71StateAt 0]
      (mtFiber71StateAt 0) (mtFiber71StateAt 4) (by decide) h0 (by decide)
      mtFiber71ReverseSingleStep4
  have h2 : mtFiber71StateAt 12 ∈ closeChainFiber mtWord mtFiber71DirectStates 2 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 1 [mtFiber71StateAt 0]
      (mtFiber71StateAt 4) (mtFiber71StateAt 12) (by decide) h1 (by decide)
      mtFiber71ReverseSingleStep12
  change mtFiber71StateAt 12 ∈ closeChainFiber mtWord mtFiber71DirectStates (2 + 14) [mtFiber71StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber71DirectStates 2 14 [mtFiber71StateAt 0] (mtFiber71StateAt 12) h2

theorem mtFiber71State13_in_close :
    mtFiber71StateAt 13 ∈ closeChainFiber mtWord mtFiber71DirectStates mtFiber71DirectStates.length [mtFiber71StateAt 0] := by
  have h0 : mtFiber71StateAt 0 ∈ closeChainFiber mtWord mtFiber71DirectStates 0 [mtFiber71StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber71StateAt 1 ∈ closeChainFiber mtWord mtFiber71DirectStates 1 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 0 [mtFiber71StateAt 0]
      (mtFiber71StateAt 0) (mtFiber71StateAt 1) (by decide) h0 (by decide)
      mtFiber71ReverseSingleStep1
  have h2 : mtFiber71StateAt 5 ∈ closeChainFiber mtWord mtFiber71DirectStates 2 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 1 [mtFiber71StateAt 0]
      (mtFiber71StateAt 1) (mtFiber71StateAt 5) (by decide) h1 (by decide)
      mtFiber71ReverseSingleStep5
  have h3 : mtFiber71StateAt 13 ∈ closeChainFiber mtWord mtFiber71DirectStates 3 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 2 [mtFiber71StateAt 0]
      (mtFiber71StateAt 5) (mtFiber71StateAt 13) (by decide) h2 (by decide)
      mtFiber71ReverseSingleStep13
  change mtFiber71StateAt 13 ∈ closeChainFiber mtWord mtFiber71DirectStates (3 + 13) [mtFiber71StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber71DirectStates 3 13 [mtFiber71StateAt 0] (mtFiber71StateAt 13) h3

theorem mtFiber71State14_in_close :
    mtFiber71StateAt 14 ∈ closeChainFiber mtWord mtFiber71DirectStates mtFiber71DirectStates.length [mtFiber71StateAt 0] := by
  have h0 : mtFiber71StateAt 0 ∈ closeChainFiber mtWord mtFiber71DirectStates 0 [mtFiber71StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber71StateAt 1 ∈ closeChainFiber mtWord mtFiber71DirectStates 1 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 0 [mtFiber71StateAt 0]
      (mtFiber71StateAt 0) (mtFiber71StateAt 1) (by decide) h0 (by decide)
      mtFiber71ReverseSingleStep1
  have h2 : mtFiber71StateAt 2 ∈ closeChainFiber mtWord mtFiber71DirectStates 2 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 1 [mtFiber71StateAt 0]
      (mtFiber71StateAt 1) (mtFiber71StateAt 2) (by decide) h1 (by decide)
      mtFiber71ReverseSingleStep2
  have h3 : mtFiber71StateAt 6 ∈ closeChainFiber mtWord mtFiber71DirectStates 3 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 2 [mtFiber71StateAt 0]
      (mtFiber71StateAt 2) (mtFiber71StateAt 6) (by decide) h2 (by decide)
      mtFiber71ReverseSingleStep6
  have h4 : mtFiber71StateAt 14 ∈ closeChainFiber mtWord mtFiber71DirectStates 4 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 3 [mtFiber71StateAt 0]
      (mtFiber71StateAt 6) (mtFiber71StateAt 14) (by decide) h3 (by decide)
      mtFiber71ReverseSingleStep14
  change mtFiber71StateAt 14 ∈ closeChainFiber mtWord mtFiber71DirectStates (4 + 12) [mtFiber71StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber71DirectStates 4 12 [mtFiber71StateAt 0] (mtFiber71StateAt 14) h4

theorem mtFiber71State15_in_close :
    mtFiber71StateAt 15 ∈ closeChainFiber mtWord mtFiber71DirectStates mtFiber71DirectStates.length [mtFiber71StateAt 0] := by
  have h0 : mtFiber71StateAt 0 ∈ closeChainFiber mtWord mtFiber71DirectStates 0 [mtFiber71StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber71StateAt 3 ∈ closeChainFiber mtWord mtFiber71DirectStates 1 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 0 [mtFiber71StateAt 0]
      (mtFiber71StateAt 0) (mtFiber71StateAt 3) (by decide) h0 (by decide)
      mtFiber71ReverseSingleStep3
  have h2 : mtFiber71StateAt 7 ∈ closeChainFiber mtWord mtFiber71DirectStates 2 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 1 [mtFiber71StateAt 0]
      (mtFiber71StateAt 3) (mtFiber71StateAt 7) (by decide) h1 (by decide)
      mtFiber71ReverseSingleStep7
  have h3 : mtFiber71StateAt 15 ∈ closeChainFiber mtWord mtFiber71DirectStates 3 [mtFiber71StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber71DirectStates 2 [mtFiber71StateAt 0]
      (mtFiber71StateAt 7) (mtFiber71StateAt 15) (by decide) h2 (by decide)
      mtFiber71ReverseSingleStep15
  change mtFiber71StateAt 15 ∈ closeChainFiber mtWord mtFiber71DirectStates (3 + 13) [mtFiber71StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber71DirectStates 3 13 [mtFiber71StateAt 0] (mtFiber71StateAt 15) h3

theorem mtFiber71DirectConnected :
    chainFiberConnected mtWord mtFiber71DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber71DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber71State0_in_close
  · subst state
    exact mtFiber71State1_in_close
  · subst state
    exact mtFiber71State2_in_close
  · subst state
    exact mtFiber71State3_in_close
  · subst state
    exact mtFiber71State4_in_close
  · subst state
    exact mtFiber71State5_in_close
  · subst state
    exact mtFiber71State6_in_close
  · subst state
    exact mtFiber71State7_in_close
  · subst state
    exact mtFiber71State8_in_close
  · subst state
    exact mtFiber71State9_in_close
  · subst state
    exact mtFiber71State10_in_close
  · subst state
    exact mtFiber71State11_in_close
  · subst state
    exact mtFiber71State12_in_close
  · subst state
    exact mtFiber71State13_in_close
  · subst state
    exact mtFiber71State14_in_close
  · subst state
    exact mtFiber71State15_in_close
  · cases h
def mtFiber74StateAt (i : Nat) : List TauState :=
  directStates (mtFiber74RowAt i).sourceLeft (mtFiber74RowAt i).sourceRight

def mtFiber74DirectStates : List (List TauState) :=
  [mtFiber74StateAt 0, mtFiber74StateAt 1, mtFiber74StateAt 2, mtFiber74StateAt 3, mtFiber74StateAt 4, mtFiber74StateAt 5, mtFiber74StateAt 6, mtFiber74StateAt 7, mtFiber74StateAt 8, mtFiber74StateAt 9, mtFiber74StateAt 10, mtFiber74StateAt 11, mtFiber74StateAt 12, mtFiber74StateAt 13, mtFiber74StateAt 14, mtFiber74StateAt 15]

theorem mtFiber74ReverseRow_1_ok :
    mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber74Chunk0_ok
  change (mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 0) &&
    mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber74ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber74StateAt 0) (mtFiber74StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber74StateAt 0) (mtFiber74StateAt 1)
    (mtFiber74RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber74Key mtFiber74Expected
        (mtFiber74RowAt 1) (by decide) mtFiber74ReverseRow_1_ok
      simpa [mtFiber74StateAt, mtFiber74RowAt, mtFiber74Rows, listGetD, directRow] using h)

theorem mtFiber74ReverseRow_2_ok :
    mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber74Chunk1_ok
  change (mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 2) &&
    mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber74ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber74StateAt 0) (mtFiber74StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber74StateAt 0) (mtFiber74StateAt 2)
    (mtFiber74RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber74Key mtFiber74Expected
        (mtFiber74RowAt 2) (by decide) mtFiber74ReverseRow_2_ok
      simpa [mtFiber74StateAt, mtFiber74RowAt, mtFiber74Rows, listGetD, directRow] using h)

theorem mtFiber74ReverseRow_3_ok :
    mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber74Chunk1_ok
  change (mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 2) &&
    mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber74ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber74StateAt 1) (mtFiber74StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber74StateAt 1) (mtFiber74StateAt 3)
    (mtFiber74RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber74Key mtFiber74Expected
        (mtFiber74RowAt 3) (by decide) mtFiber74ReverseRow_3_ok
      simpa [mtFiber74StateAt, mtFiber74RowAt, mtFiber74Rows, listGetD, directRow] using h)

theorem mtFiber74ReverseRow_4_ok :
    mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber74Chunk2_ok
  change (mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 4) &&
    mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber74ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber74StateAt 0) (mtFiber74StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber74StateAt 0) (mtFiber74StateAt 4)
    (mtFiber74RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber74Key mtFiber74Expected
        (mtFiber74RowAt 4) (by decide) mtFiber74ReverseRow_4_ok
      simpa [mtFiber74StateAt, mtFiber74RowAt, mtFiber74Rows, listGetD, directRow] using h)

theorem mtFiber74ReverseRow_5_ok :
    mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber74Chunk2_ok
  change (mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 4) &&
    mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber74ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber74StateAt 1) (mtFiber74StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber74StateAt 1) (mtFiber74StateAt 5)
    (mtFiber74RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber74Key mtFiber74Expected
        (mtFiber74RowAt 5) (by decide) mtFiber74ReverseRow_5_ok
      simpa [mtFiber74StateAt, mtFiber74RowAt, mtFiber74Rows, listGetD, directRow] using h)

theorem mtFiber74ReverseRow_6_ok :
    mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber74Chunk3_ok
  change (mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 6) &&
    mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber74ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber74StateAt 2) (mtFiber74StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber74StateAt 2) (mtFiber74StateAt 6)
    (mtFiber74RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber74Key mtFiber74Expected
        (mtFiber74RowAt 6) (by decide) mtFiber74ReverseRow_6_ok
      simpa [mtFiber74StateAt, mtFiber74RowAt, mtFiber74Rows, listGetD, directRow] using h)

theorem mtFiber74ReverseRow_7_ok :
    mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber74Chunk3_ok
  change (mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 6) &&
    mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber74ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber74StateAt 3) (mtFiber74StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber74StateAt 3) (mtFiber74StateAt 7)
    (mtFiber74RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber74Key mtFiber74Expected
        (mtFiber74RowAt 7) (by decide) mtFiber74ReverseRow_7_ok
      simpa [mtFiber74StateAt, mtFiber74RowAt, mtFiber74Rows, listGetD, directRow] using h)

theorem mtFiber74ReverseRow_8_ok :
    mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber74Chunk4_ok
  change (mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 8) &&
    mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber74ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber74StateAt 0) (mtFiber74StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber74StateAt 0) (mtFiber74StateAt 8)
    (mtFiber74RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber74Key mtFiber74Expected
        (mtFiber74RowAt 8) (by decide) mtFiber74ReverseRow_8_ok
      simpa [mtFiber74StateAt, mtFiber74RowAt, mtFiber74Rows, listGetD, directRow] using h)

theorem mtFiber74ReverseRow_9_ok :
    mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber74Chunk4_ok
  change (mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 8) &&
    mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber74ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber74StateAt 1) (mtFiber74StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber74StateAt 1) (mtFiber74StateAt 9)
    (mtFiber74RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber74Key mtFiber74Expected
        (mtFiber74RowAt 9) (by decide) mtFiber74ReverseRow_9_ok
      simpa [mtFiber74StateAt, mtFiber74RowAt, mtFiber74Rows, listGetD, directRow] using h)

theorem mtFiber74ReverseRow_10_ok :
    mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber74Chunk5_ok
  change (mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 10) &&
    mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber74ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber74StateAt 2) (mtFiber74StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber74StateAt 2) (mtFiber74StateAt 10)
    (mtFiber74RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber74Key mtFiber74Expected
        (mtFiber74RowAt 10) (by decide) mtFiber74ReverseRow_10_ok
      simpa [mtFiber74StateAt, mtFiber74RowAt, mtFiber74Rows, listGetD, directRow] using h)

theorem mtFiber74ReverseRow_11_ok :
    mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber74Chunk5_ok
  change (mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 10) &&
    mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber74ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber74StateAt 3) (mtFiber74StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber74StateAt 3) (mtFiber74StateAt 11)
    (mtFiber74RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber74Key mtFiber74Expected
        (mtFiber74RowAt 11) (by decide) mtFiber74ReverseRow_11_ok
      simpa [mtFiber74StateAt, mtFiber74RowAt, mtFiber74Rows, listGetD, directRow] using h)

theorem mtFiber74ReverseRow_12_ok :
    mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber74Chunk6_ok
  change (mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 12) &&
    mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber74ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber74StateAt 4) (mtFiber74StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber74StateAt 4) (mtFiber74StateAt 12)
    (mtFiber74RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber74Key mtFiber74Expected
        (mtFiber74RowAt 12) (by decide) mtFiber74ReverseRow_12_ok
      simpa [mtFiber74StateAt, mtFiber74RowAt, mtFiber74Rows, listGetD, directRow] using h)

theorem mtFiber74ReverseRow_13_ok :
    mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber74Chunk6_ok
  change (mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 12) &&
    mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber74ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber74StateAt 5) (mtFiber74StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber74StateAt 5) (mtFiber74StateAt 13)
    (mtFiber74RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber74Key mtFiber74Expected
        (mtFiber74RowAt 13) (by decide) mtFiber74ReverseRow_13_ok
      simpa [mtFiber74StateAt, mtFiber74RowAt, mtFiber74Rows, listGetD, directRow] using h)

theorem mtFiber74ReverseRow_14_ok :
    mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber74Chunk7_ok
  change (mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 14) &&
    mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber74ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber74StateAt 6) (mtFiber74StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber74StateAt 6) (mtFiber74StateAt 14)
    (mtFiber74RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber74Key mtFiber74Expected
        (mtFiber74RowAt 14) (by decide) mtFiber74ReverseRow_14_ok
      simpa [mtFiber74StateAt, mtFiber74RowAt, mtFiber74Rows, listGetD, directRow] using h)

theorem mtFiber74ReverseRow_15_ok :
    mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber74Chunk7_ok
  change (mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 14) &&
    mtRowReverseValid mtFiber74Key mtFiber74Expected (mtFiber74RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber74ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber74StateAt 7) (mtFiber74StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber74StateAt 7) (mtFiber74StateAt 15)
    (mtFiber74RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber74Key mtFiber74Expected
        (mtFiber74RowAt 15) (by decide) mtFiber74ReverseRow_15_ok
      simpa [mtFiber74StateAt, mtFiber74RowAt, mtFiber74Rows, listGetD, directRow] using h)

theorem mtFiber74State0_in_close :
    mtFiber74StateAt 0 ∈ closeChainFiber mtWord mtFiber74DirectStates mtFiber74DirectStates.length [mtFiber74StateAt 0] := by
  change mtFiber74StateAt 0 ∈ closeChainFiber mtWord mtFiber74DirectStates 16 [mtFiber74StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber74DirectStates 0 16 [mtFiber74StateAt 0] (mtFiber74StateAt 0) (by simp [closeChainFiber])

theorem mtFiber74State1_in_close :
    mtFiber74StateAt 1 ∈ closeChainFiber mtWord mtFiber74DirectStates mtFiber74DirectStates.length [mtFiber74StateAt 0] := by
  have h0 : mtFiber74StateAt 0 ∈ closeChainFiber mtWord mtFiber74DirectStates 0 [mtFiber74StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber74StateAt 1 ∈ closeChainFiber mtWord mtFiber74DirectStates 1 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 0 [mtFiber74StateAt 0]
      (mtFiber74StateAt 0) (mtFiber74StateAt 1) (by decide) h0 (by decide)
      mtFiber74ReverseSingleStep1
  change mtFiber74StateAt 1 ∈ closeChainFiber mtWord mtFiber74DirectStates (1 + 15) [mtFiber74StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber74DirectStates 1 15 [mtFiber74StateAt 0] (mtFiber74StateAt 1) h1

theorem mtFiber74State2_in_close :
    mtFiber74StateAt 2 ∈ closeChainFiber mtWord mtFiber74DirectStates mtFiber74DirectStates.length [mtFiber74StateAt 0] := by
  have h0 : mtFiber74StateAt 0 ∈ closeChainFiber mtWord mtFiber74DirectStates 0 [mtFiber74StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber74StateAt 2 ∈ closeChainFiber mtWord mtFiber74DirectStates 1 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 0 [mtFiber74StateAt 0]
      (mtFiber74StateAt 0) (mtFiber74StateAt 2) (by decide) h0 (by decide)
      mtFiber74ReverseSingleStep2
  change mtFiber74StateAt 2 ∈ closeChainFiber mtWord mtFiber74DirectStates (1 + 15) [mtFiber74StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber74DirectStates 1 15 [mtFiber74StateAt 0] (mtFiber74StateAt 2) h1

theorem mtFiber74State3_in_close :
    mtFiber74StateAt 3 ∈ closeChainFiber mtWord mtFiber74DirectStates mtFiber74DirectStates.length [mtFiber74StateAt 0] := by
  have h0 : mtFiber74StateAt 0 ∈ closeChainFiber mtWord mtFiber74DirectStates 0 [mtFiber74StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber74StateAt 1 ∈ closeChainFiber mtWord mtFiber74DirectStates 1 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 0 [mtFiber74StateAt 0]
      (mtFiber74StateAt 0) (mtFiber74StateAt 1) (by decide) h0 (by decide)
      mtFiber74ReverseSingleStep1
  have h2 : mtFiber74StateAt 3 ∈ closeChainFiber mtWord mtFiber74DirectStates 2 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 1 [mtFiber74StateAt 0]
      (mtFiber74StateAt 1) (mtFiber74StateAt 3) (by decide) h1 (by decide)
      mtFiber74ReverseSingleStep3
  change mtFiber74StateAt 3 ∈ closeChainFiber mtWord mtFiber74DirectStates (2 + 14) [mtFiber74StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber74DirectStates 2 14 [mtFiber74StateAt 0] (mtFiber74StateAt 3) h2

theorem mtFiber74State4_in_close :
    mtFiber74StateAt 4 ∈ closeChainFiber mtWord mtFiber74DirectStates mtFiber74DirectStates.length [mtFiber74StateAt 0] := by
  have h0 : mtFiber74StateAt 0 ∈ closeChainFiber mtWord mtFiber74DirectStates 0 [mtFiber74StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber74StateAt 4 ∈ closeChainFiber mtWord mtFiber74DirectStates 1 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 0 [mtFiber74StateAt 0]
      (mtFiber74StateAt 0) (mtFiber74StateAt 4) (by decide) h0 (by decide)
      mtFiber74ReverseSingleStep4
  change mtFiber74StateAt 4 ∈ closeChainFiber mtWord mtFiber74DirectStates (1 + 15) [mtFiber74StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber74DirectStates 1 15 [mtFiber74StateAt 0] (mtFiber74StateAt 4) h1

theorem mtFiber74State5_in_close :
    mtFiber74StateAt 5 ∈ closeChainFiber mtWord mtFiber74DirectStates mtFiber74DirectStates.length [mtFiber74StateAt 0] := by
  have h0 : mtFiber74StateAt 0 ∈ closeChainFiber mtWord mtFiber74DirectStates 0 [mtFiber74StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber74StateAt 1 ∈ closeChainFiber mtWord mtFiber74DirectStates 1 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 0 [mtFiber74StateAt 0]
      (mtFiber74StateAt 0) (mtFiber74StateAt 1) (by decide) h0 (by decide)
      mtFiber74ReverseSingleStep1
  have h2 : mtFiber74StateAt 5 ∈ closeChainFiber mtWord mtFiber74DirectStates 2 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 1 [mtFiber74StateAt 0]
      (mtFiber74StateAt 1) (mtFiber74StateAt 5) (by decide) h1 (by decide)
      mtFiber74ReverseSingleStep5
  change mtFiber74StateAt 5 ∈ closeChainFiber mtWord mtFiber74DirectStates (2 + 14) [mtFiber74StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber74DirectStates 2 14 [mtFiber74StateAt 0] (mtFiber74StateAt 5) h2

theorem mtFiber74State6_in_close :
    mtFiber74StateAt 6 ∈ closeChainFiber mtWord mtFiber74DirectStates mtFiber74DirectStates.length [mtFiber74StateAt 0] := by
  have h0 : mtFiber74StateAt 0 ∈ closeChainFiber mtWord mtFiber74DirectStates 0 [mtFiber74StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber74StateAt 2 ∈ closeChainFiber mtWord mtFiber74DirectStates 1 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 0 [mtFiber74StateAt 0]
      (mtFiber74StateAt 0) (mtFiber74StateAt 2) (by decide) h0 (by decide)
      mtFiber74ReverseSingleStep2
  have h2 : mtFiber74StateAt 6 ∈ closeChainFiber mtWord mtFiber74DirectStates 2 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 1 [mtFiber74StateAt 0]
      (mtFiber74StateAt 2) (mtFiber74StateAt 6) (by decide) h1 (by decide)
      mtFiber74ReverseSingleStep6
  change mtFiber74StateAt 6 ∈ closeChainFiber mtWord mtFiber74DirectStates (2 + 14) [mtFiber74StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber74DirectStates 2 14 [mtFiber74StateAt 0] (mtFiber74StateAt 6) h2

theorem mtFiber74State7_in_close :
    mtFiber74StateAt 7 ∈ closeChainFiber mtWord mtFiber74DirectStates mtFiber74DirectStates.length [mtFiber74StateAt 0] := by
  have h0 : mtFiber74StateAt 0 ∈ closeChainFiber mtWord mtFiber74DirectStates 0 [mtFiber74StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber74StateAt 1 ∈ closeChainFiber mtWord mtFiber74DirectStates 1 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 0 [mtFiber74StateAt 0]
      (mtFiber74StateAt 0) (mtFiber74StateAt 1) (by decide) h0 (by decide)
      mtFiber74ReverseSingleStep1
  have h2 : mtFiber74StateAt 3 ∈ closeChainFiber mtWord mtFiber74DirectStates 2 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 1 [mtFiber74StateAt 0]
      (mtFiber74StateAt 1) (mtFiber74StateAt 3) (by decide) h1 (by decide)
      mtFiber74ReverseSingleStep3
  have h3 : mtFiber74StateAt 7 ∈ closeChainFiber mtWord mtFiber74DirectStates 3 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 2 [mtFiber74StateAt 0]
      (mtFiber74StateAt 3) (mtFiber74StateAt 7) (by decide) h2 (by decide)
      mtFiber74ReverseSingleStep7
  change mtFiber74StateAt 7 ∈ closeChainFiber mtWord mtFiber74DirectStates (3 + 13) [mtFiber74StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber74DirectStates 3 13 [mtFiber74StateAt 0] (mtFiber74StateAt 7) h3

theorem mtFiber74State8_in_close :
    mtFiber74StateAt 8 ∈ closeChainFiber mtWord mtFiber74DirectStates mtFiber74DirectStates.length [mtFiber74StateAt 0] := by
  have h0 : mtFiber74StateAt 0 ∈ closeChainFiber mtWord mtFiber74DirectStates 0 [mtFiber74StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber74StateAt 8 ∈ closeChainFiber mtWord mtFiber74DirectStates 1 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 0 [mtFiber74StateAt 0]
      (mtFiber74StateAt 0) (mtFiber74StateAt 8) (by decide) h0 (by decide)
      mtFiber74ReverseSingleStep8
  change mtFiber74StateAt 8 ∈ closeChainFiber mtWord mtFiber74DirectStates (1 + 15) [mtFiber74StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber74DirectStates 1 15 [mtFiber74StateAt 0] (mtFiber74StateAt 8) h1

theorem mtFiber74State9_in_close :
    mtFiber74StateAt 9 ∈ closeChainFiber mtWord mtFiber74DirectStates mtFiber74DirectStates.length [mtFiber74StateAt 0] := by
  have h0 : mtFiber74StateAt 0 ∈ closeChainFiber mtWord mtFiber74DirectStates 0 [mtFiber74StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber74StateAt 1 ∈ closeChainFiber mtWord mtFiber74DirectStates 1 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 0 [mtFiber74StateAt 0]
      (mtFiber74StateAt 0) (mtFiber74StateAt 1) (by decide) h0 (by decide)
      mtFiber74ReverseSingleStep1
  have h2 : mtFiber74StateAt 9 ∈ closeChainFiber mtWord mtFiber74DirectStates 2 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 1 [mtFiber74StateAt 0]
      (mtFiber74StateAt 1) (mtFiber74StateAt 9) (by decide) h1 (by decide)
      mtFiber74ReverseSingleStep9
  change mtFiber74StateAt 9 ∈ closeChainFiber mtWord mtFiber74DirectStates (2 + 14) [mtFiber74StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber74DirectStates 2 14 [mtFiber74StateAt 0] (mtFiber74StateAt 9) h2

theorem mtFiber74State10_in_close :
    mtFiber74StateAt 10 ∈ closeChainFiber mtWord mtFiber74DirectStates mtFiber74DirectStates.length [mtFiber74StateAt 0] := by
  have h0 : mtFiber74StateAt 0 ∈ closeChainFiber mtWord mtFiber74DirectStates 0 [mtFiber74StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber74StateAt 2 ∈ closeChainFiber mtWord mtFiber74DirectStates 1 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 0 [mtFiber74StateAt 0]
      (mtFiber74StateAt 0) (mtFiber74StateAt 2) (by decide) h0 (by decide)
      mtFiber74ReverseSingleStep2
  have h2 : mtFiber74StateAt 10 ∈ closeChainFiber mtWord mtFiber74DirectStates 2 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 1 [mtFiber74StateAt 0]
      (mtFiber74StateAt 2) (mtFiber74StateAt 10) (by decide) h1 (by decide)
      mtFiber74ReverseSingleStep10
  change mtFiber74StateAt 10 ∈ closeChainFiber mtWord mtFiber74DirectStates (2 + 14) [mtFiber74StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber74DirectStates 2 14 [mtFiber74StateAt 0] (mtFiber74StateAt 10) h2

theorem mtFiber74State11_in_close :
    mtFiber74StateAt 11 ∈ closeChainFiber mtWord mtFiber74DirectStates mtFiber74DirectStates.length [mtFiber74StateAt 0] := by
  have h0 : mtFiber74StateAt 0 ∈ closeChainFiber mtWord mtFiber74DirectStates 0 [mtFiber74StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber74StateAt 1 ∈ closeChainFiber mtWord mtFiber74DirectStates 1 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 0 [mtFiber74StateAt 0]
      (mtFiber74StateAt 0) (mtFiber74StateAt 1) (by decide) h0 (by decide)
      mtFiber74ReverseSingleStep1
  have h2 : mtFiber74StateAt 3 ∈ closeChainFiber mtWord mtFiber74DirectStates 2 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 1 [mtFiber74StateAt 0]
      (mtFiber74StateAt 1) (mtFiber74StateAt 3) (by decide) h1 (by decide)
      mtFiber74ReverseSingleStep3
  have h3 : mtFiber74StateAt 11 ∈ closeChainFiber mtWord mtFiber74DirectStates 3 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 2 [mtFiber74StateAt 0]
      (mtFiber74StateAt 3) (mtFiber74StateAt 11) (by decide) h2 (by decide)
      mtFiber74ReverseSingleStep11
  change mtFiber74StateAt 11 ∈ closeChainFiber mtWord mtFiber74DirectStates (3 + 13) [mtFiber74StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber74DirectStates 3 13 [mtFiber74StateAt 0] (mtFiber74StateAt 11) h3

theorem mtFiber74State12_in_close :
    mtFiber74StateAt 12 ∈ closeChainFiber mtWord mtFiber74DirectStates mtFiber74DirectStates.length [mtFiber74StateAt 0] := by
  have h0 : mtFiber74StateAt 0 ∈ closeChainFiber mtWord mtFiber74DirectStates 0 [mtFiber74StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber74StateAt 4 ∈ closeChainFiber mtWord mtFiber74DirectStates 1 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 0 [mtFiber74StateAt 0]
      (mtFiber74StateAt 0) (mtFiber74StateAt 4) (by decide) h0 (by decide)
      mtFiber74ReverseSingleStep4
  have h2 : mtFiber74StateAt 12 ∈ closeChainFiber mtWord mtFiber74DirectStates 2 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 1 [mtFiber74StateAt 0]
      (mtFiber74StateAt 4) (mtFiber74StateAt 12) (by decide) h1 (by decide)
      mtFiber74ReverseSingleStep12
  change mtFiber74StateAt 12 ∈ closeChainFiber mtWord mtFiber74DirectStates (2 + 14) [mtFiber74StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber74DirectStates 2 14 [mtFiber74StateAt 0] (mtFiber74StateAt 12) h2

theorem mtFiber74State13_in_close :
    mtFiber74StateAt 13 ∈ closeChainFiber mtWord mtFiber74DirectStates mtFiber74DirectStates.length [mtFiber74StateAt 0] := by
  have h0 : mtFiber74StateAt 0 ∈ closeChainFiber mtWord mtFiber74DirectStates 0 [mtFiber74StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber74StateAt 1 ∈ closeChainFiber mtWord mtFiber74DirectStates 1 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 0 [mtFiber74StateAt 0]
      (mtFiber74StateAt 0) (mtFiber74StateAt 1) (by decide) h0 (by decide)
      mtFiber74ReverseSingleStep1
  have h2 : mtFiber74StateAt 5 ∈ closeChainFiber mtWord mtFiber74DirectStates 2 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 1 [mtFiber74StateAt 0]
      (mtFiber74StateAt 1) (mtFiber74StateAt 5) (by decide) h1 (by decide)
      mtFiber74ReverseSingleStep5
  have h3 : mtFiber74StateAt 13 ∈ closeChainFiber mtWord mtFiber74DirectStates 3 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 2 [mtFiber74StateAt 0]
      (mtFiber74StateAt 5) (mtFiber74StateAt 13) (by decide) h2 (by decide)
      mtFiber74ReverseSingleStep13
  change mtFiber74StateAt 13 ∈ closeChainFiber mtWord mtFiber74DirectStates (3 + 13) [mtFiber74StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber74DirectStates 3 13 [mtFiber74StateAt 0] (mtFiber74StateAt 13) h3

theorem mtFiber74State14_in_close :
    mtFiber74StateAt 14 ∈ closeChainFiber mtWord mtFiber74DirectStates mtFiber74DirectStates.length [mtFiber74StateAt 0] := by
  have h0 : mtFiber74StateAt 0 ∈ closeChainFiber mtWord mtFiber74DirectStates 0 [mtFiber74StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber74StateAt 2 ∈ closeChainFiber mtWord mtFiber74DirectStates 1 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 0 [mtFiber74StateAt 0]
      (mtFiber74StateAt 0) (mtFiber74StateAt 2) (by decide) h0 (by decide)
      mtFiber74ReverseSingleStep2
  have h2 : mtFiber74StateAt 6 ∈ closeChainFiber mtWord mtFiber74DirectStates 2 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 1 [mtFiber74StateAt 0]
      (mtFiber74StateAt 2) (mtFiber74StateAt 6) (by decide) h1 (by decide)
      mtFiber74ReverseSingleStep6
  have h3 : mtFiber74StateAt 14 ∈ closeChainFiber mtWord mtFiber74DirectStates 3 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 2 [mtFiber74StateAt 0]
      (mtFiber74StateAt 6) (mtFiber74StateAt 14) (by decide) h2 (by decide)
      mtFiber74ReverseSingleStep14
  change mtFiber74StateAt 14 ∈ closeChainFiber mtWord mtFiber74DirectStates (3 + 13) [mtFiber74StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber74DirectStates 3 13 [mtFiber74StateAt 0] (mtFiber74StateAt 14) h3

theorem mtFiber74State15_in_close :
    mtFiber74StateAt 15 ∈ closeChainFiber mtWord mtFiber74DirectStates mtFiber74DirectStates.length [mtFiber74StateAt 0] := by
  have h0 : mtFiber74StateAt 0 ∈ closeChainFiber mtWord mtFiber74DirectStates 0 [mtFiber74StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber74StateAt 1 ∈ closeChainFiber mtWord mtFiber74DirectStates 1 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 0 [mtFiber74StateAt 0]
      (mtFiber74StateAt 0) (mtFiber74StateAt 1) (by decide) h0 (by decide)
      mtFiber74ReverseSingleStep1
  have h2 : mtFiber74StateAt 3 ∈ closeChainFiber mtWord mtFiber74DirectStates 2 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 1 [mtFiber74StateAt 0]
      (mtFiber74StateAt 1) (mtFiber74StateAt 3) (by decide) h1 (by decide)
      mtFiber74ReverseSingleStep3
  have h3 : mtFiber74StateAt 7 ∈ closeChainFiber mtWord mtFiber74DirectStates 3 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 2 [mtFiber74StateAt 0]
      (mtFiber74StateAt 3) (mtFiber74StateAt 7) (by decide) h2 (by decide)
      mtFiber74ReverseSingleStep7
  have h4 : mtFiber74StateAt 15 ∈ closeChainFiber mtWord mtFiber74DirectStates 4 [mtFiber74StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber74DirectStates 3 [mtFiber74StateAt 0]
      (mtFiber74StateAt 7) (mtFiber74StateAt 15) (by decide) h3 (by decide)
      mtFiber74ReverseSingleStep15
  change mtFiber74StateAt 15 ∈ closeChainFiber mtWord mtFiber74DirectStates (4 + 12) [mtFiber74StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber74DirectStates 4 12 [mtFiber74StateAt 0] (mtFiber74StateAt 15) h4

theorem mtFiber74DirectConnected :
    chainFiberConnected mtWord mtFiber74DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber74DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber74State0_in_close
  · subst state
    exact mtFiber74State1_in_close
  · subst state
    exact mtFiber74State2_in_close
  · subst state
    exact mtFiber74State3_in_close
  · subst state
    exact mtFiber74State4_in_close
  · subst state
    exact mtFiber74State5_in_close
  · subst state
    exact mtFiber74State6_in_close
  · subst state
    exact mtFiber74State7_in_close
  · subst state
    exact mtFiber74State8_in_close
  · subst state
    exact mtFiber74State9_in_close
  · subst state
    exact mtFiber74State10_in_close
  · subst state
    exact mtFiber74State11_in_close
  · subst state
    exact mtFiber74State12_in_close
  · subst state
    exact mtFiber74State13_in_close
  · subst state
    exact mtFiber74State14_in_close
  · subst state
    exact mtFiber74State15_in_close
  · cases h
def mtFiber77StateAt (i : Nat) : List TauState :=
  directStates (mtFiber77RowAt i).sourceLeft (mtFiber77RowAt i).sourceRight

def mtFiber77DirectStates : List (List TauState) :=
  [mtFiber77StateAt 0, mtFiber77StateAt 1, mtFiber77StateAt 2, mtFiber77StateAt 3, mtFiber77StateAt 4, mtFiber77StateAt 5, mtFiber77StateAt 6, mtFiber77StateAt 7, mtFiber77StateAt 8, mtFiber77StateAt 9, mtFiber77StateAt 10, mtFiber77StateAt 11, mtFiber77StateAt 12, mtFiber77StateAt 13, mtFiber77StateAt 14, mtFiber77StateAt 15]

theorem mtFiber77ReverseRow_1_ok :
    mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber77Chunk0_ok
  change (mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 0) &&
    mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber77ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber77StateAt 0) (mtFiber77StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber77StateAt 0) (mtFiber77StateAt 1)
    (mtFiber77RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber77Key mtFiber77Expected
        (mtFiber77RowAt 1) (by decide) mtFiber77ReverseRow_1_ok
      simpa [mtFiber77StateAt, mtFiber77RowAt, mtFiber77Rows, listGetD, directRow] using h)

theorem mtFiber77ReverseRow_2_ok :
    mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber77Chunk1_ok
  change (mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 2) &&
    mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber77ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber77StateAt 1) (mtFiber77StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber77StateAt 1) (mtFiber77StateAt 2)
    (mtFiber77RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber77Key mtFiber77Expected
        (mtFiber77RowAt 2) (by decide) mtFiber77ReverseRow_2_ok
      simpa [mtFiber77StateAt, mtFiber77RowAt, mtFiber77Rows, listGetD, directRow] using h)

theorem mtFiber77ReverseRow_3_ok :
    mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber77Chunk1_ok
  change (mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 2) &&
    mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber77ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber77StateAt 0) (mtFiber77StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber77StateAt 0) (mtFiber77StateAt 3)
    (mtFiber77RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber77Key mtFiber77Expected
        (mtFiber77RowAt 3) (by decide) mtFiber77ReverseRow_3_ok
      simpa [mtFiber77StateAt, mtFiber77RowAt, mtFiber77Rows, listGetD, directRow] using h)

theorem mtFiber77ReverseRow_4_ok :
    mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber77Chunk2_ok
  change (mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 4) &&
    mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber77ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber77StateAt 0) (mtFiber77StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber77StateAt 0) (mtFiber77StateAt 4)
    (mtFiber77RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber77Key mtFiber77Expected
        (mtFiber77RowAt 4) (by decide) mtFiber77ReverseRow_4_ok
      simpa [mtFiber77StateAt, mtFiber77RowAt, mtFiber77Rows, listGetD, directRow] using h)

theorem mtFiber77ReverseRow_5_ok :
    mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber77Chunk2_ok
  change (mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 4) &&
    mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber77ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber77StateAt 1) (mtFiber77StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber77StateAt 1) (mtFiber77StateAt 5)
    (mtFiber77RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber77Key mtFiber77Expected
        (mtFiber77RowAt 5) (by decide) mtFiber77ReverseRow_5_ok
      simpa [mtFiber77StateAt, mtFiber77RowAt, mtFiber77Rows, listGetD, directRow] using h)

theorem mtFiber77ReverseRow_6_ok :
    mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber77Chunk3_ok
  change (mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 6) &&
    mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber77ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber77StateAt 2) (mtFiber77StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber77StateAt 2) (mtFiber77StateAt 6)
    (mtFiber77RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber77Key mtFiber77Expected
        (mtFiber77RowAt 6) (by decide) mtFiber77ReverseRow_6_ok
      simpa [mtFiber77StateAt, mtFiber77RowAt, mtFiber77Rows, listGetD, directRow] using h)

theorem mtFiber77ReverseRow_7_ok :
    mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber77Chunk3_ok
  change (mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 6) &&
    mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber77ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber77StateAt 3) (mtFiber77StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber77StateAt 3) (mtFiber77StateAt 7)
    (mtFiber77RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber77Key mtFiber77Expected
        (mtFiber77RowAt 7) (by decide) mtFiber77ReverseRow_7_ok
      simpa [mtFiber77StateAt, mtFiber77RowAt, mtFiber77Rows, listGetD, directRow] using h)

theorem mtFiber77ReverseRow_8_ok :
    mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber77Chunk4_ok
  change (mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 8) &&
    mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber77ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber77StateAt 0) (mtFiber77StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber77StateAt 0) (mtFiber77StateAt 8)
    (mtFiber77RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber77Key mtFiber77Expected
        (mtFiber77RowAt 8) (by decide) mtFiber77ReverseRow_8_ok
      simpa [mtFiber77StateAt, mtFiber77RowAt, mtFiber77Rows, listGetD, directRow] using h)

theorem mtFiber77ReverseRow_9_ok :
    mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber77Chunk4_ok
  change (mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 8) &&
    mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber77ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber77StateAt 1) (mtFiber77StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber77StateAt 1) (mtFiber77StateAt 9)
    (mtFiber77RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber77Key mtFiber77Expected
        (mtFiber77RowAt 9) (by decide) mtFiber77ReverseRow_9_ok
      simpa [mtFiber77StateAt, mtFiber77RowAt, mtFiber77Rows, listGetD, directRow] using h)

theorem mtFiber77ReverseRow_10_ok :
    mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber77Chunk5_ok
  change (mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 10) &&
    mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber77ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber77StateAt 2) (mtFiber77StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber77StateAt 2) (mtFiber77StateAt 10)
    (mtFiber77RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber77Key mtFiber77Expected
        (mtFiber77RowAt 10) (by decide) mtFiber77ReverseRow_10_ok
      simpa [mtFiber77StateAt, mtFiber77RowAt, mtFiber77Rows, listGetD, directRow] using h)

theorem mtFiber77ReverseRow_11_ok :
    mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber77Chunk5_ok
  change (mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 10) &&
    mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber77ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber77StateAt 3) (mtFiber77StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber77StateAt 3) (mtFiber77StateAt 11)
    (mtFiber77RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber77Key mtFiber77Expected
        (mtFiber77RowAt 11) (by decide) mtFiber77ReverseRow_11_ok
      simpa [mtFiber77StateAt, mtFiber77RowAt, mtFiber77Rows, listGetD, directRow] using h)

theorem mtFiber77ReverseRow_12_ok :
    mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber77Chunk6_ok
  change (mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 12) &&
    mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber77ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber77StateAt 4) (mtFiber77StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber77StateAt 4) (mtFiber77StateAt 12)
    (mtFiber77RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber77Key mtFiber77Expected
        (mtFiber77RowAt 12) (by decide) mtFiber77ReverseRow_12_ok
      simpa [mtFiber77StateAt, mtFiber77RowAt, mtFiber77Rows, listGetD, directRow] using h)

theorem mtFiber77ReverseRow_13_ok :
    mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber77Chunk6_ok
  change (mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 12) &&
    mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber77ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber77StateAt 5) (mtFiber77StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber77StateAt 5) (mtFiber77StateAt 13)
    (mtFiber77RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber77Key mtFiber77Expected
        (mtFiber77RowAt 13) (by decide) mtFiber77ReverseRow_13_ok
      simpa [mtFiber77StateAt, mtFiber77RowAt, mtFiber77Rows, listGetD, directRow] using h)

theorem mtFiber77ReverseRow_14_ok :
    mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber77Chunk7_ok
  change (mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 14) &&
    mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber77ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber77StateAt 6) (mtFiber77StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber77StateAt 6) (mtFiber77StateAt 14)
    (mtFiber77RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber77Key mtFiber77Expected
        (mtFiber77RowAt 14) (by decide) mtFiber77ReverseRow_14_ok
      simpa [mtFiber77StateAt, mtFiber77RowAt, mtFiber77Rows, listGetD, directRow] using h)

theorem mtFiber77ReverseRow_15_ok :
    mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber77Chunk7_ok
  change (mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 14) &&
    mtRowReverseValid mtFiber77Key mtFiber77Expected (mtFiber77RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber77ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber77StateAt 7) (mtFiber77StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber77StateAt 7) (mtFiber77StateAt 15)
    (mtFiber77RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber77Key mtFiber77Expected
        (mtFiber77RowAt 15) (by decide) mtFiber77ReverseRow_15_ok
      simpa [mtFiber77StateAt, mtFiber77RowAt, mtFiber77Rows, listGetD, directRow] using h)

theorem mtFiber77State0_in_close :
    mtFiber77StateAt 0 ∈ closeChainFiber mtWord mtFiber77DirectStates mtFiber77DirectStates.length [mtFiber77StateAt 0] := by
  change mtFiber77StateAt 0 ∈ closeChainFiber mtWord mtFiber77DirectStates 16 [mtFiber77StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber77DirectStates 0 16 [mtFiber77StateAt 0] (mtFiber77StateAt 0) (by simp [closeChainFiber])

theorem mtFiber77State1_in_close :
    mtFiber77StateAt 1 ∈ closeChainFiber mtWord mtFiber77DirectStates mtFiber77DirectStates.length [mtFiber77StateAt 0] := by
  have h0 : mtFiber77StateAt 0 ∈ closeChainFiber mtWord mtFiber77DirectStates 0 [mtFiber77StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber77StateAt 1 ∈ closeChainFiber mtWord mtFiber77DirectStates 1 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 0 [mtFiber77StateAt 0]
      (mtFiber77StateAt 0) (mtFiber77StateAt 1) (by decide) h0 (by decide)
      mtFiber77ReverseSingleStep1
  change mtFiber77StateAt 1 ∈ closeChainFiber mtWord mtFiber77DirectStates (1 + 15) [mtFiber77StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber77DirectStates 1 15 [mtFiber77StateAt 0] (mtFiber77StateAt 1) h1

theorem mtFiber77State2_in_close :
    mtFiber77StateAt 2 ∈ closeChainFiber mtWord mtFiber77DirectStates mtFiber77DirectStates.length [mtFiber77StateAt 0] := by
  have h0 : mtFiber77StateAt 0 ∈ closeChainFiber mtWord mtFiber77DirectStates 0 [mtFiber77StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber77StateAt 1 ∈ closeChainFiber mtWord mtFiber77DirectStates 1 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 0 [mtFiber77StateAt 0]
      (mtFiber77StateAt 0) (mtFiber77StateAt 1) (by decide) h0 (by decide)
      mtFiber77ReverseSingleStep1
  have h2 : mtFiber77StateAt 2 ∈ closeChainFiber mtWord mtFiber77DirectStates 2 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 1 [mtFiber77StateAt 0]
      (mtFiber77StateAt 1) (mtFiber77StateAt 2) (by decide) h1 (by decide)
      mtFiber77ReverseSingleStep2
  change mtFiber77StateAt 2 ∈ closeChainFiber mtWord mtFiber77DirectStates (2 + 14) [mtFiber77StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber77DirectStates 2 14 [mtFiber77StateAt 0] (mtFiber77StateAt 2) h2

theorem mtFiber77State3_in_close :
    mtFiber77StateAt 3 ∈ closeChainFiber mtWord mtFiber77DirectStates mtFiber77DirectStates.length [mtFiber77StateAt 0] := by
  have h0 : mtFiber77StateAt 0 ∈ closeChainFiber mtWord mtFiber77DirectStates 0 [mtFiber77StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber77StateAt 3 ∈ closeChainFiber mtWord mtFiber77DirectStates 1 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 0 [mtFiber77StateAt 0]
      (mtFiber77StateAt 0) (mtFiber77StateAt 3) (by decide) h0 (by decide)
      mtFiber77ReverseSingleStep3
  change mtFiber77StateAt 3 ∈ closeChainFiber mtWord mtFiber77DirectStates (1 + 15) [mtFiber77StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber77DirectStates 1 15 [mtFiber77StateAt 0] (mtFiber77StateAt 3) h1

theorem mtFiber77State4_in_close :
    mtFiber77StateAt 4 ∈ closeChainFiber mtWord mtFiber77DirectStates mtFiber77DirectStates.length [mtFiber77StateAt 0] := by
  have h0 : mtFiber77StateAt 0 ∈ closeChainFiber mtWord mtFiber77DirectStates 0 [mtFiber77StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber77StateAt 4 ∈ closeChainFiber mtWord mtFiber77DirectStates 1 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 0 [mtFiber77StateAt 0]
      (mtFiber77StateAt 0) (mtFiber77StateAt 4) (by decide) h0 (by decide)
      mtFiber77ReverseSingleStep4
  change mtFiber77StateAt 4 ∈ closeChainFiber mtWord mtFiber77DirectStates (1 + 15) [mtFiber77StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber77DirectStates 1 15 [mtFiber77StateAt 0] (mtFiber77StateAt 4) h1

theorem mtFiber77State5_in_close :
    mtFiber77StateAt 5 ∈ closeChainFiber mtWord mtFiber77DirectStates mtFiber77DirectStates.length [mtFiber77StateAt 0] := by
  have h0 : mtFiber77StateAt 0 ∈ closeChainFiber mtWord mtFiber77DirectStates 0 [mtFiber77StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber77StateAt 1 ∈ closeChainFiber mtWord mtFiber77DirectStates 1 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 0 [mtFiber77StateAt 0]
      (mtFiber77StateAt 0) (mtFiber77StateAt 1) (by decide) h0 (by decide)
      mtFiber77ReverseSingleStep1
  have h2 : mtFiber77StateAt 5 ∈ closeChainFiber mtWord mtFiber77DirectStates 2 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 1 [mtFiber77StateAt 0]
      (mtFiber77StateAt 1) (mtFiber77StateAt 5) (by decide) h1 (by decide)
      mtFiber77ReverseSingleStep5
  change mtFiber77StateAt 5 ∈ closeChainFiber mtWord mtFiber77DirectStates (2 + 14) [mtFiber77StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber77DirectStates 2 14 [mtFiber77StateAt 0] (mtFiber77StateAt 5) h2

theorem mtFiber77State6_in_close :
    mtFiber77StateAt 6 ∈ closeChainFiber mtWord mtFiber77DirectStates mtFiber77DirectStates.length [mtFiber77StateAt 0] := by
  have h0 : mtFiber77StateAt 0 ∈ closeChainFiber mtWord mtFiber77DirectStates 0 [mtFiber77StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber77StateAt 1 ∈ closeChainFiber mtWord mtFiber77DirectStates 1 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 0 [mtFiber77StateAt 0]
      (mtFiber77StateAt 0) (mtFiber77StateAt 1) (by decide) h0 (by decide)
      mtFiber77ReverseSingleStep1
  have h2 : mtFiber77StateAt 2 ∈ closeChainFiber mtWord mtFiber77DirectStates 2 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 1 [mtFiber77StateAt 0]
      (mtFiber77StateAt 1) (mtFiber77StateAt 2) (by decide) h1 (by decide)
      mtFiber77ReverseSingleStep2
  have h3 : mtFiber77StateAt 6 ∈ closeChainFiber mtWord mtFiber77DirectStates 3 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 2 [mtFiber77StateAt 0]
      (mtFiber77StateAt 2) (mtFiber77StateAt 6) (by decide) h2 (by decide)
      mtFiber77ReverseSingleStep6
  change mtFiber77StateAt 6 ∈ closeChainFiber mtWord mtFiber77DirectStates (3 + 13) [mtFiber77StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber77DirectStates 3 13 [mtFiber77StateAt 0] (mtFiber77StateAt 6) h3

theorem mtFiber77State7_in_close :
    mtFiber77StateAt 7 ∈ closeChainFiber mtWord mtFiber77DirectStates mtFiber77DirectStates.length [mtFiber77StateAt 0] := by
  have h0 : mtFiber77StateAt 0 ∈ closeChainFiber mtWord mtFiber77DirectStates 0 [mtFiber77StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber77StateAt 3 ∈ closeChainFiber mtWord mtFiber77DirectStates 1 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 0 [mtFiber77StateAt 0]
      (mtFiber77StateAt 0) (mtFiber77StateAt 3) (by decide) h0 (by decide)
      mtFiber77ReverseSingleStep3
  have h2 : mtFiber77StateAt 7 ∈ closeChainFiber mtWord mtFiber77DirectStates 2 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 1 [mtFiber77StateAt 0]
      (mtFiber77StateAt 3) (mtFiber77StateAt 7) (by decide) h1 (by decide)
      mtFiber77ReverseSingleStep7
  change mtFiber77StateAt 7 ∈ closeChainFiber mtWord mtFiber77DirectStates (2 + 14) [mtFiber77StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber77DirectStates 2 14 [mtFiber77StateAt 0] (mtFiber77StateAt 7) h2

theorem mtFiber77State8_in_close :
    mtFiber77StateAt 8 ∈ closeChainFiber mtWord mtFiber77DirectStates mtFiber77DirectStates.length [mtFiber77StateAt 0] := by
  have h0 : mtFiber77StateAt 0 ∈ closeChainFiber mtWord mtFiber77DirectStates 0 [mtFiber77StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber77StateAt 8 ∈ closeChainFiber mtWord mtFiber77DirectStates 1 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 0 [mtFiber77StateAt 0]
      (mtFiber77StateAt 0) (mtFiber77StateAt 8) (by decide) h0 (by decide)
      mtFiber77ReverseSingleStep8
  change mtFiber77StateAt 8 ∈ closeChainFiber mtWord mtFiber77DirectStates (1 + 15) [mtFiber77StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber77DirectStates 1 15 [mtFiber77StateAt 0] (mtFiber77StateAt 8) h1

theorem mtFiber77State9_in_close :
    mtFiber77StateAt 9 ∈ closeChainFiber mtWord mtFiber77DirectStates mtFiber77DirectStates.length [mtFiber77StateAt 0] := by
  have h0 : mtFiber77StateAt 0 ∈ closeChainFiber mtWord mtFiber77DirectStates 0 [mtFiber77StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber77StateAt 1 ∈ closeChainFiber mtWord mtFiber77DirectStates 1 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 0 [mtFiber77StateAt 0]
      (mtFiber77StateAt 0) (mtFiber77StateAt 1) (by decide) h0 (by decide)
      mtFiber77ReverseSingleStep1
  have h2 : mtFiber77StateAt 9 ∈ closeChainFiber mtWord mtFiber77DirectStates 2 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 1 [mtFiber77StateAt 0]
      (mtFiber77StateAt 1) (mtFiber77StateAt 9) (by decide) h1 (by decide)
      mtFiber77ReverseSingleStep9
  change mtFiber77StateAt 9 ∈ closeChainFiber mtWord mtFiber77DirectStates (2 + 14) [mtFiber77StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber77DirectStates 2 14 [mtFiber77StateAt 0] (mtFiber77StateAt 9) h2

theorem mtFiber77State10_in_close :
    mtFiber77StateAt 10 ∈ closeChainFiber mtWord mtFiber77DirectStates mtFiber77DirectStates.length [mtFiber77StateAt 0] := by
  have h0 : mtFiber77StateAt 0 ∈ closeChainFiber mtWord mtFiber77DirectStates 0 [mtFiber77StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber77StateAt 1 ∈ closeChainFiber mtWord mtFiber77DirectStates 1 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 0 [mtFiber77StateAt 0]
      (mtFiber77StateAt 0) (mtFiber77StateAt 1) (by decide) h0 (by decide)
      mtFiber77ReverseSingleStep1
  have h2 : mtFiber77StateAt 2 ∈ closeChainFiber mtWord mtFiber77DirectStates 2 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 1 [mtFiber77StateAt 0]
      (mtFiber77StateAt 1) (mtFiber77StateAt 2) (by decide) h1 (by decide)
      mtFiber77ReverseSingleStep2
  have h3 : mtFiber77StateAt 10 ∈ closeChainFiber mtWord mtFiber77DirectStates 3 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 2 [mtFiber77StateAt 0]
      (mtFiber77StateAt 2) (mtFiber77StateAt 10) (by decide) h2 (by decide)
      mtFiber77ReverseSingleStep10
  change mtFiber77StateAt 10 ∈ closeChainFiber mtWord mtFiber77DirectStates (3 + 13) [mtFiber77StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber77DirectStates 3 13 [mtFiber77StateAt 0] (mtFiber77StateAt 10) h3

theorem mtFiber77State11_in_close :
    mtFiber77StateAt 11 ∈ closeChainFiber mtWord mtFiber77DirectStates mtFiber77DirectStates.length [mtFiber77StateAt 0] := by
  have h0 : mtFiber77StateAt 0 ∈ closeChainFiber mtWord mtFiber77DirectStates 0 [mtFiber77StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber77StateAt 3 ∈ closeChainFiber mtWord mtFiber77DirectStates 1 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 0 [mtFiber77StateAt 0]
      (mtFiber77StateAt 0) (mtFiber77StateAt 3) (by decide) h0 (by decide)
      mtFiber77ReverseSingleStep3
  have h2 : mtFiber77StateAt 11 ∈ closeChainFiber mtWord mtFiber77DirectStates 2 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 1 [mtFiber77StateAt 0]
      (mtFiber77StateAt 3) (mtFiber77StateAt 11) (by decide) h1 (by decide)
      mtFiber77ReverseSingleStep11
  change mtFiber77StateAt 11 ∈ closeChainFiber mtWord mtFiber77DirectStates (2 + 14) [mtFiber77StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber77DirectStates 2 14 [mtFiber77StateAt 0] (mtFiber77StateAt 11) h2

theorem mtFiber77State12_in_close :
    mtFiber77StateAt 12 ∈ closeChainFiber mtWord mtFiber77DirectStates mtFiber77DirectStates.length [mtFiber77StateAt 0] := by
  have h0 : mtFiber77StateAt 0 ∈ closeChainFiber mtWord mtFiber77DirectStates 0 [mtFiber77StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber77StateAt 4 ∈ closeChainFiber mtWord mtFiber77DirectStates 1 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 0 [mtFiber77StateAt 0]
      (mtFiber77StateAt 0) (mtFiber77StateAt 4) (by decide) h0 (by decide)
      mtFiber77ReverseSingleStep4
  have h2 : mtFiber77StateAt 12 ∈ closeChainFiber mtWord mtFiber77DirectStates 2 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 1 [mtFiber77StateAt 0]
      (mtFiber77StateAt 4) (mtFiber77StateAt 12) (by decide) h1 (by decide)
      mtFiber77ReverseSingleStep12
  change mtFiber77StateAt 12 ∈ closeChainFiber mtWord mtFiber77DirectStates (2 + 14) [mtFiber77StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber77DirectStates 2 14 [mtFiber77StateAt 0] (mtFiber77StateAt 12) h2

theorem mtFiber77State13_in_close :
    mtFiber77StateAt 13 ∈ closeChainFiber mtWord mtFiber77DirectStates mtFiber77DirectStates.length [mtFiber77StateAt 0] := by
  have h0 : mtFiber77StateAt 0 ∈ closeChainFiber mtWord mtFiber77DirectStates 0 [mtFiber77StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber77StateAt 1 ∈ closeChainFiber mtWord mtFiber77DirectStates 1 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 0 [mtFiber77StateAt 0]
      (mtFiber77StateAt 0) (mtFiber77StateAt 1) (by decide) h0 (by decide)
      mtFiber77ReverseSingleStep1
  have h2 : mtFiber77StateAt 5 ∈ closeChainFiber mtWord mtFiber77DirectStates 2 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 1 [mtFiber77StateAt 0]
      (mtFiber77StateAt 1) (mtFiber77StateAt 5) (by decide) h1 (by decide)
      mtFiber77ReverseSingleStep5
  have h3 : mtFiber77StateAt 13 ∈ closeChainFiber mtWord mtFiber77DirectStates 3 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 2 [mtFiber77StateAt 0]
      (mtFiber77StateAt 5) (mtFiber77StateAt 13) (by decide) h2 (by decide)
      mtFiber77ReverseSingleStep13
  change mtFiber77StateAt 13 ∈ closeChainFiber mtWord mtFiber77DirectStates (3 + 13) [mtFiber77StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber77DirectStates 3 13 [mtFiber77StateAt 0] (mtFiber77StateAt 13) h3

theorem mtFiber77State14_in_close :
    mtFiber77StateAt 14 ∈ closeChainFiber mtWord mtFiber77DirectStates mtFiber77DirectStates.length [mtFiber77StateAt 0] := by
  have h0 : mtFiber77StateAt 0 ∈ closeChainFiber mtWord mtFiber77DirectStates 0 [mtFiber77StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber77StateAt 1 ∈ closeChainFiber mtWord mtFiber77DirectStates 1 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 0 [mtFiber77StateAt 0]
      (mtFiber77StateAt 0) (mtFiber77StateAt 1) (by decide) h0 (by decide)
      mtFiber77ReverseSingleStep1
  have h2 : mtFiber77StateAt 2 ∈ closeChainFiber mtWord mtFiber77DirectStates 2 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 1 [mtFiber77StateAt 0]
      (mtFiber77StateAt 1) (mtFiber77StateAt 2) (by decide) h1 (by decide)
      mtFiber77ReverseSingleStep2
  have h3 : mtFiber77StateAt 6 ∈ closeChainFiber mtWord mtFiber77DirectStates 3 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 2 [mtFiber77StateAt 0]
      (mtFiber77StateAt 2) (mtFiber77StateAt 6) (by decide) h2 (by decide)
      mtFiber77ReverseSingleStep6
  have h4 : mtFiber77StateAt 14 ∈ closeChainFiber mtWord mtFiber77DirectStates 4 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 3 [mtFiber77StateAt 0]
      (mtFiber77StateAt 6) (mtFiber77StateAt 14) (by decide) h3 (by decide)
      mtFiber77ReverseSingleStep14
  change mtFiber77StateAt 14 ∈ closeChainFiber mtWord mtFiber77DirectStates (4 + 12) [mtFiber77StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber77DirectStates 4 12 [mtFiber77StateAt 0] (mtFiber77StateAt 14) h4

theorem mtFiber77State15_in_close :
    mtFiber77StateAt 15 ∈ closeChainFiber mtWord mtFiber77DirectStates mtFiber77DirectStates.length [mtFiber77StateAt 0] := by
  have h0 : mtFiber77StateAt 0 ∈ closeChainFiber mtWord mtFiber77DirectStates 0 [mtFiber77StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber77StateAt 3 ∈ closeChainFiber mtWord mtFiber77DirectStates 1 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 0 [mtFiber77StateAt 0]
      (mtFiber77StateAt 0) (mtFiber77StateAt 3) (by decide) h0 (by decide)
      mtFiber77ReverseSingleStep3
  have h2 : mtFiber77StateAt 7 ∈ closeChainFiber mtWord mtFiber77DirectStates 2 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 1 [mtFiber77StateAt 0]
      (mtFiber77StateAt 3) (mtFiber77StateAt 7) (by decide) h1 (by decide)
      mtFiber77ReverseSingleStep7
  have h3 : mtFiber77StateAt 15 ∈ closeChainFiber mtWord mtFiber77DirectStates 3 [mtFiber77StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber77DirectStates 2 [mtFiber77StateAt 0]
      (mtFiber77StateAt 7) (mtFiber77StateAt 15) (by decide) h2 (by decide)
      mtFiber77ReverseSingleStep15
  change mtFiber77StateAt 15 ∈ closeChainFiber mtWord mtFiber77DirectStates (3 + 13) [mtFiber77StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber77DirectStates 3 13 [mtFiber77StateAt 0] (mtFiber77StateAt 15) h3

theorem mtFiber77DirectConnected :
    chainFiberConnected mtWord mtFiber77DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber77DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber77State0_in_close
  · subst state
    exact mtFiber77State1_in_close
  · subst state
    exact mtFiber77State2_in_close
  · subst state
    exact mtFiber77State3_in_close
  · subst state
    exact mtFiber77State4_in_close
  · subst state
    exact mtFiber77State5_in_close
  · subst state
    exact mtFiber77State6_in_close
  · subst state
    exact mtFiber77State7_in_close
  · subst state
    exact mtFiber77State8_in_close
  · subst state
    exact mtFiber77State9_in_close
  · subst state
    exact mtFiber77State10_in_close
  · subst state
    exact mtFiber77State11_in_close
  · subst state
    exact mtFiber77State12_in_close
  · subst state
    exact mtFiber77State13_in_close
  · subst state
    exact mtFiber77State14_in_close
  · subst state
    exact mtFiber77State15_in_close
  · cases h
end GoertzelLemma818LengthTwoMTBridge

end Mettapedia.GraphTheory.FourColor
