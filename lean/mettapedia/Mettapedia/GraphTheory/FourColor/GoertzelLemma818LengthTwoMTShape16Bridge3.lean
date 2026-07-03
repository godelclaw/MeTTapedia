import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for size-16 `mirror,normal` length-two fibers, group 3

This module proves direct connectedness for generated `mirror,normal` size-16 fibers from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMTBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorTauCertificate
open GoertzelLemma818MirrorTauReverseAudit

def mtFiber43StateAt (i : Nat) : List TauState :=
  directStates (mtFiber43RowAt i).sourceLeft (mtFiber43RowAt i).sourceRight

def mtFiber43DirectStates : List (List TauState) :=
  [mtFiber43StateAt 0, mtFiber43StateAt 1, mtFiber43StateAt 2, mtFiber43StateAt 3, mtFiber43StateAt 4, mtFiber43StateAt 5, mtFiber43StateAt 6, mtFiber43StateAt 7, mtFiber43StateAt 8, mtFiber43StateAt 9, mtFiber43StateAt 10, mtFiber43StateAt 11, mtFiber43StateAt 12, mtFiber43StateAt 13, mtFiber43StateAt 14, mtFiber43StateAt 15]

theorem mtFiber43ReverseRow_1_ok :
    mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber43Chunk0_ok
  change (mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 0) &&
    mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber43ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber43StateAt 0) (mtFiber43StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber43StateAt 0) (mtFiber43StateAt 1)
    (mtFiber43RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber43Key mtFiber43Expected
        (mtFiber43RowAt 1) (by decide) mtFiber43ReverseRow_1_ok
      simpa [mtFiber43StateAt, mtFiber43RowAt, mtFiber43Rows, listGetD, directRow] using h)

theorem mtFiber43ReverseRow_2_ok :
    mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber43Chunk1_ok
  change (mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 2) &&
    mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber43ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber43StateAt 0) (mtFiber43StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber43StateAt 0) (mtFiber43StateAt 2)
    (mtFiber43RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber43Key mtFiber43Expected
        (mtFiber43RowAt 2) (by decide) mtFiber43ReverseRow_2_ok
      simpa [mtFiber43StateAt, mtFiber43RowAt, mtFiber43Rows, listGetD, directRow] using h)

theorem mtFiber43ReverseRow_3_ok :
    mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber43Chunk1_ok
  change (mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 2) &&
    mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber43ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber43StateAt 1) (mtFiber43StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber43StateAt 1) (mtFiber43StateAt 3)
    (mtFiber43RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber43Key mtFiber43Expected
        (mtFiber43RowAt 3) (by decide) mtFiber43ReverseRow_3_ok
      simpa [mtFiber43StateAt, mtFiber43RowAt, mtFiber43Rows, listGetD, directRow] using h)

theorem mtFiber43ReverseRow_4_ok :
    mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber43Chunk2_ok
  change (mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 4) &&
    mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber43ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber43StateAt 0) (mtFiber43StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber43StateAt 0) (mtFiber43StateAt 4)
    (mtFiber43RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber43Key mtFiber43Expected
        (mtFiber43RowAt 4) (by decide) mtFiber43ReverseRow_4_ok
      simpa [mtFiber43StateAt, mtFiber43RowAt, mtFiber43Rows, listGetD, directRow] using h)

theorem mtFiber43ReverseRow_5_ok :
    mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber43Chunk2_ok
  change (mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 4) &&
    mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber43ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber43StateAt 1) (mtFiber43StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber43StateAt 1) (mtFiber43StateAt 5)
    (mtFiber43RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber43Key mtFiber43Expected
        (mtFiber43RowAt 5) (by decide) mtFiber43ReverseRow_5_ok
      simpa [mtFiber43StateAt, mtFiber43RowAt, mtFiber43Rows, listGetD, directRow] using h)

theorem mtFiber43ReverseRow_6_ok :
    mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber43Chunk3_ok
  change (mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 6) &&
    mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber43ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber43StateAt 2) (mtFiber43StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber43StateAt 2) (mtFiber43StateAt 6)
    (mtFiber43RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber43Key mtFiber43Expected
        (mtFiber43RowAt 6) (by decide) mtFiber43ReverseRow_6_ok
      simpa [mtFiber43StateAt, mtFiber43RowAt, mtFiber43Rows, listGetD, directRow] using h)

theorem mtFiber43ReverseRow_7_ok :
    mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber43Chunk3_ok
  change (mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 6) &&
    mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber43ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber43StateAt 3) (mtFiber43StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber43StateAt 3) (mtFiber43StateAt 7)
    (mtFiber43RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber43Key mtFiber43Expected
        (mtFiber43RowAt 7) (by decide) mtFiber43ReverseRow_7_ok
      simpa [mtFiber43StateAt, mtFiber43RowAt, mtFiber43Rows, listGetD, directRow] using h)

theorem mtFiber43ReverseRow_8_ok :
    mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber43Chunk4_ok
  change (mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 8) &&
    mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber43ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber43StateAt 4) (mtFiber43StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber43StateAt 4) (mtFiber43StateAt 8)
    (mtFiber43RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber43Key mtFiber43Expected
        (mtFiber43RowAt 8) (by decide) mtFiber43ReverseRow_8_ok
      simpa [mtFiber43StateAt, mtFiber43RowAt, mtFiber43Rows, listGetD, directRow] using h)

theorem mtFiber43ReverseRow_9_ok :
    mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber43Chunk4_ok
  change (mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 8) &&
    mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber43ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber43StateAt 5) (mtFiber43StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber43StateAt 5) (mtFiber43StateAt 9)
    (mtFiber43RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber43Key mtFiber43Expected
        (mtFiber43RowAt 9) (by decide) mtFiber43ReverseRow_9_ok
      simpa [mtFiber43StateAt, mtFiber43RowAt, mtFiber43Rows, listGetD, directRow] using h)

theorem mtFiber43ReverseRow_10_ok :
    mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber43Chunk5_ok
  change (mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 10) &&
    mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber43ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber43StateAt 6) (mtFiber43StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber43StateAt 6) (mtFiber43StateAt 10)
    (mtFiber43RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber43Key mtFiber43Expected
        (mtFiber43RowAt 10) (by decide) mtFiber43ReverseRow_10_ok
      simpa [mtFiber43StateAt, mtFiber43RowAt, mtFiber43Rows, listGetD, directRow] using h)

theorem mtFiber43ReverseRow_11_ok :
    mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber43Chunk5_ok
  change (mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 10) &&
    mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber43ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber43StateAt 7) (mtFiber43StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber43StateAt 7) (mtFiber43StateAt 11)
    (mtFiber43RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber43Key mtFiber43Expected
        (mtFiber43RowAt 11) (by decide) mtFiber43ReverseRow_11_ok
      simpa [mtFiber43StateAt, mtFiber43RowAt, mtFiber43Rows, listGetD, directRow] using h)

theorem mtFiber43ReverseRow_12_ok :
    mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber43Chunk6_ok
  change (mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 12) &&
    mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber43ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber43StateAt 0) (mtFiber43StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber43StateAt 0) (mtFiber43StateAt 12)
    (mtFiber43RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber43Key mtFiber43Expected
        (mtFiber43RowAt 12) (by decide) mtFiber43ReverseRow_12_ok
      simpa [mtFiber43StateAt, mtFiber43RowAt, mtFiber43Rows, listGetD, directRow] using h)

theorem mtFiber43ReverseRow_13_ok :
    mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber43Chunk6_ok
  change (mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 12) &&
    mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber43ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber43StateAt 1) (mtFiber43StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber43StateAt 1) (mtFiber43StateAt 13)
    (mtFiber43RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber43Key mtFiber43Expected
        (mtFiber43RowAt 13) (by decide) mtFiber43ReverseRow_13_ok
      simpa [mtFiber43StateAt, mtFiber43RowAt, mtFiber43Rows, listGetD, directRow] using h)

theorem mtFiber43ReverseRow_14_ok :
    mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber43Chunk7_ok
  change (mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 14) &&
    mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber43ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber43StateAt 2) (mtFiber43StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber43StateAt 2) (mtFiber43StateAt 14)
    (mtFiber43RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber43Key mtFiber43Expected
        (mtFiber43RowAt 14) (by decide) mtFiber43ReverseRow_14_ok
      simpa [mtFiber43StateAt, mtFiber43RowAt, mtFiber43Rows, listGetD, directRow] using h)

theorem mtFiber43ReverseRow_15_ok :
    mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber43Chunk7_ok
  change (mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 14) &&
    mtRowReverseValid mtFiber43Key mtFiber43Expected (mtFiber43RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber43ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber43StateAt 3) (mtFiber43StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber43StateAt 3) (mtFiber43StateAt 15)
    (mtFiber43RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber43Key mtFiber43Expected
        (mtFiber43RowAt 15) (by decide) mtFiber43ReverseRow_15_ok
      simpa [mtFiber43StateAt, mtFiber43RowAt, mtFiber43Rows, listGetD, directRow] using h)

theorem mtFiber43State0_in_close :
    mtFiber43StateAt 0 ∈ closeChainFiber mtWord mtFiber43DirectStates mtFiber43DirectStates.length [mtFiber43StateAt 0] := by
  change mtFiber43StateAt 0 ∈ closeChainFiber mtWord mtFiber43DirectStates 16 [mtFiber43StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber43DirectStates 0 16 [mtFiber43StateAt 0] (mtFiber43StateAt 0) (by simp [closeChainFiber])

theorem mtFiber43State1_in_close :
    mtFiber43StateAt 1 ∈ closeChainFiber mtWord mtFiber43DirectStates mtFiber43DirectStates.length [mtFiber43StateAt 0] := by
  have h0 : mtFiber43StateAt 0 ∈ closeChainFiber mtWord mtFiber43DirectStates 0 [mtFiber43StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber43StateAt 1 ∈ closeChainFiber mtWord mtFiber43DirectStates 1 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 0 [mtFiber43StateAt 0]
      (mtFiber43StateAt 0) (mtFiber43StateAt 1) (by decide) h0 (by decide)
      mtFiber43ReverseSingleStep1
  change mtFiber43StateAt 1 ∈ closeChainFiber mtWord mtFiber43DirectStates (1 + 15) [mtFiber43StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber43DirectStates 1 15 [mtFiber43StateAt 0] (mtFiber43StateAt 1) h1

theorem mtFiber43State2_in_close :
    mtFiber43StateAt 2 ∈ closeChainFiber mtWord mtFiber43DirectStates mtFiber43DirectStates.length [mtFiber43StateAt 0] := by
  have h0 : mtFiber43StateAt 0 ∈ closeChainFiber mtWord mtFiber43DirectStates 0 [mtFiber43StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber43StateAt 2 ∈ closeChainFiber mtWord mtFiber43DirectStates 1 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 0 [mtFiber43StateAt 0]
      (mtFiber43StateAt 0) (mtFiber43StateAt 2) (by decide) h0 (by decide)
      mtFiber43ReverseSingleStep2
  change mtFiber43StateAt 2 ∈ closeChainFiber mtWord mtFiber43DirectStates (1 + 15) [mtFiber43StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber43DirectStates 1 15 [mtFiber43StateAt 0] (mtFiber43StateAt 2) h1

theorem mtFiber43State3_in_close :
    mtFiber43StateAt 3 ∈ closeChainFiber mtWord mtFiber43DirectStates mtFiber43DirectStates.length [mtFiber43StateAt 0] := by
  have h0 : mtFiber43StateAt 0 ∈ closeChainFiber mtWord mtFiber43DirectStates 0 [mtFiber43StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber43StateAt 1 ∈ closeChainFiber mtWord mtFiber43DirectStates 1 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 0 [mtFiber43StateAt 0]
      (mtFiber43StateAt 0) (mtFiber43StateAt 1) (by decide) h0 (by decide)
      mtFiber43ReverseSingleStep1
  have h2 : mtFiber43StateAt 3 ∈ closeChainFiber mtWord mtFiber43DirectStates 2 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 1 [mtFiber43StateAt 0]
      (mtFiber43StateAt 1) (mtFiber43StateAt 3) (by decide) h1 (by decide)
      mtFiber43ReverseSingleStep3
  change mtFiber43StateAt 3 ∈ closeChainFiber mtWord mtFiber43DirectStates (2 + 14) [mtFiber43StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber43DirectStates 2 14 [mtFiber43StateAt 0] (mtFiber43StateAt 3) h2

theorem mtFiber43State4_in_close :
    mtFiber43StateAt 4 ∈ closeChainFiber mtWord mtFiber43DirectStates mtFiber43DirectStates.length [mtFiber43StateAt 0] := by
  have h0 : mtFiber43StateAt 0 ∈ closeChainFiber mtWord mtFiber43DirectStates 0 [mtFiber43StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber43StateAt 4 ∈ closeChainFiber mtWord mtFiber43DirectStates 1 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 0 [mtFiber43StateAt 0]
      (mtFiber43StateAt 0) (mtFiber43StateAt 4) (by decide) h0 (by decide)
      mtFiber43ReverseSingleStep4
  change mtFiber43StateAt 4 ∈ closeChainFiber mtWord mtFiber43DirectStates (1 + 15) [mtFiber43StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber43DirectStates 1 15 [mtFiber43StateAt 0] (mtFiber43StateAt 4) h1

theorem mtFiber43State5_in_close :
    mtFiber43StateAt 5 ∈ closeChainFiber mtWord mtFiber43DirectStates mtFiber43DirectStates.length [mtFiber43StateAt 0] := by
  have h0 : mtFiber43StateAt 0 ∈ closeChainFiber mtWord mtFiber43DirectStates 0 [mtFiber43StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber43StateAt 1 ∈ closeChainFiber mtWord mtFiber43DirectStates 1 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 0 [mtFiber43StateAt 0]
      (mtFiber43StateAt 0) (mtFiber43StateAt 1) (by decide) h0 (by decide)
      mtFiber43ReverseSingleStep1
  have h2 : mtFiber43StateAt 5 ∈ closeChainFiber mtWord mtFiber43DirectStates 2 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 1 [mtFiber43StateAt 0]
      (mtFiber43StateAt 1) (mtFiber43StateAt 5) (by decide) h1 (by decide)
      mtFiber43ReverseSingleStep5
  change mtFiber43StateAt 5 ∈ closeChainFiber mtWord mtFiber43DirectStates (2 + 14) [mtFiber43StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber43DirectStates 2 14 [mtFiber43StateAt 0] (mtFiber43StateAt 5) h2

theorem mtFiber43State6_in_close :
    mtFiber43StateAt 6 ∈ closeChainFiber mtWord mtFiber43DirectStates mtFiber43DirectStates.length [mtFiber43StateAt 0] := by
  have h0 : mtFiber43StateAt 0 ∈ closeChainFiber mtWord mtFiber43DirectStates 0 [mtFiber43StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber43StateAt 2 ∈ closeChainFiber mtWord mtFiber43DirectStates 1 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 0 [mtFiber43StateAt 0]
      (mtFiber43StateAt 0) (mtFiber43StateAt 2) (by decide) h0 (by decide)
      mtFiber43ReverseSingleStep2
  have h2 : mtFiber43StateAt 6 ∈ closeChainFiber mtWord mtFiber43DirectStates 2 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 1 [mtFiber43StateAt 0]
      (mtFiber43StateAt 2) (mtFiber43StateAt 6) (by decide) h1 (by decide)
      mtFiber43ReverseSingleStep6
  change mtFiber43StateAt 6 ∈ closeChainFiber mtWord mtFiber43DirectStates (2 + 14) [mtFiber43StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber43DirectStates 2 14 [mtFiber43StateAt 0] (mtFiber43StateAt 6) h2

theorem mtFiber43State7_in_close :
    mtFiber43StateAt 7 ∈ closeChainFiber mtWord mtFiber43DirectStates mtFiber43DirectStates.length [mtFiber43StateAt 0] := by
  have h0 : mtFiber43StateAt 0 ∈ closeChainFiber mtWord mtFiber43DirectStates 0 [mtFiber43StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber43StateAt 1 ∈ closeChainFiber mtWord mtFiber43DirectStates 1 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 0 [mtFiber43StateAt 0]
      (mtFiber43StateAt 0) (mtFiber43StateAt 1) (by decide) h0 (by decide)
      mtFiber43ReverseSingleStep1
  have h2 : mtFiber43StateAt 3 ∈ closeChainFiber mtWord mtFiber43DirectStates 2 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 1 [mtFiber43StateAt 0]
      (mtFiber43StateAt 1) (mtFiber43StateAt 3) (by decide) h1 (by decide)
      mtFiber43ReverseSingleStep3
  have h3 : mtFiber43StateAt 7 ∈ closeChainFiber mtWord mtFiber43DirectStates 3 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 2 [mtFiber43StateAt 0]
      (mtFiber43StateAt 3) (mtFiber43StateAt 7) (by decide) h2 (by decide)
      mtFiber43ReverseSingleStep7
  change mtFiber43StateAt 7 ∈ closeChainFiber mtWord mtFiber43DirectStates (3 + 13) [mtFiber43StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber43DirectStates 3 13 [mtFiber43StateAt 0] (mtFiber43StateAt 7) h3

theorem mtFiber43State8_in_close :
    mtFiber43StateAt 8 ∈ closeChainFiber mtWord mtFiber43DirectStates mtFiber43DirectStates.length [mtFiber43StateAt 0] := by
  have h0 : mtFiber43StateAt 0 ∈ closeChainFiber mtWord mtFiber43DirectStates 0 [mtFiber43StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber43StateAt 4 ∈ closeChainFiber mtWord mtFiber43DirectStates 1 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 0 [mtFiber43StateAt 0]
      (mtFiber43StateAt 0) (mtFiber43StateAt 4) (by decide) h0 (by decide)
      mtFiber43ReverseSingleStep4
  have h2 : mtFiber43StateAt 8 ∈ closeChainFiber mtWord mtFiber43DirectStates 2 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 1 [mtFiber43StateAt 0]
      (mtFiber43StateAt 4) (mtFiber43StateAt 8) (by decide) h1 (by decide)
      mtFiber43ReverseSingleStep8
  change mtFiber43StateAt 8 ∈ closeChainFiber mtWord mtFiber43DirectStates (2 + 14) [mtFiber43StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber43DirectStates 2 14 [mtFiber43StateAt 0] (mtFiber43StateAt 8) h2

theorem mtFiber43State9_in_close :
    mtFiber43StateAt 9 ∈ closeChainFiber mtWord mtFiber43DirectStates mtFiber43DirectStates.length [mtFiber43StateAt 0] := by
  have h0 : mtFiber43StateAt 0 ∈ closeChainFiber mtWord mtFiber43DirectStates 0 [mtFiber43StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber43StateAt 1 ∈ closeChainFiber mtWord mtFiber43DirectStates 1 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 0 [mtFiber43StateAt 0]
      (mtFiber43StateAt 0) (mtFiber43StateAt 1) (by decide) h0 (by decide)
      mtFiber43ReverseSingleStep1
  have h2 : mtFiber43StateAt 5 ∈ closeChainFiber mtWord mtFiber43DirectStates 2 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 1 [mtFiber43StateAt 0]
      (mtFiber43StateAt 1) (mtFiber43StateAt 5) (by decide) h1 (by decide)
      mtFiber43ReverseSingleStep5
  have h3 : mtFiber43StateAt 9 ∈ closeChainFiber mtWord mtFiber43DirectStates 3 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 2 [mtFiber43StateAt 0]
      (mtFiber43StateAt 5) (mtFiber43StateAt 9) (by decide) h2 (by decide)
      mtFiber43ReverseSingleStep9
  change mtFiber43StateAt 9 ∈ closeChainFiber mtWord mtFiber43DirectStates (3 + 13) [mtFiber43StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber43DirectStates 3 13 [mtFiber43StateAt 0] (mtFiber43StateAt 9) h3

theorem mtFiber43State10_in_close :
    mtFiber43StateAt 10 ∈ closeChainFiber mtWord mtFiber43DirectStates mtFiber43DirectStates.length [mtFiber43StateAt 0] := by
  have h0 : mtFiber43StateAt 0 ∈ closeChainFiber mtWord mtFiber43DirectStates 0 [mtFiber43StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber43StateAt 2 ∈ closeChainFiber mtWord mtFiber43DirectStates 1 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 0 [mtFiber43StateAt 0]
      (mtFiber43StateAt 0) (mtFiber43StateAt 2) (by decide) h0 (by decide)
      mtFiber43ReverseSingleStep2
  have h2 : mtFiber43StateAt 6 ∈ closeChainFiber mtWord mtFiber43DirectStates 2 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 1 [mtFiber43StateAt 0]
      (mtFiber43StateAt 2) (mtFiber43StateAt 6) (by decide) h1 (by decide)
      mtFiber43ReverseSingleStep6
  have h3 : mtFiber43StateAt 10 ∈ closeChainFiber mtWord mtFiber43DirectStates 3 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 2 [mtFiber43StateAt 0]
      (mtFiber43StateAt 6) (mtFiber43StateAt 10) (by decide) h2 (by decide)
      mtFiber43ReverseSingleStep10
  change mtFiber43StateAt 10 ∈ closeChainFiber mtWord mtFiber43DirectStates (3 + 13) [mtFiber43StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber43DirectStates 3 13 [mtFiber43StateAt 0] (mtFiber43StateAt 10) h3

theorem mtFiber43State11_in_close :
    mtFiber43StateAt 11 ∈ closeChainFiber mtWord mtFiber43DirectStates mtFiber43DirectStates.length [mtFiber43StateAt 0] := by
  have h0 : mtFiber43StateAt 0 ∈ closeChainFiber mtWord mtFiber43DirectStates 0 [mtFiber43StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber43StateAt 1 ∈ closeChainFiber mtWord mtFiber43DirectStates 1 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 0 [mtFiber43StateAt 0]
      (mtFiber43StateAt 0) (mtFiber43StateAt 1) (by decide) h0 (by decide)
      mtFiber43ReverseSingleStep1
  have h2 : mtFiber43StateAt 3 ∈ closeChainFiber mtWord mtFiber43DirectStates 2 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 1 [mtFiber43StateAt 0]
      (mtFiber43StateAt 1) (mtFiber43StateAt 3) (by decide) h1 (by decide)
      mtFiber43ReverseSingleStep3
  have h3 : mtFiber43StateAt 7 ∈ closeChainFiber mtWord mtFiber43DirectStates 3 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 2 [mtFiber43StateAt 0]
      (mtFiber43StateAt 3) (mtFiber43StateAt 7) (by decide) h2 (by decide)
      mtFiber43ReverseSingleStep7
  have h4 : mtFiber43StateAt 11 ∈ closeChainFiber mtWord mtFiber43DirectStates 4 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 3 [mtFiber43StateAt 0]
      (mtFiber43StateAt 7) (mtFiber43StateAt 11) (by decide) h3 (by decide)
      mtFiber43ReverseSingleStep11
  change mtFiber43StateAt 11 ∈ closeChainFiber mtWord mtFiber43DirectStates (4 + 12) [mtFiber43StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber43DirectStates 4 12 [mtFiber43StateAt 0] (mtFiber43StateAt 11) h4

theorem mtFiber43State12_in_close :
    mtFiber43StateAt 12 ∈ closeChainFiber mtWord mtFiber43DirectStates mtFiber43DirectStates.length [mtFiber43StateAt 0] := by
  have h0 : mtFiber43StateAt 0 ∈ closeChainFiber mtWord mtFiber43DirectStates 0 [mtFiber43StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber43StateAt 12 ∈ closeChainFiber mtWord mtFiber43DirectStates 1 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 0 [mtFiber43StateAt 0]
      (mtFiber43StateAt 0) (mtFiber43StateAt 12) (by decide) h0 (by decide)
      mtFiber43ReverseSingleStep12
  change mtFiber43StateAt 12 ∈ closeChainFiber mtWord mtFiber43DirectStates (1 + 15) [mtFiber43StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber43DirectStates 1 15 [mtFiber43StateAt 0] (mtFiber43StateAt 12) h1

theorem mtFiber43State13_in_close :
    mtFiber43StateAt 13 ∈ closeChainFiber mtWord mtFiber43DirectStates mtFiber43DirectStates.length [mtFiber43StateAt 0] := by
  have h0 : mtFiber43StateAt 0 ∈ closeChainFiber mtWord mtFiber43DirectStates 0 [mtFiber43StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber43StateAt 1 ∈ closeChainFiber mtWord mtFiber43DirectStates 1 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 0 [mtFiber43StateAt 0]
      (mtFiber43StateAt 0) (mtFiber43StateAt 1) (by decide) h0 (by decide)
      mtFiber43ReverseSingleStep1
  have h2 : mtFiber43StateAt 13 ∈ closeChainFiber mtWord mtFiber43DirectStates 2 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 1 [mtFiber43StateAt 0]
      (mtFiber43StateAt 1) (mtFiber43StateAt 13) (by decide) h1 (by decide)
      mtFiber43ReverseSingleStep13
  change mtFiber43StateAt 13 ∈ closeChainFiber mtWord mtFiber43DirectStates (2 + 14) [mtFiber43StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber43DirectStates 2 14 [mtFiber43StateAt 0] (mtFiber43StateAt 13) h2

theorem mtFiber43State14_in_close :
    mtFiber43StateAt 14 ∈ closeChainFiber mtWord mtFiber43DirectStates mtFiber43DirectStates.length [mtFiber43StateAt 0] := by
  have h0 : mtFiber43StateAt 0 ∈ closeChainFiber mtWord mtFiber43DirectStates 0 [mtFiber43StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber43StateAt 2 ∈ closeChainFiber mtWord mtFiber43DirectStates 1 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 0 [mtFiber43StateAt 0]
      (mtFiber43StateAt 0) (mtFiber43StateAt 2) (by decide) h0 (by decide)
      mtFiber43ReverseSingleStep2
  have h2 : mtFiber43StateAt 14 ∈ closeChainFiber mtWord mtFiber43DirectStates 2 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 1 [mtFiber43StateAt 0]
      (mtFiber43StateAt 2) (mtFiber43StateAt 14) (by decide) h1 (by decide)
      mtFiber43ReverseSingleStep14
  change mtFiber43StateAt 14 ∈ closeChainFiber mtWord mtFiber43DirectStates (2 + 14) [mtFiber43StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber43DirectStates 2 14 [mtFiber43StateAt 0] (mtFiber43StateAt 14) h2

theorem mtFiber43State15_in_close :
    mtFiber43StateAt 15 ∈ closeChainFiber mtWord mtFiber43DirectStates mtFiber43DirectStates.length [mtFiber43StateAt 0] := by
  have h0 : mtFiber43StateAt 0 ∈ closeChainFiber mtWord mtFiber43DirectStates 0 [mtFiber43StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber43StateAt 1 ∈ closeChainFiber mtWord mtFiber43DirectStates 1 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 0 [mtFiber43StateAt 0]
      (mtFiber43StateAt 0) (mtFiber43StateAt 1) (by decide) h0 (by decide)
      mtFiber43ReverseSingleStep1
  have h2 : mtFiber43StateAt 3 ∈ closeChainFiber mtWord mtFiber43DirectStates 2 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 1 [mtFiber43StateAt 0]
      (mtFiber43StateAt 1) (mtFiber43StateAt 3) (by decide) h1 (by decide)
      mtFiber43ReverseSingleStep3
  have h3 : mtFiber43StateAt 15 ∈ closeChainFiber mtWord mtFiber43DirectStates 3 [mtFiber43StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber43DirectStates 2 [mtFiber43StateAt 0]
      (mtFiber43StateAt 3) (mtFiber43StateAt 15) (by decide) h2 (by decide)
      mtFiber43ReverseSingleStep15
  change mtFiber43StateAt 15 ∈ closeChainFiber mtWord mtFiber43DirectStates (3 + 13) [mtFiber43StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber43DirectStates 3 13 [mtFiber43StateAt 0] (mtFiber43StateAt 15) h3

theorem mtFiber43DirectConnected :
    chainFiberConnected mtWord mtFiber43DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber43DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber43State0_in_close
  · subst state
    exact mtFiber43State1_in_close
  · subst state
    exact mtFiber43State2_in_close
  · subst state
    exact mtFiber43State3_in_close
  · subst state
    exact mtFiber43State4_in_close
  · subst state
    exact mtFiber43State5_in_close
  · subst state
    exact mtFiber43State6_in_close
  · subst state
    exact mtFiber43State7_in_close
  · subst state
    exact mtFiber43State8_in_close
  · subst state
    exact mtFiber43State9_in_close
  · subst state
    exact mtFiber43State10_in_close
  · subst state
    exact mtFiber43State11_in_close
  · subst state
    exact mtFiber43State12_in_close
  · subst state
    exact mtFiber43State13_in_close
  · subst state
    exact mtFiber43State14_in_close
  · subst state
    exact mtFiber43State15_in_close
  · cases h
def mtFiber45StateAt (i : Nat) : List TauState :=
  directStates (mtFiber45RowAt i).sourceLeft (mtFiber45RowAt i).sourceRight

def mtFiber45DirectStates : List (List TauState) :=
  [mtFiber45StateAt 0, mtFiber45StateAt 1, mtFiber45StateAt 2, mtFiber45StateAt 3, mtFiber45StateAt 4, mtFiber45StateAt 5, mtFiber45StateAt 6, mtFiber45StateAt 7, mtFiber45StateAt 8, mtFiber45StateAt 9, mtFiber45StateAt 10, mtFiber45StateAt 11, mtFiber45StateAt 12, mtFiber45StateAt 13, mtFiber45StateAt 14, mtFiber45StateAt 15]

theorem mtFiber45ReverseRow_1_ok :
    mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber45Chunk0_ok
  change (mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 0) &&
    mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber45ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber45StateAt 0) (mtFiber45StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber45StateAt 0) (mtFiber45StateAt 1)
    (mtFiber45RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber45Key mtFiber45Expected
        (mtFiber45RowAt 1) (by decide) mtFiber45ReverseRow_1_ok
      simpa [mtFiber45StateAt, mtFiber45RowAt, mtFiber45Rows, listGetD, directRow] using h)

theorem mtFiber45ReverseRow_2_ok :
    mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber45Chunk1_ok
  change (mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 2) &&
    mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber45ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber45StateAt 0) (mtFiber45StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber45StateAt 0) (mtFiber45StateAt 2)
    (mtFiber45RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber45Key mtFiber45Expected
        (mtFiber45RowAt 2) (by decide) mtFiber45ReverseRow_2_ok
      simpa [mtFiber45StateAt, mtFiber45RowAt, mtFiber45Rows, listGetD, directRow] using h)

theorem mtFiber45ReverseRow_3_ok :
    mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber45Chunk1_ok
  change (mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 2) &&
    mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber45ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber45StateAt 1) (mtFiber45StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber45StateAt 1) (mtFiber45StateAt 3)
    (mtFiber45RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber45Key mtFiber45Expected
        (mtFiber45RowAt 3) (by decide) mtFiber45ReverseRow_3_ok
      simpa [mtFiber45StateAt, mtFiber45RowAt, mtFiber45Rows, listGetD, directRow] using h)

theorem mtFiber45ReverseRow_4_ok :
    mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber45Chunk2_ok
  change (mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 4) &&
    mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber45ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber45StateAt 0) (mtFiber45StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber45StateAt 0) (mtFiber45StateAt 4)
    (mtFiber45RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber45Key mtFiber45Expected
        (mtFiber45RowAt 4) (by decide) mtFiber45ReverseRow_4_ok
      simpa [mtFiber45StateAt, mtFiber45RowAt, mtFiber45Rows, listGetD, directRow] using h)

theorem mtFiber45ReverseRow_5_ok :
    mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber45Chunk2_ok
  change (mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 4) &&
    mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber45ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber45StateAt 1) (mtFiber45StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber45StateAt 1) (mtFiber45StateAt 5)
    (mtFiber45RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber45Key mtFiber45Expected
        (mtFiber45RowAt 5) (by decide) mtFiber45ReverseRow_5_ok
      simpa [mtFiber45StateAt, mtFiber45RowAt, mtFiber45Rows, listGetD, directRow] using h)

theorem mtFiber45ReverseRow_6_ok :
    mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber45Chunk3_ok
  change (mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 6) &&
    mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber45ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber45StateAt 2) (mtFiber45StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber45StateAt 2) (mtFiber45StateAt 6)
    (mtFiber45RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber45Key mtFiber45Expected
        (mtFiber45RowAt 6) (by decide) mtFiber45ReverseRow_6_ok
      simpa [mtFiber45StateAt, mtFiber45RowAt, mtFiber45Rows, listGetD, directRow] using h)

theorem mtFiber45ReverseRow_7_ok :
    mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber45Chunk3_ok
  change (mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 6) &&
    mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber45ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber45StateAt 3) (mtFiber45StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber45StateAt 3) (mtFiber45StateAt 7)
    (mtFiber45RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber45Key mtFiber45Expected
        (mtFiber45RowAt 7) (by decide) mtFiber45ReverseRow_7_ok
      simpa [mtFiber45StateAt, mtFiber45RowAt, mtFiber45Rows, listGetD, directRow] using h)

theorem mtFiber45ReverseRow_8_ok :
    mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber45Chunk4_ok
  change (mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 8) &&
    mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber45ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber45StateAt 4) (mtFiber45StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber45StateAt 4) (mtFiber45StateAt 8)
    (mtFiber45RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber45Key mtFiber45Expected
        (mtFiber45RowAt 8) (by decide) mtFiber45ReverseRow_8_ok
      simpa [mtFiber45StateAt, mtFiber45RowAt, mtFiber45Rows, listGetD, directRow] using h)

theorem mtFiber45ReverseRow_9_ok :
    mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber45Chunk4_ok
  change (mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 8) &&
    mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber45ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber45StateAt 5) (mtFiber45StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber45StateAt 5) (mtFiber45StateAt 9)
    (mtFiber45RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber45Key mtFiber45Expected
        (mtFiber45RowAt 9) (by decide) mtFiber45ReverseRow_9_ok
      simpa [mtFiber45StateAt, mtFiber45RowAt, mtFiber45Rows, listGetD, directRow] using h)

theorem mtFiber45ReverseRow_10_ok :
    mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber45Chunk5_ok
  change (mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 10) &&
    mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber45ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber45StateAt 6) (mtFiber45StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber45StateAt 6) (mtFiber45StateAt 10)
    (mtFiber45RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber45Key mtFiber45Expected
        (mtFiber45RowAt 10) (by decide) mtFiber45ReverseRow_10_ok
      simpa [mtFiber45StateAt, mtFiber45RowAt, mtFiber45Rows, listGetD, directRow] using h)

theorem mtFiber45ReverseRow_11_ok :
    mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber45Chunk5_ok
  change (mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 10) &&
    mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber45ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber45StateAt 7) (mtFiber45StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber45StateAt 7) (mtFiber45StateAt 11)
    (mtFiber45RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber45Key mtFiber45Expected
        (mtFiber45RowAt 11) (by decide) mtFiber45ReverseRow_11_ok
      simpa [mtFiber45StateAt, mtFiber45RowAt, mtFiber45Rows, listGetD, directRow] using h)

theorem mtFiber45ReverseRow_12_ok :
    mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber45Chunk6_ok
  change (mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 12) &&
    mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber45ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber45StateAt 0) (mtFiber45StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber45StateAt 0) (mtFiber45StateAt 12)
    (mtFiber45RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber45Key mtFiber45Expected
        (mtFiber45RowAt 12) (by decide) mtFiber45ReverseRow_12_ok
      simpa [mtFiber45StateAt, mtFiber45RowAt, mtFiber45Rows, listGetD, directRow] using h)

theorem mtFiber45ReverseRow_13_ok :
    mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber45Chunk6_ok
  change (mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 12) &&
    mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber45ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber45StateAt 1) (mtFiber45StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber45StateAt 1) (mtFiber45StateAt 13)
    (mtFiber45RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber45Key mtFiber45Expected
        (mtFiber45RowAt 13) (by decide) mtFiber45ReverseRow_13_ok
      simpa [mtFiber45StateAt, mtFiber45RowAt, mtFiber45Rows, listGetD, directRow] using h)

theorem mtFiber45ReverseRow_14_ok :
    mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber45Chunk7_ok
  change (mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 14) &&
    mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber45ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber45StateAt 2) (mtFiber45StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber45StateAt 2) (mtFiber45StateAt 14)
    (mtFiber45RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber45Key mtFiber45Expected
        (mtFiber45RowAt 14) (by decide) mtFiber45ReverseRow_14_ok
      simpa [mtFiber45StateAt, mtFiber45RowAt, mtFiber45Rows, listGetD, directRow] using h)

theorem mtFiber45ReverseRow_15_ok :
    mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber45Chunk7_ok
  change (mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 14) &&
    mtRowReverseValid mtFiber45Key mtFiber45Expected (mtFiber45RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber45ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber45StateAt 3) (mtFiber45StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber45StateAt 3) (mtFiber45StateAt 15)
    (mtFiber45RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber45Key mtFiber45Expected
        (mtFiber45RowAt 15) (by decide) mtFiber45ReverseRow_15_ok
      simpa [mtFiber45StateAt, mtFiber45RowAt, mtFiber45Rows, listGetD, directRow] using h)

theorem mtFiber45State0_in_close :
    mtFiber45StateAt 0 ∈ closeChainFiber mtWord mtFiber45DirectStates mtFiber45DirectStates.length [mtFiber45StateAt 0] := by
  change mtFiber45StateAt 0 ∈ closeChainFiber mtWord mtFiber45DirectStates 16 [mtFiber45StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber45DirectStates 0 16 [mtFiber45StateAt 0] (mtFiber45StateAt 0) (by simp [closeChainFiber])

theorem mtFiber45State1_in_close :
    mtFiber45StateAt 1 ∈ closeChainFiber mtWord mtFiber45DirectStates mtFiber45DirectStates.length [mtFiber45StateAt 0] := by
  have h0 : mtFiber45StateAt 0 ∈ closeChainFiber mtWord mtFiber45DirectStates 0 [mtFiber45StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber45StateAt 1 ∈ closeChainFiber mtWord mtFiber45DirectStates 1 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 0 [mtFiber45StateAt 0]
      (mtFiber45StateAt 0) (mtFiber45StateAt 1) (by decide) h0 (by decide)
      mtFiber45ReverseSingleStep1
  change mtFiber45StateAt 1 ∈ closeChainFiber mtWord mtFiber45DirectStates (1 + 15) [mtFiber45StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber45DirectStates 1 15 [mtFiber45StateAt 0] (mtFiber45StateAt 1) h1

theorem mtFiber45State2_in_close :
    mtFiber45StateAt 2 ∈ closeChainFiber mtWord mtFiber45DirectStates mtFiber45DirectStates.length [mtFiber45StateAt 0] := by
  have h0 : mtFiber45StateAt 0 ∈ closeChainFiber mtWord mtFiber45DirectStates 0 [mtFiber45StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber45StateAt 2 ∈ closeChainFiber mtWord mtFiber45DirectStates 1 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 0 [mtFiber45StateAt 0]
      (mtFiber45StateAt 0) (mtFiber45StateAt 2) (by decide) h0 (by decide)
      mtFiber45ReverseSingleStep2
  change mtFiber45StateAt 2 ∈ closeChainFiber mtWord mtFiber45DirectStates (1 + 15) [mtFiber45StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber45DirectStates 1 15 [mtFiber45StateAt 0] (mtFiber45StateAt 2) h1

theorem mtFiber45State3_in_close :
    mtFiber45StateAt 3 ∈ closeChainFiber mtWord mtFiber45DirectStates mtFiber45DirectStates.length [mtFiber45StateAt 0] := by
  have h0 : mtFiber45StateAt 0 ∈ closeChainFiber mtWord mtFiber45DirectStates 0 [mtFiber45StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber45StateAt 1 ∈ closeChainFiber mtWord mtFiber45DirectStates 1 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 0 [mtFiber45StateAt 0]
      (mtFiber45StateAt 0) (mtFiber45StateAt 1) (by decide) h0 (by decide)
      mtFiber45ReverseSingleStep1
  have h2 : mtFiber45StateAt 3 ∈ closeChainFiber mtWord mtFiber45DirectStates 2 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 1 [mtFiber45StateAt 0]
      (mtFiber45StateAt 1) (mtFiber45StateAt 3) (by decide) h1 (by decide)
      mtFiber45ReverseSingleStep3
  change mtFiber45StateAt 3 ∈ closeChainFiber mtWord mtFiber45DirectStates (2 + 14) [mtFiber45StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber45DirectStates 2 14 [mtFiber45StateAt 0] (mtFiber45StateAt 3) h2

theorem mtFiber45State4_in_close :
    mtFiber45StateAt 4 ∈ closeChainFiber mtWord mtFiber45DirectStates mtFiber45DirectStates.length [mtFiber45StateAt 0] := by
  have h0 : mtFiber45StateAt 0 ∈ closeChainFiber mtWord mtFiber45DirectStates 0 [mtFiber45StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber45StateAt 4 ∈ closeChainFiber mtWord mtFiber45DirectStates 1 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 0 [mtFiber45StateAt 0]
      (mtFiber45StateAt 0) (mtFiber45StateAt 4) (by decide) h0 (by decide)
      mtFiber45ReverseSingleStep4
  change mtFiber45StateAt 4 ∈ closeChainFiber mtWord mtFiber45DirectStates (1 + 15) [mtFiber45StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber45DirectStates 1 15 [mtFiber45StateAt 0] (mtFiber45StateAt 4) h1

theorem mtFiber45State5_in_close :
    mtFiber45StateAt 5 ∈ closeChainFiber mtWord mtFiber45DirectStates mtFiber45DirectStates.length [mtFiber45StateAt 0] := by
  have h0 : mtFiber45StateAt 0 ∈ closeChainFiber mtWord mtFiber45DirectStates 0 [mtFiber45StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber45StateAt 1 ∈ closeChainFiber mtWord mtFiber45DirectStates 1 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 0 [mtFiber45StateAt 0]
      (mtFiber45StateAt 0) (mtFiber45StateAt 1) (by decide) h0 (by decide)
      mtFiber45ReverseSingleStep1
  have h2 : mtFiber45StateAt 5 ∈ closeChainFiber mtWord mtFiber45DirectStates 2 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 1 [mtFiber45StateAt 0]
      (mtFiber45StateAt 1) (mtFiber45StateAt 5) (by decide) h1 (by decide)
      mtFiber45ReverseSingleStep5
  change mtFiber45StateAt 5 ∈ closeChainFiber mtWord mtFiber45DirectStates (2 + 14) [mtFiber45StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber45DirectStates 2 14 [mtFiber45StateAt 0] (mtFiber45StateAt 5) h2

theorem mtFiber45State6_in_close :
    mtFiber45StateAt 6 ∈ closeChainFiber mtWord mtFiber45DirectStates mtFiber45DirectStates.length [mtFiber45StateAt 0] := by
  have h0 : mtFiber45StateAt 0 ∈ closeChainFiber mtWord mtFiber45DirectStates 0 [mtFiber45StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber45StateAt 2 ∈ closeChainFiber mtWord mtFiber45DirectStates 1 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 0 [mtFiber45StateAt 0]
      (mtFiber45StateAt 0) (mtFiber45StateAt 2) (by decide) h0 (by decide)
      mtFiber45ReverseSingleStep2
  have h2 : mtFiber45StateAt 6 ∈ closeChainFiber mtWord mtFiber45DirectStates 2 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 1 [mtFiber45StateAt 0]
      (mtFiber45StateAt 2) (mtFiber45StateAt 6) (by decide) h1 (by decide)
      mtFiber45ReverseSingleStep6
  change mtFiber45StateAt 6 ∈ closeChainFiber mtWord mtFiber45DirectStates (2 + 14) [mtFiber45StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber45DirectStates 2 14 [mtFiber45StateAt 0] (mtFiber45StateAt 6) h2

theorem mtFiber45State7_in_close :
    mtFiber45StateAt 7 ∈ closeChainFiber mtWord mtFiber45DirectStates mtFiber45DirectStates.length [mtFiber45StateAt 0] := by
  have h0 : mtFiber45StateAt 0 ∈ closeChainFiber mtWord mtFiber45DirectStates 0 [mtFiber45StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber45StateAt 1 ∈ closeChainFiber mtWord mtFiber45DirectStates 1 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 0 [mtFiber45StateAt 0]
      (mtFiber45StateAt 0) (mtFiber45StateAt 1) (by decide) h0 (by decide)
      mtFiber45ReverseSingleStep1
  have h2 : mtFiber45StateAt 3 ∈ closeChainFiber mtWord mtFiber45DirectStates 2 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 1 [mtFiber45StateAt 0]
      (mtFiber45StateAt 1) (mtFiber45StateAt 3) (by decide) h1 (by decide)
      mtFiber45ReverseSingleStep3
  have h3 : mtFiber45StateAt 7 ∈ closeChainFiber mtWord mtFiber45DirectStates 3 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 2 [mtFiber45StateAt 0]
      (mtFiber45StateAt 3) (mtFiber45StateAt 7) (by decide) h2 (by decide)
      mtFiber45ReverseSingleStep7
  change mtFiber45StateAt 7 ∈ closeChainFiber mtWord mtFiber45DirectStates (3 + 13) [mtFiber45StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber45DirectStates 3 13 [mtFiber45StateAt 0] (mtFiber45StateAt 7) h3

theorem mtFiber45State8_in_close :
    mtFiber45StateAt 8 ∈ closeChainFiber mtWord mtFiber45DirectStates mtFiber45DirectStates.length [mtFiber45StateAt 0] := by
  have h0 : mtFiber45StateAt 0 ∈ closeChainFiber mtWord mtFiber45DirectStates 0 [mtFiber45StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber45StateAt 4 ∈ closeChainFiber mtWord mtFiber45DirectStates 1 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 0 [mtFiber45StateAt 0]
      (mtFiber45StateAt 0) (mtFiber45StateAt 4) (by decide) h0 (by decide)
      mtFiber45ReverseSingleStep4
  have h2 : mtFiber45StateAt 8 ∈ closeChainFiber mtWord mtFiber45DirectStates 2 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 1 [mtFiber45StateAt 0]
      (mtFiber45StateAt 4) (mtFiber45StateAt 8) (by decide) h1 (by decide)
      mtFiber45ReverseSingleStep8
  change mtFiber45StateAt 8 ∈ closeChainFiber mtWord mtFiber45DirectStates (2 + 14) [mtFiber45StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber45DirectStates 2 14 [mtFiber45StateAt 0] (mtFiber45StateAt 8) h2

theorem mtFiber45State9_in_close :
    mtFiber45StateAt 9 ∈ closeChainFiber mtWord mtFiber45DirectStates mtFiber45DirectStates.length [mtFiber45StateAt 0] := by
  have h0 : mtFiber45StateAt 0 ∈ closeChainFiber mtWord mtFiber45DirectStates 0 [mtFiber45StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber45StateAt 1 ∈ closeChainFiber mtWord mtFiber45DirectStates 1 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 0 [mtFiber45StateAt 0]
      (mtFiber45StateAt 0) (mtFiber45StateAt 1) (by decide) h0 (by decide)
      mtFiber45ReverseSingleStep1
  have h2 : mtFiber45StateAt 5 ∈ closeChainFiber mtWord mtFiber45DirectStates 2 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 1 [mtFiber45StateAt 0]
      (mtFiber45StateAt 1) (mtFiber45StateAt 5) (by decide) h1 (by decide)
      mtFiber45ReverseSingleStep5
  have h3 : mtFiber45StateAt 9 ∈ closeChainFiber mtWord mtFiber45DirectStates 3 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 2 [mtFiber45StateAt 0]
      (mtFiber45StateAt 5) (mtFiber45StateAt 9) (by decide) h2 (by decide)
      mtFiber45ReverseSingleStep9
  change mtFiber45StateAt 9 ∈ closeChainFiber mtWord mtFiber45DirectStates (3 + 13) [mtFiber45StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber45DirectStates 3 13 [mtFiber45StateAt 0] (mtFiber45StateAt 9) h3

theorem mtFiber45State10_in_close :
    mtFiber45StateAt 10 ∈ closeChainFiber mtWord mtFiber45DirectStates mtFiber45DirectStates.length [mtFiber45StateAt 0] := by
  have h0 : mtFiber45StateAt 0 ∈ closeChainFiber mtWord mtFiber45DirectStates 0 [mtFiber45StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber45StateAt 2 ∈ closeChainFiber mtWord mtFiber45DirectStates 1 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 0 [mtFiber45StateAt 0]
      (mtFiber45StateAt 0) (mtFiber45StateAt 2) (by decide) h0 (by decide)
      mtFiber45ReverseSingleStep2
  have h2 : mtFiber45StateAt 6 ∈ closeChainFiber mtWord mtFiber45DirectStates 2 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 1 [mtFiber45StateAt 0]
      (mtFiber45StateAt 2) (mtFiber45StateAt 6) (by decide) h1 (by decide)
      mtFiber45ReverseSingleStep6
  have h3 : mtFiber45StateAt 10 ∈ closeChainFiber mtWord mtFiber45DirectStates 3 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 2 [mtFiber45StateAt 0]
      (mtFiber45StateAt 6) (mtFiber45StateAt 10) (by decide) h2 (by decide)
      mtFiber45ReverseSingleStep10
  change mtFiber45StateAt 10 ∈ closeChainFiber mtWord mtFiber45DirectStates (3 + 13) [mtFiber45StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber45DirectStates 3 13 [mtFiber45StateAt 0] (mtFiber45StateAt 10) h3

theorem mtFiber45State11_in_close :
    mtFiber45StateAt 11 ∈ closeChainFiber mtWord mtFiber45DirectStates mtFiber45DirectStates.length [mtFiber45StateAt 0] := by
  have h0 : mtFiber45StateAt 0 ∈ closeChainFiber mtWord mtFiber45DirectStates 0 [mtFiber45StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber45StateAt 1 ∈ closeChainFiber mtWord mtFiber45DirectStates 1 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 0 [mtFiber45StateAt 0]
      (mtFiber45StateAt 0) (mtFiber45StateAt 1) (by decide) h0 (by decide)
      mtFiber45ReverseSingleStep1
  have h2 : mtFiber45StateAt 3 ∈ closeChainFiber mtWord mtFiber45DirectStates 2 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 1 [mtFiber45StateAt 0]
      (mtFiber45StateAt 1) (mtFiber45StateAt 3) (by decide) h1 (by decide)
      mtFiber45ReverseSingleStep3
  have h3 : mtFiber45StateAt 7 ∈ closeChainFiber mtWord mtFiber45DirectStates 3 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 2 [mtFiber45StateAt 0]
      (mtFiber45StateAt 3) (mtFiber45StateAt 7) (by decide) h2 (by decide)
      mtFiber45ReverseSingleStep7
  have h4 : mtFiber45StateAt 11 ∈ closeChainFiber mtWord mtFiber45DirectStates 4 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 3 [mtFiber45StateAt 0]
      (mtFiber45StateAt 7) (mtFiber45StateAt 11) (by decide) h3 (by decide)
      mtFiber45ReverseSingleStep11
  change mtFiber45StateAt 11 ∈ closeChainFiber mtWord mtFiber45DirectStates (4 + 12) [mtFiber45StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber45DirectStates 4 12 [mtFiber45StateAt 0] (mtFiber45StateAt 11) h4

theorem mtFiber45State12_in_close :
    mtFiber45StateAt 12 ∈ closeChainFiber mtWord mtFiber45DirectStates mtFiber45DirectStates.length [mtFiber45StateAt 0] := by
  have h0 : mtFiber45StateAt 0 ∈ closeChainFiber mtWord mtFiber45DirectStates 0 [mtFiber45StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber45StateAt 12 ∈ closeChainFiber mtWord mtFiber45DirectStates 1 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 0 [mtFiber45StateAt 0]
      (mtFiber45StateAt 0) (mtFiber45StateAt 12) (by decide) h0 (by decide)
      mtFiber45ReverseSingleStep12
  change mtFiber45StateAt 12 ∈ closeChainFiber mtWord mtFiber45DirectStates (1 + 15) [mtFiber45StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber45DirectStates 1 15 [mtFiber45StateAt 0] (mtFiber45StateAt 12) h1

theorem mtFiber45State13_in_close :
    mtFiber45StateAt 13 ∈ closeChainFiber mtWord mtFiber45DirectStates mtFiber45DirectStates.length [mtFiber45StateAt 0] := by
  have h0 : mtFiber45StateAt 0 ∈ closeChainFiber mtWord mtFiber45DirectStates 0 [mtFiber45StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber45StateAt 1 ∈ closeChainFiber mtWord mtFiber45DirectStates 1 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 0 [mtFiber45StateAt 0]
      (mtFiber45StateAt 0) (mtFiber45StateAt 1) (by decide) h0 (by decide)
      mtFiber45ReverseSingleStep1
  have h2 : mtFiber45StateAt 13 ∈ closeChainFiber mtWord mtFiber45DirectStates 2 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 1 [mtFiber45StateAt 0]
      (mtFiber45StateAt 1) (mtFiber45StateAt 13) (by decide) h1 (by decide)
      mtFiber45ReverseSingleStep13
  change mtFiber45StateAt 13 ∈ closeChainFiber mtWord mtFiber45DirectStates (2 + 14) [mtFiber45StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber45DirectStates 2 14 [mtFiber45StateAt 0] (mtFiber45StateAt 13) h2

theorem mtFiber45State14_in_close :
    mtFiber45StateAt 14 ∈ closeChainFiber mtWord mtFiber45DirectStates mtFiber45DirectStates.length [mtFiber45StateAt 0] := by
  have h0 : mtFiber45StateAt 0 ∈ closeChainFiber mtWord mtFiber45DirectStates 0 [mtFiber45StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber45StateAt 2 ∈ closeChainFiber mtWord mtFiber45DirectStates 1 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 0 [mtFiber45StateAt 0]
      (mtFiber45StateAt 0) (mtFiber45StateAt 2) (by decide) h0 (by decide)
      mtFiber45ReverseSingleStep2
  have h2 : mtFiber45StateAt 14 ∈ closeChainFiber mtWord mtFiber45DirectStates 2 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 1 [mtFiber45StateAt 0]
      (mtFiber45StateAt 2) (mtFiber45StateAt 14) (by decide) h1 (by decide)
      mtFiber45ReverseSingleStep14
  change mtFiber45StateAt 14 ∈ closeChainFiber mtWord mtFiber45DirectStates (2 + 14) [mtFiber45StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber45DirectStates 2 14 [mtFiber45StateAt 0] (mtFiber45StateAt 14) h2

theorem mtFiber45State15_in_close :
    mtFiber45StateAt 15 ∈ closeChainFiber mtWord mtFiber45DirectStates mtFiber45DirectStates.length [mtFiber45StateAt 0] := by
  have h0 : mtFiber45StateAt 0 ∈ closeChainFiber mtWord mtFiber45DirectStates 0 [mtFiber45StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber45StateAt 1 ∈ closeChainFiber mtWord mtFiber45DirectStates 1 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 0 [mtFiber45StateAt 0]
      (mtFiber45StateAt 0) (mtFiber45StateAt 1) (by decide) h0 (by decide)
      mtFiber45ReverseSingleStep1
  have h2 : mtFiber45StateAt 3 ∈ closeChainFiber mtWord mtFiber45DirectStates 2 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 1 [mtFiber45StateAt 0]
      (mtFiber45StateAt 1) (mtFiber45StateAt 3) (by decide) h1 (by decide)
      mtFiber45ReverseSingleStep3
  have h3 : mtFiber45StateAt 15 ∈ closeChainFiber mtWord mtFiber45DirectStates 3 [mtFiber45StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber45DirectStates 2 [mtFiber45StateAt 0]
      (mtFiber45StateAt 3) (mtFiber45StateAt 15) (by decide) h2 (by decide)
      mtFiber45ReverseSingleStep15
  change mtFiber45StateAt 15 ∈ closeChainFiber mtWord mtFiber45DirectStates (3 + 13) [mtFiber45StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber45DirectStates 3 13 [mtFiber45StateAt 0] (mtFiber45StateAt 15) h3

theorem mtFiber45DirectConnected :
    chainFiberConnected mtWord mtFiber45DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber45DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber45State0_in_close
  · subst state
    exact mtFiber45State1_in_close
  · subst state
    exact mtFiber45State2_in_close
  · subst state
    exact mtFiber45State3_in_close
  · subst state
    exact mtFiber45State4_in_close
  · subst state
    exact mtFiber45State5_in_close
  · subst state
    exact mtFiber45State6_in_close
  · subst state
    exact mtFiber45State7_in_close
  · subst state
    exact mtFiber45State8_in_close
  · subst state
    exact mtFiber45State9_in_close
  · subst state
    exact mtFiber45State10_in_close
  · subst state
    exact mtFiber45State11_in_close
  · subst state
    exact mtFiber45State12_in_close
  · subst state
    exact mtFiber45State13_in_close
  · subst state
    exact mtFiber45State14_in_close
  · subst state
    exact mtFiber45State15_in_close
  · cases h
def mtFiber47StateAt (i : Nat) : List TauState :=
  directStates (mtFiber47RowAt i).sourceLeft (mtFiber47RowAt i).sourceRight

def mtFiber47DirectStates : List (List TauState) :=
  [mtFiber47StateAt 0, mtFiber47StateAt 1, mtFiber47StateAt 2, mtFiber47StateAt 3, mtFiber47StateAt 4, mtFiber47StateAt 5, mtFiber47StateAt 6, mtFiber47StateAt 7, mtFiber47StateAt 8, mtFiber47StateAt 9, mtFiber47StateAt 10, mtFiber47StateAt 11, mtFiber47StateAt 12, mtFiber47StateAt 13, mtFiber47StateAt 14, mtFiber47StateAt 15]

theorem mtFiber47ReverseRow_1_ok :
    mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber47Chunk0_ok
  change (mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 0) &&
    mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber47ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber47StateAt 0) (mtFiber47StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber47StateAt 0) (mtFiber47StateAt 1)
    (mtFiber47RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber47Key mtFiber47Expected
        (mtFiber47RowAt 1) (by decide) mtFiber47ReverseRow_1_ok
      simpa [mtFiber47StateAt, mtFiber47RowAt, mtFiber47Rows, listGetD, directRow] using h)

theorem mtFiber47ReverseRow_2_ok :
    mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber47Chunk1_ok
  change (mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 2) &&
    mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber47ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber47StateAt 0) (mtFiber47StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber47StateAt 0) (mtFiber47StateAt 2)
    (mtFiber47RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber47Key mtFiber47Expected
        (mtFiber47RowAt 2) (by decide) mtFiber47ReverseRow_2_ok
      simpa [mtFiber47StateAt, mtFiber47RowAt, mtFiber47Rows, listGetD, directRow] using h)

theorem mtFiber47ReverseRow_3_ok :
    mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber47Chunk1_ok
  change (mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 2) &&
    mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber47ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber47StateAt 1) (mtFiber47StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber47StateAt 1) (mtFiber47StateAt 3)
    (mtFiber47RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber47Key mtFiber47Expected
        (mtFiber47RowAt 3) (by decide) mtFiber47ReverseRow_3_ok
      simpa [mtFiber47StateAt, mtFiber47RowAt, mtFiber47Rows, listGetD, directRow] using h)

theorem mtFiber47ReverseRow_4_ok :
    mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber47Chunk2_ok
  change (mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 4) &&
    mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber47ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber47StateAt 0) (mtFiber47StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber47StateAt 0) (mtFiber47StateAt 4)
    (mtFiber47RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber47Key mtFiber47Expected
        (mtFiber47RowAt 4) (by decide) mtFiber47ReverseRow_4_ok
      simpa [mtFiber47StateAt, mtFiber47RowAt, mtFiber47Rows, listGetD, directRow] using h)

theorem mtFiber47ReverseRow_5_ok :
    mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber47Chunk2_ok
  change (mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 4) &&
    mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber47ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber47StateAt 1) (mtFiber47StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber47StateAt 1) (mtFiber47StateAt 5)
    (mtFiber47RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber47Key mtFiber47Expected
        (mtFiber47RowAt 5) (by decide) mtFiber47ReverseRow_5_ok
      simpa [mtFiber47StateAt, mtFiber47RowAt, mtFiber47Rows, listGetD, directRow] using h)

theorem mtFiber47ReverseRow_6_ok :
    mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber47Chunk3_ok
  change (mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 6) &&
    mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber47ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber47StateAt 2) (mtFiber47StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber47StateAt 2) (mtFiber47StateAt 6)
    (mtFiber47RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber47Key mtFiber47Expected
        (mtFiber47RowAt 6) (by decide) mtFiber47ReverseRow_6_ok
      simpa [mtFiber47StateAt, mtFiber47RowAt, mtFiber47Rows, listGetD, directRow] using h)

theorem mtFiber47ReverseRow_7_ok :
    mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber47Chunk3_ok
  change (mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 6) &&
    mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber47ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber47StateAt 3) (mtFiber47StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber47StateAt 3) (mtFiber47StateAt 7)
    (mtFiber47RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber47Key mtFiber47Expected
        (mtFiber47RowAt 7) (by decide) mtFiber47ReverseRow_7_ok
      simpa [mtFiber47StateAt, mtFiber47RowAt, mtFiber47Rows, listGetD, directRow] using h)

theorem mtFiber47ReverseRow_8_ok :
    mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber47Chunk4_ok
  change (mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 8) &&
    mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber47ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber47StateAt 4) (mtFiber47StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber47StateAt 4) (mtFiber47StateAt 8)
    (mtFiber47RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber47Key mtFiber47Expected
        (mtFiber47RowAt 8) (by decide) mtFiber47ReverseRow_8_ok
      simpa [mtFiber47StateAt, mtFiber47RowAt, mtFiber47Rows, listGetD, directRow] using h)

theorem mtFiber47ReverseRow_9_ok :
    mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber47Chunk4_ok
  change (mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 8) &&
    mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber47ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber47StateAt 5) (mtFiber47StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber47StateAt 5) (mtFiber47StateAt 9)
    (mtFiber47RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber47Key mtFiber47Expected
        (mtFiber47RowAt 9) (by decide) mtFiber47ReverseRow_9_ok
      simpa [mtFiber47StateAt, mtFiber47RowAt, mtFiber47Rows, listGetD, directRow] using h)

theorem mtFiber47ReverseRow_10_ok :
    mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber47Chunk5_ok
  change (mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 10) &&
    mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber47ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber47StateAt 6) (mtFiber47StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber47StateAt 6) (mtFiber47StateAt 10)
    (mtFiber47RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber47Key mtFiber47Expected
        (mtFiber47RowAt 10) (by decide) mtFiber47ReverseRow_10_ok
      simpa [mtFiber47StateAt, mtFiber47RowAt, mtFiber47Rows, listGetD, directRow] using h)

theorem mtFiber47ReverseRow_11_ok :
    mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber47Chunk5_ok
  change (mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 10) &&
    mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber47ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber47StateAt 7) (mtFiber47StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber47StateAt 7) (mtFiber47StateAt 11)
    (mtFiber47RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber47Key mtFiber47Expected
        (mtFiber47RowAt 11) (by decide) mtFiber47ReverseRow_11_ok
      simpa [mtFiber47StateAt, mtFiber47RowAt, mtFiber47Rows, listGetD, directRow] using h)

theorem mtFiber47ReverseRow_12_ok :
    mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber47Chunk6_ok
  change (mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 12) &&
    mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber47ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber47StateAt 0) (mtFiber47StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber47StateAt 0) (mtFiber47StateAt 12)
    (mtFiber47RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber47Key mtFiber47Expected
        (mtFiber47RowAt 12) (by decide) mtFiber47ReverseRow_12_ok
      simpa [mtFiber47StateAt, mtFiber47RowAt, mtFiber47Rows, listGetD, directRow] using h)

theorem mtFiber47ReverseRow_13_ok :
    mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber47Chunk6_ok
  change (mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 12) &&
    mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber47ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber47StateAt 1) (mtFiber47StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber47StateAt 1) (mtFiber47StateAt 13)
    (mtFiber47RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber47Key mtFiber47Expected
        (mtFiber47RowAt 13) (by decide) mtFiber47ReverseRow_13_ok
      simpa [mtFiber47StateAt, mtFiber47RowAt, mtFiber47Rows, listGetD, directRow] using h)

theorem mtFiber47ReverseRow_14_ok :
    mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber47Chunk7_ok
  change (mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 14) &&
    mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber47ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber47StateAt 2) (mtFiber47StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber47StateAt 2) (mtFiber47StateAt 14)
    (mtFiber47RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber47Key mtFiber47Expected
        (mtFiber47RowAt 14) (by decide) mtFiber47ReverseRow_14_ok
      simpa [mtFiber47StateAt, mtFiber47RowAt, mtFiber47Rows, listGetD, directRow] using h)

theorem mtFiber47ReverseRow_15_ok :
    mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber47Chunk7_ok
  change (mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 14) &&
    mtRowReverseValid mtFiber47Key mtFiber47Expected (mtFiber47RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber47ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber47StateAt 3) (mtFiber47StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber47StateAt 3) (mtFiber47StateAt 15)
    (mtFiber47RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber47Key mtFiber47Expected
        (mtFiber47RowAt 15) (by decide) mtFiber47ReverseRow_15_ok
      simpa [mtFiber47StateAt, mtFiber47RowAt, mtFiber47Rows, listGetD, directRow] using h)

theorem mtFiber47State0_in_close :
    mtFiber47StateAt 0 ∈ closeChainFiber mtWord mtFiber47DirectStates mtFiber47DirectStates.length [mtFiber47StateAt 0] := by
  change mtFiber47StateAt 0 ∈ closeChainFiber mtWord mtFiber47DirectStates 16 [mtFiber47StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber47DirectStates 0 16 [mtFiber47StateAt 0] (mtFiber47StateAt 0) (by simp [closeChainFiber])

theorem mtFiber47State1_in_close :
    mtFiber47StateAt 1 ∈ closeChainFiber mtWord mtFiber47DirectStates mtFiber47DirectStates.length [mtFiber47StateAt 0] := by
  have h0 : mtFiber47StateAt 0 ∈ closeChainFiber mtWord mtFiber47DirectStates 0 [mtFiber47StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber47StateAt 1 ∈ closeChainFiber mtWord mtFiber47DirectStates 1 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 0 [mtFiber47StateAt 0]
      (mtFiber47StateAt 0) (mtFiber47StateAt 1) (by decide) h0 (by decide)
      mtFiber47ReverseSingleStep1
  change mtFiber47StateAt 1 ∈ closeChainFiber mtWord mtFiber47DirectStates (1 + 15) [mtFiber47StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber47DirectStates 1 15 [mtFiber47StateAt 0] (mtFiber47StateAt 1) h1

theorem mtFiber47State2_in_close :
    mtFiber47StateAt 2 ∈ closeChainFiber mtWord mtFiber47DirectStates mtFiber47DirectStates.length [mtFiber47StateAt 0] := by
  have h0 : mtFiber47StateAt 0 ∈ closeChainFiber mtWord mtFiber47DirectStates 0 [mtFiber47StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber47StateAt 2 ∈ closeChainFiber mtWord mtFiber47DirectStates 1 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 0 [mtFiber47StateAt 0]
      (mtFiber47StateAt 0) (mtFiber47StateAt 2) (by decide) h0 (by decide)
      mtFiber47ReverseSingleStep2
  change mtFiber47StateAt 2 ∈ closeChainFiber mtWord mtFiber47DirectStates (1 + 15) [mtFiber47StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber47DirectStates 1 15 [mtFiber47StateAt 0] (mtFiber47StateAt 2) h1

theorem mtFiber47State3_in_close :
    mtFiber47StateAt 3 ∈ closeChainFiber mtWord mtFiber47DirectStates mtFiber47DirectStates.length [mtFiber47StateAt 0] := by
  have h0 : mtFiber47StateAt 0 ∈ closeChainFiber mtWord mtFiber47DirectStates 0 [mtFiber47StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber47StateAt 1 ∈ closeChainFiber mtWord mtFiber47DirectStates 1 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 0 [mtFiber47StateAt 0]
      (mtFiber47StateAt 0) (mtFiber47StateAt 1) (by decide) h0 (by decide)
      mtFiber47ReverseSingleStep1
  have h2 : mtFiber47StateAt 3 ∈ closeChainFiber mtWord mtFiber47DirectStates 2 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 1 [mtFiber47StateAt 0]
      (mtFiber47StateAt 1) (mtFiber47StateAt 3) (by decide) h1 (by decide)
      mtFiber47ReverseSingleStep3
  change mtFiber47StateAt 3 ∈ closeChainFiber mtWord mtFiber47DirectStates (2 + 14) [mtFiber47StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber47DirectStates 2 14 [mtFiber47StateAt 0] (mtFiber47StateAt 3) h2

theorem mtFiber47State4_in_close :
    mtFiber47StateAt 4 ∈ closeChainFiber mtWord mtFiber47DirectStates mtFiber47DirectStates.length [mtFiber47StateAt 0] := by
  have h0 : mtFiber47StateAt 0 ∈ closeChainFiber mtWord mtFiber47DirectStates 0 [mtFiber47StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber47StateAt 4 ∈ closeChainFiber mtWord mtFiber47DirectStates 1 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 0 [mtFiber47StateAt 0]
      (mtFiber47StateAt 0) (mtFiber47StateAt 4) (by decide) h0 (by decide)
      mtFiber47ReverseSingleStep4
  change mtFiber47StateAt 4 ∈ closeChainFiber mtWord mtFiber47DirectStates (1 + 15) [mtFiber47StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber47DirectStates 1 15 [mtFiber47StateAt 0] (mtFiber47StateAt 4) h1

theorem mtFiber47State5_in_close :
    mtFiber47StateAt 5 ∈ closeChainFiber mtWord mtFiber47DirectStates mtFiber47DirectStates.length [mtFiber47StateAt 0] := by
  have h0 : mtFiber47StateAt 0 ∈ closeChainFiber mtWord mtFiber47DirectStates 0 [mtFiber47StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber47StateAt 1 ∈ closeChainFiber mtWord mtFiber47DirectStates 1 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 0 [mtFiber47StateAt 0]
      (mtFiber47StateAt 0) (mtFiber47StateAt 1) (by decide) h0 (by decide)
      mtFiber47ReverseSingleStep1
  have h2 : mtFiber47StateAt 5 ∈ closeChainFiber mtWord mtFiber47DirectStates 2 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 1 [mtFiber47StateAt 0]
      (mtFiber47StateAt 1) (mtFiber47StateAt 5) (by decide) h1 (by decide)
      mtFiber47ReverseSingleStep5
  change mtFiber47StateAt 5 ∈ closeChainFiber mtWord mtFiber47DirectStates (2 + 14) [mtFiber47StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber47DirectStates 2 14 [mtFiber47StateAt 0] (mtFiber47StateAt 5) h2

theorem mtFiber47State6_in_close :
    mtFiber47StateAt 6 ∈ closeChainFiber mtWord mtFiber47DirectStates mtFiber47DirectStates.length [mtFiber47StateAt 0] := by
  have h0 : mtFiber47StateAt 0 ∈ closeChainFiber mtWord mtFiber47DirectStates 0 [mtFiber47StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber47StateAt 2 ∈ closeChainFiber mtWord mtFiber47DirectStates 1 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 0 [mtFiber47StateAt 0]
      (mtFiber47StateAt 0) (mtFiber47StateAt 2) (by decide) h0 (by decide)
      mtFiber47ReverseSingleStep2
  have h2 : mtFiber47StateAt 6 ∈ closeChainFiber mtWord mtFiber47DirectStates 2 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 1 [mtFiber47StateAt 0]
      (mtFiber47StateAt 2) (mtFiber47StateAt 6) (by decide) h1 (by decide)
      mtFiber47ReverseSingleStep6
  change mtFiber47StateAt 6 ∈ closeChainFiber mtWord mtFiber47DirectStates (2 + 14) [mtFiber47StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber47DirectStates 2 14 [mtFiber47StateAt 0] (mtFiber47StateAt 6) h2

theorem mtFiber47State7_in_close :
    mtFiber47StateAt 7 ∈ closeChainFiber mtWord mtFiber47DirectStates mtFiber47DirectStates.length [mtFiber47StateAt 0] := by
  have h0 : mtFiber47StateAt 0 ∈ closeChainFiber mtWord mtFiber47DirectStates 0 [mtFiber47StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber47StateAt 1 ∈ closeChainFiber mtWord mtFiber47DirectStates 1 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 0 [mtFiber47StateAt 0]
      (mtFiber47StateAt 0) (mtFiber47StateAt 1) (by decide) h0 (by decide)
      mtFiber47ReverseSingleStep1
  have h2 : mtFiber47StateAt 3 ∈ closeChainFiber mtWord mtFiber47DirectStates 2 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 1 [mtFiber47StateAt 0]
      (mtFiber47StateAt 1) (mtFiber47StateAt 3) (by decide) h1 (by decide)
      mtFiber47ReverseSingleStep3
  have h3 : mtFiber47StateAt 7 ∈ closeChainFiber mtWord mtFiber47DirectStates 3 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 2 [mtFiber47StateAt 0]
      (mtFiber47StateAt 3) (mtFiber47StateAt 7) (by decide) h2 (by decide)
      mtFiber47ReverseSingleStep7
  change mtFiber47StateAt 7 ∈ closeChainFiber mtWord mtFiber47DirectStates (3 + 13) [mtFiber47StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber47DirectStates 3 13 [mtFiber47StateAt 0] (mtFiber47StateAt 7) h3

theorem mtFiber47State8_in_close :
    mtFiber47StateAt 8 ∈ closeChainFiber mtWord mtFiber47DirectStates mtFiber47DirectStates.length [mtFiber47StateAt 0] := by
  have h0 : mtFiber47StateAt 0 ∈ closeChainFiber mtWord mtFiber47DirectStates 0 [mtFiber47StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber47StateAt 4 ∈ closeChainFiber mtWord mtFiber47DirectStates 1 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 0 [mtFiber47StateAt 0]
      (mtFiber47StateAt 0) (mtFiber47StateAt 4) (by decide) h0 (by decide)
      mtFiber47ReverseSingleStep4
  have h2 : mtFiber47StateAt 8 ∈ closeChainFiber mtWord mtFiber47DirectStates 2 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 1 [mtFiber47StateAt 0]
      (mtFiber47StateAt 4) (mtFiber47StateAt 8) (by decide) h1 (by decide)
      mtFiber47ReverseSingleStep8
  change mtFiber47StateAt 8 ∈ closeChainFiber mtWord mtFiber47DirectStates (2 + 14) [mtFiber47StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber47DirectStates 2 14 [mtFiber47StateAt 0] (mtFiber47StateAt 8) h2

theorem mtFiber47State9_in_close :
    mtFiber47StateAt 9 ∈ closeChainFiber mtWord mtFiber47DirectStates mtFiber47DirectStates.length [mtFiber47StateAt 0] := by
  have h0 : mtFiber47StateAt 0 ∈ closeChainFiber mtWord mtFiber47DirectStates 0 [mtFiber47StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber47StateAt 1 ∈ closeChainFiber mtWord mtFiber47DirectStates 1 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 0 [mtFiber47StateAt 0]
      (mtFiber47StateAt 0) (mtFiber47StateAt 1) (by decide) h0 (by decide)
      mtFiber47ReverseSingleStep1
  have h2 : mtFiber47StateAt 5 ∈ closeChainFiber mtWord mtFiber47DirectStates 2 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 1 [mtFiber47StateAt 0]
      (mtFiber47StateAt 1) (mtFiber47StateAt 5) (by decide) h1 (by decide)
      mtFiber47ReverseSingleStep5
  have h3 : mtFiber47StateAt 9 ∈ closeChainFiber mtWord mtFiber47DirectStates 3 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 2 [mtFiber47StateAt 0]
      (mtFiber47StateAt 5) (mtFiber47StateAt 9) (by decide) h2 (by decide)
      mtFiber47ReverseSingleStep9
  change mtFiber47StateAt 9 ∈ closeChainFiber mtWord mtFiber47DirectStates (3 + 13) [mtFiber47StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber47DirectStates 3 13 [mtFiber47StateAt 0] (mtFiber47StateAt 9) h3

theorem mtFiber47State10_in_close :
    mtFiber47StateAt 10 ∈ closeChainFiber mtWord mtFiber47DirectStates mtFiber47DirectStates.length [mtFiber47StateAt 0] := by
  have h0 : mtFiber47StateAt 0 ∈ closeChainFiber mtWord mtFiber47DirectStates 0 [mtFiber47StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber47StateAt 2 ∈ closeChainFiber mtWord mtFiber47DirectStates 1 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 0 [mtFiber47StateAt 0]
      (mtFiber47StateAt 0) (mtFiber47StateAt 2) (by decide) h0 (by decide)
      mtFiber47ReverseSingleStep2
  have h2 : mtFiber47StateAt 6 ∈ closeChainFiber mtWord mtFiber47DirectStates 2 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 1 [mtFiber47StateAt 0]
      (mtFiber47StateAt 2) (mtFiber47StateAt 6) (by decide) h1 (by decide)
      mtFiber47ReverseSingleStep6
  have h3 : mtFiber47StateAt 10 ∈ closeChainFiber mtWord mtFiber47DirectStates 3 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 2 [mtFiber47StateAt 0]
      (mtFiber47StateAt 6) (mtFiber47StateAt 10) (by decide) h2 (by decide)
      mtFiber47ReverseSingleStep10
  change mtFiber47StateAt 10 ∈ closeChainFiber mtWord mtFiber47DirectStates (3 + 13) [mtFiber47StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber47DirectStates 3 13 [mtFiber47StateAt 0] (mtFiber47StateAt 10) h3

theorem mtFiber47State11_in_close :
    mtFiber47StateAt 11 ∈ closeChainFiber mtWord mtFiber47DirectStates mtFiber47DirectStates.length [mtFiber47StateAt 0] := by
  have h0 : mtFiber47StateAt 0 ∈ closeChainFiber mtWord mtFiber47DirectStates 0 [mtFiber47StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber47StateAt 1 ∈ closeChainFiber mtWord mtFiber47DirectStates 1 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 0 [mtFiber47StateAt 0]
      (mtFiber47StateAt 0) (mtFiber47StateAt 1) (by decide) h0 (by decide)
      mtFiber47ReverseSingleStep1
  have h2 : mtFiber47StateAt 3 ∈ closeChainFiber mtWord mtFiber47DirectStates 2 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 1 [mtFiber47StateAt 0]
      (mtFiber47StateAt 1) (mtFiber47StateAt 3) (by decide) h1 (by decide)
      mtFiber47ReverseSingleStep3
  have h3 : mtFiber47StateAt 7 ∈ closeChainFiber mtWord mtFiber47DirectStates 3 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 2 [mtFiber47StateAt 0]
      (mtFiber47StateAt 3) (mtFiber47StateAt 7) (by decide) h2 (by decide)
      mtFiber47ReverseSingleStep7
  have h4 : mtFiber47StateAt 11 ∈ closeChainFiber mtWord mtFiber47DirectStates 4 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 3 [mtFiber47StateAt 0]
      (mtFiber47StateAt 7) (mtFiber47StateAt 11) (by decide) h3 (by decide)
      mtFiber47ReverseSingleStep11
  change mtFiber47StateAt 11 ∈ closeChainFiber mtWord mtFiber47DirectStates (4 + 12) [mtFiber47StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber47DirectStates 4 12 [mtFiber47StateAt 0] (mtFiber47StateAt 11) h4

theorem mtFiber47State12_in_close :
    mtFiber47StateAt 12 ∈ closeChainFiber mtWord mtFiber47DirectStates mtFiber47DirectStates.length [mtFiber47StateAt 0] := by
  have h0 : mtFiber47StateAt 0 ∈ closeChainFiber mtWord mtFiber47DirectStates 0 [mtFiber47StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber47StateAt 12 ∈ closeChainFiber mtWord mtFiber47DirectStates 1 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 0 [mtFiber47StateAt 0]
      (mtFiber47StateAt 0) (mtFiber47StateAt 12) (by decide) h0 (by decide)
      mtFiber47ReverseSingleStep12
  change mtFiber47StateAt 12 ∈ closeChainFiber mtWord mtFiber47DirectStates (1 + 15) [mtFiber47StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber47DirectStates 1 15 [mtFiber47StateAt 0] (mtFiber47StateAt 12) h1

theorem mtFiber47State13_in_close :
    mtFiber47StateAt 13 ∈ closeChainFiber mtWord mtFiber47DirectStates mtFiber47DirectStates.length [mtFiber47StateAt 0] := by
  have h0 : mtFiber47StateAt 0 ∈ closeChainFiber mtWord mtFiber47DirectStates 0 [mtFiber47StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber47StateAt 1 ∈ closeChainFiber mtWord mtFiber47DirectStates 1 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 0 [mtFiber47StateAt 0]
      (mtFiber47StateAt 0) (mtFiber47StateAt 1) (by decide) h0 (by decide)
      mtFiber47ReverseSingleStep1
  have h2 : mtFiber47StateAt 13 ∈ closeChainFiber mtWord mtFiber47DirectStates 2 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 1 [mtFiber47StateAt 0]
      (mtFiber47StateAt 1) (mtFiber47StateAt 13) (by decide) h1 (by decide)
      mtFiber47ReverseSingleStep13
  change mtFiber47StateAt 13 ∈ closeChainFiber mtWord mtFiber47DirectStates (2 + 14) [mtFiber47StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber47DirectStates 2 14 [mtFiber47StateAt 0] (mtFiber47StateAt 13) h2

theorem mtFiber47State14_in_close :
    mtFiber47StateAt 14 ∈ closeChainFiber mtWord mtFiber47DirectStates mtFiber47DirectStates.length [mtFiber47StateAt 0] := by
  have h0 : mtFiber47StateAt 0 ∈ closeChainFiber mtWord mtFiber47DirectStates 0 [mtFiber47StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber47StateAt 2 ∈ closeChainFiber mtWord mtFiber47DirectStates 1 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 0 [mtFiber47StateAt 0]
      (mtFiber47StateAt 0) (mtFiber47StateAt 2) (by decide) h0 (by decide)
      mtFiber47ReverseSingleStep2
  have h2 : mtFiber47StateAt 14 ∈ closeChainFiber mtWord mtFiber47DirectStates 2 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 1 [mtFiber47StateAt 0]
      (mtFiber47StateAt 2) (mtFiber47StateAt 14) (by decide) h1 (by decide)
      mtFiber47ReverseSingleStep14
  change mtFiber47StateAt 14 ∈ closeChainFiber mtWord mtFiber47DirectStates (2 + 14) [mtFiber47StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber47DirectStates 2 14 [mtFiber47StateAt 0] (mtFiber47StateAt 14) h2

theorem mtFiber47State15_in_close :
    mtFiber47StateAt 15 ∈ closeChainFiber mtWord mtFiber47DirectStates mtFiber47DirectStates.length [mtFiber47StateAt 0] := by
  have h0 : mtFiber47StateAt 0 ∈ closeChainFiber mtWord mtFiber47DirectStates 0 [mtFiber47StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber47StateAt 1 ∈ closeChainFiber mtWord mtFiber47DirectStates 1 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 0 [mtFiber47StateAt 0]
      (mtFiber47StateAt 0) (mtFiber47StateAt 1) (by decide) h0 (by decide)
      mtFiber47ReverseSingleStep1
  have h2 : mtFiber47StateAt 3 ∈ closeChainFiber mtWord mtFiber47DirectStates 2 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 1 [mtFiber47StateAt 0]
      (mtFiber47StateAt 1) (mtFiber47StateAt 3) (by decide) h1 (by decide)
      mtFiber47ReverseSingleStep3
  have h3 : mtFiber47StateAt 15 ∈ closeChainFiber mtWord mtFiber47DirectStates 3 [mtFiber47StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber47DirectStates 2 [mtFiber47StateAt 0]
      (mtFiber47StateAt 3) (mtFiber47StateAt 15) (by decide) h2 (by decide)
      mtFiber47ReverseSingleStep15
  change mtFiber47StateAt 15 ∈ closeChainFiber mtWord mtFiber47DirectStates (3 + 13) [mtFiber47StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber47DirectStates 3 13 [mtFiber47StateAt 0] (mtFiber47StateAt 15) h3

theorem mtFiber47DirectConnected :
    chainFiberConnected mtWord mtFiber47DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber47DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber47State0_in_close
  · subst state
    exact mtFiber47State1_in_close
  · subst state
    exact mtFiber47State2_in_close
  · subst state
    exact mtFiber47State3_in_close
  · subst state
    exact mtFiber47State4_in_close
  · subst state
    exact mtFiber47State5_in_close
  · subst state
    exact mtFiber47State6_in_close
  · subst state
    exact mtFiber47State7_in_close
  · subst state
    exact mtFiber47State8_in_close
  · subst state
    exact mtFiber47State9_in_close
  · subst state
    exact mtFiber47State10_in_close
  · subst state
    exact mtFiber47State11_in_close
  · subst state
    exact mtFiber47State12_in_close
  · subst state
    exact mtFiber47State13_in_close
  · subst state
    exact mtFiber47State14_in_close
  · subst state
    exact mtFiber47State15_in_close
  · cases h
def mtFiber49StateAt (i : Nat) : List TauState :=
  directStates (mtFiber49RowAt i).sourceLeft (mtFiber49RowAt i).sourceRight

def mtFiber49DirectStates : List (List TauState) :=
  [mtFiber49StateAt 0, mtFiber49StateAt 1, mtFiber49StateAt 2, mtFiber49StateAt 3, mtFiber49StateAt 4, mtFiber49StateAt 5, mtFiber49StateAt 6, mtFiber49StateAt 7, mtFiber49StateAt 8, mtFiber49StateAt 9, mtFiber49StateAt 10, mtFiber49StateAt 11, mtFiber49StateAt 12, mtFiber49StateAt 13, mtFiber49StateAt 14, mtFiber49StateAt 15]

theorem mtFiber49ReverseRow_1_ok :
    mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber49Chunk0_ok
  change (mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 0) &&
    mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber49ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber49StateAt 0) (mtFiber49StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber49StateAt 0) (mtFiber49StateAt 1)
    (mtFiber49RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber49Key mtFiber49Expected
        (mtFiber49RowAt 1) (by decide) mtFiber49ReverseRow_1_ok
      simpa [mtFiber49StateAt, mtFiber49RowAt, mtFiber49Rows, listGetD, directRow] using h)

theorem mtFiber49ReverseRow_2_ok :
    mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber49Chunk1_ok
  change (mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 2) &&
    mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber49ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber49StateAt 0) (mtFiber49StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber49StateAt 0) (mtFiber49StateAt 2)
    (mtFiber49RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber49Key mtFiber49Expected
        (mtFiber49RowAt 2) (by decide) mtFiber49ReverseRow_2_ok
      simpa [mtFiber49StateAt, mtFiber49RowAt, mtFiber49Rows, listGetD, directRow] using h)

theorem mtFiber49ReverseRow_3_ok :
    mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber49Chunk1_ok
  change (mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 2) &&
    mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber49ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber49StateAt 1) (mtFiber49StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber49StateAt 1) (mtFiber49StateAt 3)
    (mtFiber49RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber49Key mtFiber49Expected
        (mtFiber49RowAt 3) (by decide) mtFiber49ReverseRow_3_ok
      simpa [mtFiber49StateAt, mtFiber49RowAt, mtFiber49Rows, listGetD, directRow] using h)

theorem mtFiber49ReverseRow_4_ok :
    mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber49Chunk2_ok
  change (mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 4) &&
    mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber49ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber49StateAt 0) (mtFiber49StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber49StateAt 0) (mtFiber49StateAt 4)
    (mtFiber49RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber49Key mtFiber49Expected
        (mtFiber49RowAt 4) (by decide) mtFiber49ReverseRow_4_ok
      simpa [mtFiber49StateAt, mtFiber49RowAt, mtFiber49Rows, listGetD, directRow] using h)

theorem mtFiber49ReverseRow_5_ok :
    mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber49Chunk2_ok
  change (mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 4) &&
    mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber49ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber49StateAt 1) (mtFiber49StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber49StateAt 1) (mtFiber49StateAt 5)
    (mtFiber49RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber49Key mtFiber49Expected
        (mtFiber49RowAt 5) (by decide) mtFiber49ReverseRow_5_ok
      simpa [mtFiber49StateAt, mtFiber49RowAt, mtFiber49Rows, listGetD, directRow] using h)

theorem mtFiber49ReverseRow_6_ok :
    mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber49Chunk3_ok
  change (mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 6) &&
    mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber49ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber49StateAt 2) (mtFiber49StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber49StateAt 2) (mtFiber49StateAt 6)
    (mtFiber49RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber49Key mtFiber49Expected
        (mtFiber49RowAt 6) (by decide) mtFiber49ReverseRow_6_ok
      simpa [mtFiber49StateAt, mtFiber49RowAt, mtFiber49Rows, listGetD, directRow] using h)

theorem mtFiber49ReverseRow_7_ok :
    mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber49Chunk3_ok
  change (mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 6) &&
    mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber49ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber49StateAt 3) (mtFiber49StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber49StateAt 3) (mtFiber49StateAt 7)
    (mtFiber49RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber49Key mtFiber49Expected
        (mtFiber49RowAt 7) (by decide) mtFiber49ReverseRow_7_ok
      simpa [mtFiber49StateAt, mtFiber49RowAt, mtFiber49Rows, listGetD, directRow] using h)

theorem mtFiber49ReverseRow_8_ok :
    mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber49Chunk4_ok
  change (mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 8) &&
    mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber49ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber49StateAt 4) (mtFiber49StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber49StateAt 4) (mtFiber49StateAt 8)
    (mtFiber49RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber49Key mtFiber49Expected
        (mtFiber49RowAt 8) (by decide) mtFiber49ReverseRow_8_ok
      simpa [mtFiber49StateAt, mtFiber49RowAt, mtFiber49Rows, listGetD, directRow] using h)

theorem mtFiber49ReverseRow_9_ok :
    mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber49Chunk4_ok
  change (mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 8) &&
    mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber49ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber49StateAt 5) (mtFiber49StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber49StateAt 5) (mtFiber49StateAt 9)
    (mtFiber49RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber49Key mtFiber49Expected
        (mtFiber49RowAt 9) (by decide) mtFiber49ReverseRow_9_ok
      simpa [mtFiber49StateAt, mtFiber49RowAt, mtFiber49Rows, listGetD, directRow] using h)

theorem mtFiber49ReverseRow_10_ok :
    mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber49Chunk5_ok
  change (mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 10) &&
    mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber49ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber49StateAt 6) (mtFiber49StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber49StateAt 6) (mtFiber49StateAt 10)
    (mtFiber49RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber49Key mtFiber49Expected
        (mtFiber49RowAt 10) (by decide) mtFiber49ReverseRow_10_ok
      simpa [mtFiber49StateAt, mtFiber49RowAt, mtFiber49Rows, listGetD, directRow] using h)

theorem mtFiber49ReverseRow_11_ok :
    mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber49Chunk5_ok
  change (mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 10) &&
    mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber49ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber49StateAt 7) (mtFiber49StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber49StateAt 7) (mtFiber49StateAt 11)
    (mtFiber49RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber49Key mtFiber49Expected
        (mtFiber49RowAt 11) (by decide) mtFiber49ReverseRow_11_ok
      simpa [mtFiber49StateAt, mtFiber49RowAt, mtFiber49Rows, listGetD, directRow] using h)

theorem mtFiber49ReverseRow_12_ok :
    mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber49Chunk6_ok
  change (mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 12) &&
    mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber49ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber49StateAt 0) (mtFiber49StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber49StateAt 0) (mtFiber49StateAt 12)
    (mtFiber49RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber49Key mtFiber49Expected
        (mtFiber49RowAt 12) (by decide) mtFiber49ReverseRow_12_ok
      simpa [mtFiber49StateAt, mtFiber49RowAt, mtFiber49Rows, listGetD, directRow] using h)

theorem mtFiber49ReverseRow_13_ok :
    mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber49Chunk6_ok
  change (mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 12) &&
    mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber49ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber49StateAt 1) (mtFiber49StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber49StateAt 1) (mtFiber49StateAt 13)
    (mtFiber49RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber49Key mtFiber49Expected
        (mtFiber49RowAt 13) (by decide) mtFiber49ReverseRow_13_ok
      simpa [mtFiber49StateAt, mtFiber49RowAt, mtFiber49Rows, listGetD, directRow] using h)

theorem mtFiber49ReverseRow_14_ok :
    mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber49Chunk7_ok
  change (mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 14) &&
    mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber49ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber49StateAt 2) (mtFiber49StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber49StateAt 2) (mtFiber49StateAt 14)
    (mtFiber49RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber49Key mtFiber49Expected
        (mtFiber49RowAt 14) (by decide) mtFiber49ReverseRow_14_ok
      simpa [mtFiber49StateAt, mtFiber49RowAt, mtFiber49Rows, listGetD, directRow] using h)

theorem mtFiber49ReverseRow_15_ok :
    mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber49Chunk7_ok
  change (mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 14) &&
    mtRowReverseValid mtFiber49Key mtFiber49Expected (mtFiber49RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber49ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber49StateAt 3) (mtFiber49StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber49StateAt 3) (mtFiber49StateAt 15)
    (mtFiber49RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber49Key mtFiber49Expected
        (mtFiber49RowAt 15) (by decide) mtFiber49ReverseRow_15_ok
      simpa [mtFiber49StateAt, mtFiber49RowAt, mtFiber49Rows, listGetD, directRow] using h)

theorem mtFiber49State0_in_close :
    mtFiber49StateAt 0 ∈ closeChainFiber mtWord mtFiber49DirectStates mtFiber49DirectStates.length [mtFiber49StateAt 0] := by
  change mtFiber49StateAt 0 ∈ closeChainFiber mtWord mtFiber49DirectStates 16 [mtFiber49StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber49DirectStates 0 16 [mtFiber49StateAt 0] (mtFiber49StateAt 0) (by simp [closeChainFiber])

theorem mtFiber49State1_in_close :
    mtFiber49StateAt 1 ∈ closeChainFiber mtWord mtFiber49DirectStates mtFiber49DirectStates.length [mtFiber49StateAt 0] := by
  have h0 : mtFiber49StateAt 0 ∈ closeChainFiber mtWord mtFiber49DirectStates 0 [mtFiber49StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber49StateAt 1 ∈ closeChainFiber mtWord mtFiber49DirectStates 1 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 0 [mtFiber49StateAt 0]
      (mtFiber49StateAt 0) (mtFiber49StateAt 1) (by decide) h0 (by decide)
      mtFiber49ReverseSingleStep1
  change mtFiber49StateAt 1 ∈ closeChainFiber mtWord mtFiber49DirectStates (1 + 15) [mtFiber49StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber49DirectStates 1 15 [mtFiber49StateAt 0] (mtFiber49StateAt 1) h1

theorem mtFiber49State2_in_close :
    mtFiber49StateAt 2 ∈ closeChainFiber mtWord mtFiber49DirectStates mtFiber49DirectStates.length [mtFiber49StateAt 0] := by
  have h0 : mtFiber49StateAt 0 ∈ closeChainFiber mtWord mtFiber49DirectStates 0 [mtFiber49StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber49StateAt 2 ∈ closeChainFiber mtWord mtFiber49DirectStates 1 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 0 [mtFiber49StateAt 0]
      (mtFiber49StateAt 0) (mtFiber49StateAt 2) (by decide) h0 (by decide)
      mtFiber49ReverseSingleStep2
  change mtFiber49StateAt 2 ∈ closeChainFiber mtWord mtFiber49DirectStates (1 + 15) [mtFiber49StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber49DirectStates 1 15 [mtFiber49StateAt 0] (mtFiber49StateAt 2) h1

theorem mtFiber49State3_in_close :
    mtFiber49StateAt 3 ∈ closeChainFiber mtWord mtFiber49DirectStates mtFiber49DirectStates.length [mtFiber49StateAt 0] := by
  have h0 : mtFiber49StateAt 0 ∈ closeChainFiber mtWord mtFiber49DirectStates 0 [mtFiber49StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber49StateAt 1 ∈ closeChainFiber mtWord mtFiber49DirectStates 1 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 0 [mtFiber49StateAt 0]
      (mtFiber49StateAt 0) (mtFiber49StateAt 1) (by decide) h0 (by decide)
      mtFiber49ReverseSingleStep1
  have h2 : mtFiber49StateAt 3 ∈ closeChainFiber mtWord mtFiber49DirectStates 2 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 1 [mtFiber49StateAt 0]
      (mtFiber49StateAt 1) (mtFiber49StateAt 3) (by decide) h1 (by decide)
      mtFiber49ReverseSingleStep3
  change mtFiber49StateAt 3 ∈ closeChainFiber mtWord mtFiber49DirectStates (2 + 14) [mtFiber49StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber49DirectStates 2 14 [mtFiber49StateAt 0] (mtFiber49StateAt 3) h2

theorem mtFiber49State4_in_close :
    mtFiber49StateAt 4 ∈ closeChainFiber mtWord mtFiber49DirectStates mtFiber49DirectStates.length [mtFiber49StateAt 0] := by
  have h0 : mtFiber49StateAt 0 ∈ closeChainFiber mtWord mtFiber49DirectStates 0 [mtFiber49StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber49StateAt 4 ∈ closeChainFiber mtWord mtFiber49DirectStates 1 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 0 [mtFiber49StateAt 0]
      (mtFiber49StateAt 0) (mtFiber49StateAt 4) (by decide) h0 (by decide)
      mtFiber49ReverseSingleStep4
  change mtFiber49StateAt 4 ∈ closeChainFiber mtWord mtFiber49DirectStates (1 + 15) [mtFiber49StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber49DirectStates 1 15 [mtFiber49StateAt 0] (mtFiber49StateAt 4) h1

theorem mtFiber49State5_in_close :
    mtFiber49StateAt 5 ∈ closeChainFiber mtWord mtFiber49DirectStates mtFiber49DirectStates.length [mtFiber49StateAt 0] := by
  have h0 : mtFiber49StateAt 0 ∈ closeChainFiber mtWord mtFiber49DirectStates 0 [mtFiber49StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber49StateAt 1 ∈ closeChainFiber mtWord mtFiber49DirectStates 1 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 0 [mtFiber49StateAt 0]
      (mtFiber49StateAt 0) (mtFiber49StateAt 1) (by decide) h0 (by decide)
      mtFiber49ReverseSingleStep1
  have h2 : mtFiber49StateAt 5 ∈ closeChainFiber mtWord mtFiber49DirectStates 2 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 1 [mtFiber49StateAt 0]
      (mtFiber49StateAt 1) (mtFiber49StateAt 5) (by decide) h1 (by decide)
      mtFiber49ReverseSingleStep5
  change mtFiber49StateAt 5 ∈ closeChainFiber mtWord mtFiber49DirectStates (2 + 14) [mtFiber49StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber49DirectStates 2 14 [mtFiber49StateAt 0] (mtFiber49StateAt 5) h2

theorem mtFiber49State6_in_close :
    mtFiber49StateAt 6 ∈ closeChainFiber mtWord mtFiber49DirectStates mtFiber49DirectStates.length [mtFiber49StateAt 0] := by
  have h0 : mtFiber49StateAt 0 ∈ closeChainFiber mtWord mtFiber49DirectStates 0 [mtFiber49StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber49StateAt 2 ∈ closeChainFiber mtWord mtFiber49DirectStates 1 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 0 [mtFiber49StateAt 0]
      (mtFiber49StateAt 0) (mtFiber49StateAt 2) (by decide) h0 (by decide)
      mtFiber49ReverseSingleStep2
  have h2 : mtFiber49StateAt 6 ∈ closeChainFiber mtWord mtFiber49DirectStates 2 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 1 [mtFiber49StateAt 0]
      (mtFiber49StateAt 2) (mtFiber49StateAt 6) (by decide) h1 (by decide)
      mtFiber49ReverseSingleStep6
  change mtFiber49StateAt 6 ∈ closeChainFiber mtWord mtFiber49DirectStates (2 + 14) [mtFiber49StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber49DirectStates 2 14 [mtFiber49StateAt 0] (mtFiber49StateAt 6) h2

theorem mtFiber49State7_in_close :
    mtFiber49StateAt 7 ∈ closeChainFiber mtWord mtFiber49DirectStates mtFiber49DirectStates.length [mtFiber49StateAt 0] := by
  have h0 : mtFiber49StateAt 0 ∈ closeChainFiber mtWord mtFiber49DirectStates 0 [mtFiber49StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber49StateAt 1 ∈ closeChainFiber mtWord mtFiber49DirectStates 1 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 0 [mtFiber49StateAt 0]
      (mtFiber49StateAt 0) (mtFiber49StateAt 1) (by decide) h0 (by decide)
      mtFiber49ReverseSingleStep1
  have h2 : mtFiber49StateAt 3 ∈ closeChainFiber mtWord mtFiber49DirectStates 2 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 1 [mtFiber49StateAt 0]
      (mtFiber49StateAt 1) (mtFiber49StateAt 3) (by decide) h1 (by decide)
      mtFiber49ReverseSingleStep3
  have h3 : mtFiber49StateAt 7 ∈ closeChainFiber mtWord mtFiber49DirectStates 3 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 2 [mtFiber49StateAt 0]
      (mtFiber49StateAt 3) (mtFiber49StateAt 7) (by decide) h2 (by decide)
      mtFiber49ReverseSingleStep7
  change mtFiber49StateAt 7 ∈ closeChainFiber mtWord mtFiber49DirectStates (3 + 13) [mtFiber49StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber49DirectStates 3 13 [mtFiber49StateAt 0] (mtFiber49StateAt 7) h3

theorem mtFiber49State8_in_close :
    mtFiber49StateAt 8 ∈ closeChainFiber mtWord mtFiber49DirectStates mtFiber49DirectStates.length [mtFiber49StateAt 0] := by
  have h0 : mtFiber49StateAt 0 ∈ closeChainFiber mtWord mtFiber49DirectStates 0 [mtFiber49StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber49StateAt 4 ∈ closeChainFiber mtWord mtFiber49DirectStates 1 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 0 [mtFiber49StateAt 0]
      (mtFiber49StateAt 0) (mtFiber49StateAt 4) (by decide) h0 (by decide)
      mtFiber49ReverseSingleStep4
  have h2 : mtFiber49StateAt 8 ∈ closeChainFiber mtWord mtFiber49DirectStates 2 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 1 [mtFiber49StateAt 0]
      (mtFiber49StateAt 4) (mtFiber49StateAt 8) (by decide) h1 (by decide)
      mtFiber49ReverseSingleStep8
  change mtFiber49StateAt 8 ∈ closeChainFiber mtWord mtFiber49DirectStates (2 + 14) [mtFiber49StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber49DirectStates 2 14 [mtFiber49StateAt 0] (mtFiber49StateAt 8) h2

theorem mtFiber49State9_in_close :
    mtFiber49StateAt 9 ∈ closeChainFiber mtWord mtFiber49DirectStates mtFiber49DirectStates.length [mtFiber49StateAt 0] := by
  have h0 : mtFiber49StateAt 0 ∈ closeChainFiber mtWord mtFiber49DirectStates 0 [mtFiber49StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber49StateAt 1 ∈ closeChainFiber mtWord mtFiber49DirectStates 1 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 0 [mtFiber49StateAt 0]
      (mtFiber49StateAt 0) (mtFiber49StateAt 1) (by decide) h0 (by decide)
      mtFiber49ReverseSingleStep1
  have h2 : mtFiber49StateAt 5 ∈ closeChainFiber mtWord mtFiber49DirectStates 2 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 1 [mtFiber49StateAt 0]
      (mtFiber49StateAt 1) (mtFiber49StateAt 5) (by decide) h1 (by decide)
      mtFiber49ReverseSingleStep5
  have h3 : mtFiber49StateAt 9 ∈ closeChainFiber mtWord mtFiber49DirectStates 3 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 2 [mtFiber49StateAt 0]
      (mtFiber49StateAt 5) (mtFiber49StateAt 9) (by decide) h2 (by decide)
      mtFiber49ReverseSingleStep9
  change mtFiber49StateAt 9 ∈ closeChainFiber mtWord mtFiber49DirectStates (3 + 13) [mtFiber49StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber49DirectStates 3 13 [mtFiber49StateAt 0] (mtFiber49StateAt 9) h3

theorem mtFiber49State10_in_close :
    mtFiber49StateAt 10 ∈ closeChainFiber mtWord mtFiber49DirectStates mtFiber49DirectStates.length [mtFiber49StateAt 0] := by
  have h0 : mtFiber49StateAt 0 ∈ closeChainFiber mtWord mtFiber49DirectStates 0 [mtFiber49StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber49StateAt 2 ∈ closeChainFiber mtWord mtFiber49DirectStates 1 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 0 [mtFiber49StateAt 0]
      (mtFiber49StateAt 0) (mtFiber49StateAt 2) (by decide) h0 (by decide)
      mtFiber49ReverseSingleStep2
  have h2 : mtFiber49StateAt 6 ∈ closeChainFiber mtWord mtFiber49DirectStates 2 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 1 [mtFiber49StateAt 0]
      (mtFiber49StateAt 2) (mtFiber49StateAt 6) (by decide) h1 (by decide)
      mtFiber49ReverseSingleStep6
  have h3 : mtFiber49StateAt 10 ∈ closeChainFiber mtWord mtFiber49DirectStates 3 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 2 [mtFiber49StateAt 0]
      (mtFiber49StateAt 6) (mtFiber49StateAt 10) (by decide) h2 (by decide)
      mtFiber49ReverseSingleStep10
  change mtFiber49StateAt 10 ∈ closeChainFiber mtWord mtFiber49DirectStates (3 + 13) [mtFiber49StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber49DirectStates 3 13 [mtFiber49StateAt 0] (mtFiber49StateAt 10) h3

theorem mtFiber49State11_in_close :
    mtFiber49StateAt 11 ∈ closeChainFiber mtWord mtFiber49DirectStates mtFiber49DirectStates.length [mtFiber49StateAt 0] := by
  have h0 : mtFiber49StateAt 0 ∈ closeChainFiber mtWord mtFiber49DirectStates 0 [mtFiber49StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber49StateAt 1 ∈ closeChainFiber mtWord mtFiber49DirectStates 1 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 0 [mtFiber49StateAt 0]
      (mtFiber49StateAt 0) (mtFiber49StateAt 1) (by decide) h0 (by decide)
      mtFiber49ReverseSingleStep1
  have h2 : mtFiber49StateAt 3 ∈ closeChainFiber mtWord mtFiber49DirectStates 2 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 1 [mtFiber49StateAt 0]
      (mtFiber49StateAt 1) (mtFiber49StateAt 3) (by decide) h1 (by decide)
      mtFiber49ReverseSingleStep3
  have h3 : mtFiber49StateAt 7 ∈ closeChainFiber mtWord mtFiber49DirectStates 3 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 2 [mtFiber49StateAt 0]
      (mtFiber49StateAt 3) (mtFiber49StateAt 7) (by decide) h2 (by decide)
      mtFiber49ReverseSingleStep7
  have h4 : mtFiber49StateAt 11 ∈ closeChainFiber mtWord mtFiber49DirectStates 4 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 3 [mtFiber49StateAt 0]
      (mtFiber49StateAt 7) (mtFiber49StateAt 11) (by decide) h3 (by decide)
      mtFiber49ReverseSingleStep11
  change mtFiber49StateAt 11 ∈ closeChainFiber mtWord mtFiber49DirectStates (4 + 12) [mtFiber49StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber49DirectStates 4 12 [mtFiber49StateAt 0] (mtFiber49StateAt 11) h4

theorem mtFiber49State12_in_close :
    mtFiber49StateAt 12 ∈ closeChainFiber mtWord mtFiber49DirectStates mtFiber49DirectStates.length [mtFiber49StateAt 0] := by
  have h0 : mtFiber49StateAt 0 ∈ closeChainFiber mtWord mtFiber49DirectStates 0 [mtFiber49StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber49StateAt 12 ∈ closeChainFiber mtWord mtFiber49DirectStates 1 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 0 [mtFiber49StateAt 0]
      (mtFiber49StateAt 0) (mtFiber49StateAt 12) (by decide) h0 (by decide)
      mtFiber49ReverseSingleStep12
  change mtFiber49StateAt 12 ∈ closeChainFiber mtWord mtFiber49DirectStates (1 + 15) [mtFiber49StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber49DirectStates 1 15 [mtFiber49StateAt 0] (mtFiber49StateAt 12) h1

theorem mtFiber49State13_in_close :
    mtFiber49StateAt 13 ∈ closeChainFiber mtWord mtFiber49DirectStates mtFiber49DirectStates.length [mtFiber49StateAt 0] := by
  have h0 : mtFiber49StateAt 0 ∈ closeChainFiber mtWord mtFiber49DirectStates 0 [mtFiber49StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber49StateAt 1 ∈ closeChainFiber mtWord mtFiber49DirectStates 1 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 0 [mtFiber49StateAt 0]
      (mtFiber49StateAt 0) (mtFiber49StateAt 1) (by decide) h0 (by decide)
      mtFiber49ReverseSingleStep1
  have h2 : mtFiber49StateAt 13 ∈ closeChainFiber mtWord mtFiber49DirectStates 2 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 1 [mtFiber49StateAt 0]
      (mtFiber49StateAt 1) (mtFiber49StateAt 13) (by decide) h1 (by decide)
      mtFiber49ReverseSingleStep13
  change mtFiber49StateAt 13 ∈ closeChainFiber mtWord mtFiber49DirectStates (2 + 14) [mtFiber49StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber49DirectStates 2 14 [mtFiber49StateAt 0] (mtFiber49StateAt 13) h2

theorem mtFiber49State14_in_close :
    mtFiber49StateAt 14 ∈ closeChainFiber mtWord mtFiber49DirectStates mtFiber49DirectStates.length [mtFiber49StateAt 0] := by
  have h0 : mtFiber49StateAt 0 ∈ closeChainFiber mtWord mtFiber49DirectStates 0 [mtFiber49StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber49StateAt 2 ∈ closeChainFiber mtWord mtFiber49DirectStates 1 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 0 [mtFiber49StateAt 0]
      (mtFiber49StateAt 0) (mtFiber49StateAt 2) (by decide) h0 (by decide)
      mtFiber49ReverseSingleStep2
  have h2 : mtFiber49StateAt 14 ∈ closeChainFiber mtWord mtFiber49DirectStates 2 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 1 [mtFiber49StateAt 0]
      (mtFiber49StateAt 2) (mtFiber49StateAt 14) (by decide) h1 (by decide)
      mtFiber49ReverseSingleStep14
  change mtFiber49StateAt 14 ∈ closeChainFiber mtWord mtFiber49DirectStates (2 + 14) [mtFiber49StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber49DirectStates 2 14 [mtFiber49StateAt 0] (mtFiber49StateAt 14) h2

theorem mtFiber49State15_in_close :
    mtFiber49StateAt 15 ∈ closeChainFiber mtWord mtFiber49DirectStates mtFiber49DirectStates.length [mtFiber49StateAt 0] := by
  have h0 : mtFiber49StateAt 0 ∈ closeChainFiber mtWord mtFiber49DirectStates 0 [mtFiber49StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber49StateAt 1 ∈ closeChainFiber mtWord mtFiber49DirectStates 1 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 0 [mtFiber49StateAt 0]
      (mtFiber49StateAt 0) (mtFiber49StateAt 1) (by decide) h0 (by decide)
      mtFiber49ReverseSingleStep1
  have h2 : mtFiber49StateAt 3 ∈ closeChainFiber mtWord mtFiber49DirectStates 2 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 1 [mtFiber49StateAt 0]
      (mtFiber49StateAt 1) (mtFiber49StateAt 3) (by decide) h1 (by decide)
      mtFiber49ReverseSingleStep3
  have h3 : mtFiber49StateAt 15 ∈ closeChainFiber mtWord mtFiber49DirectStates 3 [mtFiber49StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber49DirectStates 2 [mtFiber49StateAt 0]
      (mtFiber49StateAt 3) (mtFiber49StateAt 15) (by decide) h2 (by decide)
      mtFiber49ReverseSingleStep15
  change mtFiber49StateAt 15 ∈ closeChainFiber mtWord mtFiber49DirectStates (3 + 13) [mtFiber49StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber49DirectStates 3 13 [mtFiber49StateAt 0] (mtFiber49StateAt 15) h3

theorem mtFiber49DirectConnected :
    chainFiberConnected mtWord mtFiber49DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber49DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber49State0_in_close
  · subst state
    exact mtFiber49State1_in_close
  · subst state
    exact mtFiber49State2_in_close
  · subst state
    exact mtFiber49State3_in_close
  · subst state
    exact mtFiber49State4_in_close
  · subst state
    exact mtFiber49State5_in_close
  · subst state
    exact mtFiber49State6_in_close
  · subst state
    exact mtFiber49State7_in_close
  · subst state
    exact mtFiber49State8_in_close
  · subst state
    exact mtFiber49State9_in_close
  · subst state
    exact mtFiber49State10_in_close
  · subst state
    exact mtFiber49State11_in_close
  · subst state
    exact mtFiber49State12_in_close
  · subst state
    exact mtFiber49State13_in_close
  · subst state
    exact mtFiber49State14_in_close
  · subst state
    exact mtFiber49State15_in_close
  · cases h
end GoertzelLemma818LengthTwoMTBridge

end Mettapedia.GraphTheory.FourColor
