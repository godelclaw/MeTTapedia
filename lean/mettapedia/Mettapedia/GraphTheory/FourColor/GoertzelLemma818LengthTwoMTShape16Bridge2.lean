import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for size-16 `mirror,normal` length-two fibers, group 2

This module proves direct connectedness for generated `mirror,normal` size-16 fibers from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMTBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorTauCertificate
open GoertzelLemma818MirrorTauReverseAudit

def mtFiber31StateAt (i : Nat) : List TauState :=
  directStates (mtFiber31RowAt i).sourceLeft (mtFiber31RowAt i).sourceRight

def mtFiber31DirectStates : List (List TauState) :=
  [mtFiber31StateAt 0, mtFiber31StateAt 1, mtFiber31StateAt 2, mtFiber31StateAt 3, mtFiber31StateAt 4, mtFiber31StateAt 5, mtFiber31StateAt 6, mtFiber31StateAt 7, mtFiber31StateAt 8, mtFiber31StateAt 9, mtFiber31StateAt 10, mtFiber31StateAt 11, mtFiber31StateAt 12, mtFiber31StateAt 13, mtFiber31StateAt 14, mtFiber31StateAt 15]

theorem mtFiber31ReverseRow_1_ok :
    mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber31Chunk0_ok
  change (mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 0) &&
    mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber31ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber31StateAt 0) (mtFiber31StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber31StateAt 0) (mtFiber31StateAt 1)
    (mtFiber31RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber31Key mtFiber31Expected
        (mtFiber31RowAt 1) (by decide) mtFiber31ReverseRow_1_ok
      simpa [mtFiber31StateAt, mtFiber31RowAt, mtFiber31Rows, listGetD, directRow] using h)

theorem mtFiber31ReverseRow_2_ok :
    mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber31Chunk1_ok
  change (mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 2) &&
    mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber31ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber31StateAt 0) (mtFiber31StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber31StateAt 0) (mtFiber31StateAt 2)
    (mtFiber31RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber31Key mtFiber31Expected
        (mtFiber31RowAt 2) (by decide) mtFiber31ReverseRow_2_ok
      simpa [mtFiber31StateAt, mtFiber31RowAt, mtFiber31Rows, listGetD, directRow] using h)

theorem mtFiber31ReverseRow_3_ok :
    mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber31Chunk1_ok
  change (mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 2) &&
    mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber31ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber31StateAt 1) (mtFiber31StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber31StateAt 1) (mtFiber31StateAt 3)
    (mtFiber31RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber31Key mtFiber31Expected
        (mtFiber31RowAt 3) (by decide) mtFiber31ReverseRow_3_ok
      simpa [mtFiber31StateAt, mtFiber31RowAt, mtFiber31Rows, listGetD, directRow] using h)

theorem mtFiber31ReverseRow_4_ok :
    mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber31Chunk2_ok
  change (mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 4) &&
    mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber31ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber31StateAt 0) (mtFiber31StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber31StateAt 0) (mtFiber31StateAt 4)
    (mtFiber31RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber31Key mtFiber31Expected
        (mtFiber31RowAt 4) (by decide) mtFiber31ReverseRow_4_ok
      simpa [mtFiber31StateAt, mtFiber31RowAt, mtFiber31Rows, listGetD, directRow] using h)

theorem mtFiber31ReverseRow_5_ok :
    mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber31Chunk2_ok
  change (mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 4) &&
    mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber31ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber31StateAt 1) (mtFiber31StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber31StateAt 1) (mtFiber31StateAt 5)
    (mtFiber31RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber31Key mtFiber31Expected
        (mtFiber31RowAt 5) (by decide) mtFiber31ReverseRow_5_ok
      simpa [mtFiber31StateAt, mtFiber31RowAt, mtFiber31Rows, listGetD, directRow] using h)

theorem mtFiber31ReverseRow_6_ok :
    mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber31Chunk3_ok
  change (mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 6) &&
    mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber31ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber31StateAt 2) (mtFiber31StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber31StateAt 2) (mtFiber31StateAt 6)
    (mtFiber31RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber31Key mtFiber31Expected
        (mtFiber31RowAt 6) (by decide) mtFiber31ReverseRow_6_ok
      simpa [mtFiber31StateAt, mtFiber31RowAt, mtFiber31Rows, listGetD, directRow] using h)

theorem mtFiber31ReverseRow_7_ok :
    mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber31Chunk3_ok
  change (mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 6) &&
    mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber31ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber31StateAt 3) (mtFiber31StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber31StateAt 3) (mtFiber31StateAt 7)
    (mtFiber31RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber31Key mtFiber31Expected
        (mtFiber31RowAt 7) (by decide) mtFiber31ReverseRow_7_ok
      simpa [mtFiber31StateAt, mtFiber31RowAt, mtFiber31Rows, listGetD, directRow] using h)

theorem mtFiber31ReverseRow_8_ok :
    mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber31Chunk4_ok
  change (mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 8) &&
    mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber31ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber31StateAt 4) (mtFiber31StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber31StateAt 4) (mtFiber31StateAt 8)
    (mtFiber31RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber31Key mtFiber31Expected
        (mtFiber31RowAt 8) (by decide) mtFiber31ReverseRow_8_ok
      simpa [mtFiber31StateAt, mtFiber31RowAt, mtFiber31Rows, listGetD, directRow] using h)

theorem mtFiber31ReverseRow_9_ok :
    mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber31Chunk4_ok
  change (mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 8) &&
    mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber31ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber31StateAt 5) (mtFiber31StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber31StateAt 5) (mtFiber31StateAt 9)
    (mtFiber31RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber31Key mtFiber31Expected
        (mtFiber31RowAt 9) (by decide) mtFiber31ReverseRow_9_ok
      simpa [mtFiber31StateAt, mtFiber31RowAt, mtFiber31Rows, listGetD, directRow] using h)

theorem mtFiber31ReverseRow_10_ok :
    mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber31Chunk5_ok
  change (mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 10) &&
    mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber31ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber31StateAt 6) (mtFiber31StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber31StateAt 6) (mtFiber31StateAt 10)
    (mtFiber31RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber31Key mtFiber31Expected
        (mtFiber31RowAt 10) (by decide) mtFiber31ReverseRow_10_ok
      simpa [mtFiber31StateAt, mtFiber31RowAt, mtFiber31Rows, listGetD, directRow] using h)

theorem mtFiber31ReverseRow_11_ok :
    mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber31Chunk5_ok
  change (mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 10) &&
    mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber31ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber31StateAt 7) (mtFiber31StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber31StateAt 7) (mtFiber31StateAt 11)
    (mtFiber31RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber31Key mtFiber31Expected
        (mtFiber31RowAt 11) (by decide) mtFiber31ReverseRow_11_ok
      simpa [mtFiber31StateAt, mtFiber31RowAt, mtFiber31Rows, listGetD, directRow] using h)

theorem mtFiber31ReverseRow_12_ok :
    mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber31Chunk6_ok
  change (mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 12) &&
    mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber31ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber31StateAt 0) (mtFiber31StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber31StateAt 0) (mtFiber31StateAt 12)
    (mtFiber31RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber31Key mtFiber31Expected
        (mtFiber31RowAt 12) (by decide) mtFiber31ReverseRow_12_ok
      simpa [mtFiber31StateAt, mtFiber31RowAt, mtFiber31Rows, listGetD, directRow] using h)

theorem mtFiber31ReverseRow_13_ok :
    mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber31Chunk6_ok
  change (mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 12) &&
    mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber31ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber31StateAt 1) (mtFiber31StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber31StateAt 1) (mtFiber31StateAt 13)
    (mtFiber31RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber31Key mtFiber31Expected
        (mtFiber31RowAt 13) (by decide) mtFiber31ReverseRow_13_ok
      simpa [mtFiber31StateAt, mtFiber31RowAt, mtFiber31Rows, listGetD, directRow] using h)

theorem mtFiber31ReverseRow_14_ok :
    mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber31Chunk7_ok
  change (mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 14) &&
    mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber31ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber31StateAt 2) (mtFiber31StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber31StateAt 2) (mtFiber31StateAt 14)
    (mtFiber31RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber31Key mtFiber31Expected
        (mtFiber31RowAt 14) (by decide) mtFiber31ReverseRow_14_ok
      simpa [mtFiber31StateAt, mtFiber31RowAt, mtFiber31Rows, listGetD, directRow] using h)

theorem mtFiber31ReverseRow_15_ok :
    mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber31Chunk7_ok
  change (mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 14) &&
    mtRowReverseValid mtFiber31Key mtFiber31Expected (mtFiber31RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber31ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber31StateAt 3) (mtFiber31StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber31StateAt 3) (mtFiber31StateAt 15)
    (mtFiber31RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber31Key mtFiber31Expected
        (mtFiber31RowAt 15) (by decide) mtFiber31ReverseRow_15_ok
      simpa [mtFiber31StateAt, mtFiber31RowAt, mtFiber31Rows, listGetD, directRow] using h)

theorem mtFiber31State0_in_close :
    mtFiber31StateAt 0 ∈ closeChainFiber mtWord mtFiber31DirectStates mtFiber31DirectStates.length [mtFiber31StateAt 0] := by
  change mtFiber31StateAt 0 ∈ closeChainFiber mtWord mtFiber31DirectStates 16 [mtFiber31StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber31DirectStates 0 16 [mtFiber31StateAt 0] (mtFiber31StateAt 0) (by simp [closeChainFiber])

theorem mtFiber31State1_in_close :
    mtFiber31StateAt 1 ∈ closeChainFiber mtWord mtFiber31DirectStates mtFiber31DirectStates.length [mtFiber31StateAt 0] := by
  have h0 : mtFiber31StateAt 0 ∈ closeChainFiber mtWord mtFiber31DirectStates 0 [mtFiber31StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber31StateAt 1 ∈ closeChainFiber mtWord mtFiber31DirectStates 1 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 0 [mtFiber31StateAt 0]
      (mtFiber31StateAt 0) (mtFiber31StateAt 1) (by decide) h0 (by decide)
      mtFiber31ReverseSingleStep1
  change mtFiber31StateAt 1 ∈ closeChainFiber mtWord mtFiber31DirectStates (1 + 15) [mtFiber31StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber31DirectStates 1 15 [mtFiber31StateAt 0] (mtFiber31StateAt 1) h1

theorem mtFiber31State2_in_close :
    mtFiber31StateAt 2 ∈ closeChainFiber mtWord mtFiber31DirectStates mtFiber31DirectStates.length [mtFiber31StateAt 0] := by
  have h0 : mtFiber31StateAt 0 ∈ closeChainFiber mtWord mtFiber31DirectStates 0 [mtFiber31StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber31StateAt 2 ∈ closeChainFiber mtWord mtFiber31DirectStates 1 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 0 [mtFiber31StateAt 0]
      (mtFiber31StateAt 0) (mtFiber31StateAt 2) (by decide) h0 (by decide)
      mtFiber31ReverseSingleStep2
  change mtFiber31StateAt 2 ∈ closeChainFiber mtWord mtFiber31DirectStates (1 + 15) [mtFiber31StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber31DirectStates 1 15 [mtFiber31StateAt 0] (mtFiber31StateAt 2) h1

theorem mtFiber31State3_in_close :
    mtFiber31StateAt 3 ∈ closeChainFiber mtWord mtFiber31DirectStates mtFiber31DirectStates.length [mtFiber31StateAt 0] := by
  have h0 : mtFiber31StateAt 0 ∈ closeChainFiber mtWord mtFiber31DirectStates 0 [mtFiber31StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber31StateAt 1 ∈ closeChainFiber mtWord mtFiber31DirectStates 1 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 0 [mtFiber31StateAt 0]
      (mtFiber31StateAt 0) (mtFiber31StateAt 1) (by decide) h0 (by decide)
      mtFiber31ReverseSingleStep1
  have h2 : mtFiber31StateAt 3 ∈ closeChainFiber mtWord mtFiber31DirectStates 2 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 1 [mtFiber31StateAt 0]
      (mtFiber31StateAt 1) (mtFiber31StateAt 3) (by decide) h1 (by decide)
      mtFiber31ReverseSingleStep3
  change mtFiber31StateAt 3 ∈ closeChainFiber mtWord mtFiber31DirectStates (2 + 14) [mtFiber31StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber31DirectStates 2 14 [mtFiber31StateAt 0] (mtFiber31StateAt 3) h2

theorem mtFiber31State4_in_close :
    mtFiber31StateAt 4 ∈ closeChainFiber mtWord mtFiber31DirectStates mtFiber31DirectStates.length [mtFiber31StateAt 0] := by
  have h0 : mtFiber31StateAt 0 ∈ closeChainFiber mtWord mtFiber31DirectStates 0 [mtFiber31StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber31StateAt 4 ∈ closeChainFiber mtWord mtFiber31DirectStates 1 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 0 [mtFiber31StateAt 0]
      (mtFiber31StateAt 0) (mtFiber31StateAt 4) (by decide) h0 (by decide)
      mtFiber31ReverseSingleStep4
  change mtFiber31StateAt 4 ∈ closeChainFiber mtWord mtFiber31DirectStates (1 + 15) [mtFiber31StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber31DirectStates 1 15 [mtFiber31StateAt 0] (mtFiber31StateAt 4) h1

theorem mtFiber31State5_in_close :
    mtFiber31StateAt 5 ∈ closeChainFiber mtWord mtFiber31DirectStates mtFiber31DirectStates.length [mtFiber31StateAt 0] := by
  have h0 : mtFiber31StateAt 0 ∈ closeChainFiber mtWord mtFiber31DirectStates 0 [mtFiber31StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber31StateAt 1 ∈ closeChainFiber mtWord mtFiber31DirectStates 1 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 0 [mtFiber31StateAt 0]
      (mtFiber31StateAt 0) (mtFiber31StateAt 1) (by decide) h0 (by decide)
      mtFiber31ReverseSingleStep1
  have h2 : mtFiber31StateAt 5 ∈ closeChainFiber mtWord mtFiber31DirectStates 2 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 1 [mtFiber31StateAt 0]
      (mtFiber31StateAt 1) (mtFiber31StateAt 5) (by decide) h1 (by decide)
      mtFiber31ReverseSingleStep5
  change mtFiber31StateAt 5 ∈ closeChainFiber mtWord mtFiber31DirectStates (2 + 14) [mtFiber31StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber31DirectStates 2 14 [mtFiber31StateAt 0] (mtFiber31StateAt 5) h2

theorem mtFiber31State6_in_close :
    mtFiber31StateAt 6 ∈ closeChainFiber mtWord mtFiber31DirectStates mtFiber31DirectStates.length [mtFiber31StateAt 0] := by
  have h0 : mtFiber31StateAt 0 ∈ closeChainFiber mtWord mtFiber31DirectStates 0 [mtFiber31StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber31StateAt 2 ∈ closeChainFiber mtWord mtFiber31DirectStates 1 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 0 [mtFiber31StateAt 0]
      (mtFiber31StateAt 0) (mtFiber31StateAt 2) (by decide) h0 (by decide)
      mtFiber31ReverseSingleStep2
  have h2 : mtFiber31StateAt 6 ∈ closeChainFiber mtWord mtFiber31DirectStates 2 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 1 [mtFiber31StateAt 0]
      (mtFiber31StateAt 2) (mtFiber31StateAt 6) (by decide) h1 (by decide)
      mtFiber31ReverseSingleStep6
  change mtFiber31StateAt 6 ∈ closeChainFiber mtWord mtFiber31DirectStates (2 + 14) [mtFiber31StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber31DirectStates 2 14 [mtFiber31StateAt 0] (mtFiber31StateAt 6) h2

theorem mtFiber31State7_in_close :
    mtFiber31StateAt 7 ∈ closeChainFiber mtWord mtFiber31DirectStates mtFiber31DirectStates.length [mtFiber31StateAt 0] := by
  have h0 : mtFiber31StateAt 0 ∈ closeChainFiber mtWord mtFiber31DirectStates 0 [mtFiber31StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber31StateAt 1 ∈ closeChainFiber mtWord mtFiber31DirectStates 1 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 0 [mtFiber31StateAt 0]
      (mtFiber31StateAt 0) (mtFiber31StateAt 1) (by decide) h0 (by decide)
      mtFiber31ReverseSingleStep1
  have h2 : mtFiber31StateAt 3 ∈ closeChainFiber mtWord mtFiber31DirectStates 2 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 1 [mtFiber31StateAt 0]
      (mtFiber31StateAt 1) (mtFiber31StateAt 3) (by decide) h1 (by decide)
      mtFiber31ReverseSingleStep3
  have h3 : mtFiber31StateAt 7 ∈ closeChainFiber mtWord mtFiber31DirectStates 3 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 2 [mtFiber31StateAt 0]
      (mtFiber31StateAt 3) (mtFiber31StateAt 7) (by decide) h2 (by decide)
      mtFiber31ReverseSingleStep7
  change mtFiber31StateAt 7 ∈ closeChainFiber mtWord mtFiber31DirectStates (3 + 13) [mtFiber31StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber31DirectStates 3 13 [mtFiber31StateAt 0] (mtFiber31StateAt 7) h3

theorem mtFiber31State8_in_close :
    mtFiber31StateAt 8 ∈ closeChainFiber mtWord mtFiber31DirectStates mtFiber31DirectStates.length [mtFiber31StateAt 0] := by
  have h0 : mtFiber31StateAt 0 ∈ closeChainFiber mtWord mtFiber31DirectStates 0 [mtFiber31StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber31StateAt 4 ∈ closeChainFiber mtWord mtFiber31DirectStates 1 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 0 [mtFiber31StateAt 0]
      (mtFiber31StateAt 0) (mtFiber31StateAt 4) (by decide) h0 (by decide)
      mtFiber31ReverseSingleStep4
  have h2 : mtFiber31StateAt 8 ∈ closeChainFiber mtWord mtFiber31DirectStates 2 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 1 [mtFiber31StateAt 0]
      (mtFiber31StateAt 4) (mtFiber31StateAt 8) (by decide) h1 (by decide)
      mtFiber31ReverseSingleStep8
  change mtFiber31StateAt 8 ∈ closeChainFiber mtWord mtFiber31DirectStates (2 + 14) [mtFiber31StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber31DirectStates 2 14 [mtFiber31StateAt 0] (mtFiber31StateAt 8) h2

theorem mtFiber31State9_in_close :
    mtFiber31StateAt 9 ∈ closeChainFiber mtWord mtFiber31DirectStates mtFiber31DirectStates.length [mtFiber31StateAt 0] := by
  have h0 : mtFiber31StateAt 0 ∈ closeChainFiber mtWord mtFiber31DirectStates 0 [mtFiber31StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber31StateAt 1 ∈ closeChainFiber mtWord mtFiber31DirectStates 1 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 0 [mtFiber31StateAt 0]
      (mtFiber31StateAt 0) (mtFiber31StateAt 1) (by decide) h0 (by decide)
      mtFiber31ReverseSingleStep1
  have h2 : mtFiber31StateAt 5 ∈ closeChainFiber mtWord mtFiber31DirectStates 2 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 1 [mtFiber31StateAt 0]
      (mtFiber31StateAt 1) (mtFiber31StateAt 5) (by decide) h1 (by decide)
      mtFiber31ReverseSingleStep5
  have h3 : mtFiber31StateAt 9 ∈ closeChainFiber mtWord mtFiber31DirectStates 3 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 2 [mtFiber31StateAt 0]
      (mtFiber31StateAt 5) (mtFiber31StateAt 9) (by decide) h2 (by decide)
      mtFiber31ReverseSingleStep9
  change mtFiber31StateAt 9 ∈ closeChainFiber mtWord mtFiber31DirectStates (3 + 13) [mtFiber31StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber31DirectStates 3 13 [mtFiber31StateAt 0] (mtFiber31StateAt 9) h3

theorem mtFiber31State10_in_close :
    mtFiber31StateAt 10 ∈ closeChainFiber mtWord mtFiber31DirectStates mtFiber31DirectStates.length [mtFiber31StateAt 0] := by
  have h0 : mtFiber31StateAt 0 ∈ closeChainFiber mtWord mtFiber31DirectStates 0 [mtFiber31StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber31StateAt 2 ∈ closeChainFiber mtWord mtFiber31DirectStates 1 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 0 [mtFiber31StateAt 0]
      (mtFiber31StateAt 0) (mtFiber31StateAt 2) (by decide) h0 (by decide)
      mtFiber31ReverseSingleStep2
  have h2 : mtFiber31StateAt 6 ∈ closeChainFiber mtWord mtFiber31DirectStates 2 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 1 [mtFiber31StateAt 0]
      (mtFiber31StateAt 2) (mtFiber31StateAt 6) (by decide) h1 (by decide)
      mtFiber31ReverseSingleStep6
  have h3 : mtFiber31StateAt 10 ∈ closeChainFiber mtWord mtFiber31DirectStates 3 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 2 [mtFiber31StateAt 0]
      (mtFiber31StateAt 6) (mtFiber31StateAt 10) (by decide) h2 (by decide)
      mtFiber31ReverseSingleStep10
  change mtFiber31StateAt 10 ∈ closeChainFiber mtWord mtFiber31DirectStates (3 + 13) [mtFiber31StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber31DirectStates 3 13 [mtFiber31StateAt 0] (mtFiber31StateAt 10) h3

theorem mtFiber31State11_in_close :
    mtFiber31StateAt 11 ∈ closeChainFiber mtWord mtFiber31DirectStates mtFiber31DirectStates.length [mtFiber31StateAt 0] := by
  have h0 : mtFiber31StateAt 0 ∈ closeChainFiber mtWord mtFiber31DirectStates 0 [mtFiber31StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber31StateAt 1 ∈ closeChainFiber mtWord mtFiber31DirectStates 1 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 0 [mtFiber31StateAt 0]
      (mtFiber31StateAt 0) (mtFiber31StateAt 1) (by decide) h0 (by decide)
      mtFiber31ReverseSingleStep1
  have h2 : mtFiber31StateAt 3 ∈ closeChainFiber mtWord mtFiber31DirectStates 2 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 1 [mtFiber31StateAt 0]
      (mtFiber31StateAt 1) (mtFiber31StateAt 3) (by decide) h1 (by decide)
      mtFiber31ReverseSingleStep3
  have h3 : mtFiber31StateAt 7 ∈ closeChainFiber mtWord mtFiber31DirectStates 3 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 2 [mtFiber31StateAt 0]
      (mtFiber31StateAt 3) (mtFiber31StateAt 7) (by decide) h2 (by decide)
      mtFiber31ReverseSingleStep7
  have h4 : mtFiber31StateAt 11 ∈ closeChainFiber mtWord mtFiber31DirectStates 4 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 3 [mtFiber31StateAt 0]
      (mtFiber31StateAt 7) (mtFiber31StateAt 11) (by decide) h3 (by decide)
      mtFiber31ReverseSingleStep11
  change mtFiber31StateAt 11 ∈ closeChainFiber mtWord mtFiber31DirectStates (4 + 12) [mtFiber31StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber31DirectStates 4 12 [mtFiber31StateAt 0] (mtFiber31StateAt 11) h4

theorem mtFiber31State12_in_close :
    mtFiber31StateAt 12 ∈ closeChainFiber mtWord mtFiber31DirectStates mtFiber31DirectStates.length [mtFiber31StateAt 0] := by
  have h0 : mtFiber31StateAt 0 ∈ closeChainFiber mtWord mtFiber31DirectStates 0 [mtFiber31StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber31StateAt 12 ∈ closeChainFiber mtWord mtFiber31DirectStates 1 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 0 [mtFiber31StateAt 0]
      (mtFiber31StateAt 0) (mtFiber31StateAt 12) (by decide) h0 (by decide)
      mtFiber31ReverseSingleStep12
  change mtFiber31StateAt 12 ∈ closeChainFiber mtWord mtFiber31DirectStates (1 + 15) [mtFiber31StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber31DirectStates 1 15 [mtFiber31StateAt 0] (mtFiber31StateAt 12) h1

theorem mtFiber31State13_in_close :
    mtFiber31StateAt 13 ∈ closeChainFiber mtWord mtFiber31DirectStates mtFiber31DirectStates.length [mtFiber31StateAt 0] := by
  have h0 : mtFiber31StateAt 0 ∈ closeChainFiber mtWord mtFiber31DirectStates 0 [mtFiber31StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber31StateAt 1 ∈ closeChainFiber mtWord mtFiber31DirectStates 1 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 0 [mtFiber31StateAt 0]
      (mtFiber31StateAt 0) (mtFiber31StateAt 1) (by decide) h0 (by decide)
      mtFiber31ReverseSingleStep1
  have h2 : mtFiber31StateAt 13 ∈ closeChainFiber mtWord mtFiber31DirectStates 2 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 1 [mtFiber31StateAt 0]
      (mtFiber31StateAt 1) (mtFiber31StateAt 13) (by decide) h1 (by decide)
      mtFiber31ReverseSingleStep13
  change mtFiber31StateAt 13 ∈ closeChainFiber mtWord mtFiber31DirectStates (2 + 14) [mtFiber31StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber31DirectStates 2 14 [mtFiber31StateAt 0] (mtFiber31StateAt 13) h2

theorem mtFiber31State14_in_close :
    mtFiber31StateAt 14 ∈ closeChainFiber mtWord mtFiber31DirectStates mtFiber31DirectStates.length [mtFiber31StateAt 0] := by
  have h0 : mtFiber31StateAt 0 ∈ closeChainFiber mtWord mtFiber31DirectStates 0 [mtFiber31StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber31StateAt 2 ∈ closeChainFiber mtWord mtFiber31DirectStates 1 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 0 [mtFiber31StateAt 0]
      (mtFiber31StateAt 0) (mtFiber31StateAt 2) (by decide) h0 (by decide)
      mtFiber31ReverseSingleStep2
  have h2 : mtFiber31StateAt 14 ∈ closeChainFiber mtWord mtFiber31DirectStates 2 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 1 [mtFiber31StateAt 0]
      (mtFiber31StateAt 2) (mtFiber31StateAt 14) (by decide) h1 (by decide)
      mtFiber31ReverseSingleStep14
  change mtFiber31StateAt 14 ∈ closeChainFiber mtWord mtFiber31DirectStates (2 + 14) [mtFiber31StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber31DirectStates 2 14 [mtFiber31StateAt 0] (mtFiber31StateAt 14) h2

theorem mtFiber31State15_in_close :
    mtFiber31StateAt 15 ∈ closeChainFiber mtWord mtFiber31DirectStates mtFiber31DirectStates.length [mtFiber31StateAt 0] := by
  have h0 : mtFiber31StateAt 0 ∈ closeChainFiber mtWord mtFiber31DirectStates 0 [mtFiber31StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber31StateAt 1 ∈ closeChainFiber mtWord mtFiber31DirectStates 1 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 0 [mtFiber31StateAt 0]
      (mtFiber31StateAt 0) (mtFiber31StateAt 1) (by decide) h0 (by decide)
      mtFiber31ReverseSingleStep1
  have h2 : mtFiber31StateAt 3 ∈ closeChainFiber mtWord mtFiber31DirectStates 2 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 1 [mtFiber31StateAt 0]
      (mtFiber31StateAt 1) (mtFiber31StateAt 3) (by decide) h1 (by decide)
      mtFiber31ReverseSingleStep3
  have h3 : mtFiber31StateAt 15 ∈ closeChainFiber mtWord mtFiber31DirectStates 3 [mtFiber31StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber31DirectStates 2 [mtFiber31StateAt 0]
      (mtFiber31StateAt 3) (mtFiber31StateAt 15) (by decide) h2 (by decide)
      mtFiber31ReverseSingleStep15
  change mtFiber31StateAt 15 ∈ closeChainFiber mtWord mtFiber31DirectStates (3 + 13) [mtFiber31StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber31DirectStates 3 13 [mtFiber31StateAt 0] (mtFiber31StateAt 15) h3

theorem mtFiber31DirectConnected :
    chainFiberConnected mtWord mtFiber31DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber31DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber31State0_in_close
  · subst state
    exact mtFiber31State1_in_close
  · subst state
    exact mtFiber31State2_in_close
  · subst state
    exact mtFiber31State3_in_close
  · subst state
    exact mtFiber31State4_in_close
  · subst state
    exact mtFiber31State5_in_close
  · subst state
    exact mtFiber31State6_in_close
  · subst state
    exact mtFiber31State7_in_close
  · subst state
    exact mtFiber31State8_in_close
  · subst state
    exact mtFiber31State9_in_close
  · subst state
    exact mtFiber31State10_in_close
  · subst state
    exact mtFiber31State11_in_close
  · subst state
    exact mtFiber31State12_in_close
  · subst state
    exact mtFiber31State13_in_close
  · subst state
    exact mtFiber31State14_in_close
  · subst state
    exact mtFiber31State15_in_close
  · cases h
def mtFiber33StateAt (i : Nat) : List TauState :=
  directStates (mtFiber33RowAt i).sourceLeft (mtFiber33RowAt i).sourceRight

def mtFiber33DirectStates : List (List TauState) :=
  [mtFiber33StateAt 0, mtFiber33StateAt 1, mtFiber33StateAt 2, mtFiber33StateAt 3, mtFiber33StateAt 4, mtFiber33StateAt 5, mtFiber33StateAt 6, mtFiber33StateAt 7, mtFiber33StateAt 8, mtFiber33StateAt 9, mtFiber33StateAt 10, mtFiber33StateAt 11, mtFiber33StateAt 12, mtFiber33StateAt 13, mtFiber33StateAt 14, mtFiber33StateAt 15]

theorem mtFiber33ReverseRow_1_ok :
    mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber33Chunk0_ok
  change (mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 0) &&
    mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber33ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber33StateAt 0) (mtFiber33StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber33StateAt 0) (mtFiber33StateAt 1)
    (mtFiber33RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber33Key mtFiber33Expected
        (mtFiber33RowAt 1) (by decide) mtFiber33ReverseRow_1_ok
      simpa [mtFiber33StateAt, mtFiber33RowAt, mtFiber33Rows, listGetD, directRow] using h)

theorem mtFiber33ReverseRow_2_ok :
    mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber33Chunk1_ok
  change (mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 2) &&
    mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber33ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber33StateAt 0) (mtFiber33StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber33StateAt 0) (mtFiber33StateAt 2)
    (mtFiber33RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber33Key mtFiber33Expected
        (mtFiber33RowAt 2) (by decide) mtFiber33ReverseRow_2_ok
      simpa [mtFiber33StateAt, mtFiber33RowAt, mtFiber33Rows, listGetD, directRow] using h)

theorem mtFiber33ReverseRow_3_ok :
    mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber33Chunk1_ok
  change (mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 2) &&
    mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber33ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber33StateAt 1) (mtFiber33StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber33StateAt 1) (mtFiber33StateAt 3)
    (mtFiber33RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber33Key mtFiber33Expected
        (mtFiber33RowAt 3) (by decide) mtFiber33ReverseRow_3_ok
      simpa [mtFiber33StateAt, mtFiber33RowAt, mtFiber33Rows, listGetD, directRow] using h)

theorem mtFiber33ReverseRow_4_ok :
    mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber33Chunk2_ok
  change (mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 4) &&
    mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber33ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber33StateAt 0) (mtFiber33StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber33StateAt 0) (mtFiber33StateAt 4)
    (mtFiber33RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber33Key mtFiber33Expected
        (mtFiber33RowAt 4) (by decide) mtFiber33ReverseRow_4_ok
      simpa [mtFiber33StateAt, mtFiber33RowAt, mtFiber33Rows, listGetD, directRow] using h)

theorem mtFiber33ReverseRow_5_ok :
    mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber33Chunk2_ok
  change (mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 4) &&
    mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber33ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber33StateAt 1) (mtFiber33StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber33StateAt 1) (mtFiber33StateAt 5)
    (mtFiber33RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber33Key mtFiber33Expected
        (mtFiber33RowAt 5) (by decide) mtFiber33ReverseRow_5_ok
      simpa [mtFiber33StateAt, mtFiber33RowAt, mtFiber33Rows, listGetD, directRow] using h)

theorem mtFiber33ReverseRow_6_ok :
    mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber33Chunk3_ok
  change (mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 6) &&
    mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber33ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber33StateAt 2) (mtFiber33StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber33StateAt 2) (mtFiber33StateAt 6)
    (mtFiber33RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber33Key mtFiber33Expected
        (mtFiber33RowAt 6) (by decide) mtFiber33ReverseRow_6_ok
      simpa [mtFiber33StateAt, mtFiber33RowAt, mtFiber33Rows, listGetD, directRow] using h)

theorem mtFiber33ReverseRow_7_ok :
    mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber33Chunk3_ok
  change (mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 6) &&
    mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber33ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber33StateAt 3) (mtFiber33StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber33StateAt 3) (mtFiber33StateAt 7)
    (mtFiber33RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber33Key mtFiber33Expected
        (mtFiber33RowAt 7) (by decide) mtFiber33ReverseRow_7_ok
      simpa [mtFiber33StateAt, mtFiber33RowAt, mtFiber33Rows, listGetD, directRow] using h)

theorem mtFiber33ReverseRow_8_ok :
    mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber33Chunk4_ok
  change (mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 8) &&
    mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber33ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber33StateAt 4) (mtFiber33StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber33StateAt 4) (mtFiber33StateAt 8)
    (mtFiber33RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber33Key mtFiber33Expected
        (mtFiber33RowAt 8) (by decide) mtFiber33ReverseRow_8_ok
      simpa [mtFiber33StateAt, mtFiber33RowAt, mtFiber33Rows, listGetD, directRow] using h)

theorem mtFiber33ReverseRow_9_ok :
    mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber33Chunk4_ok
  change (mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 8) &&
    mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber33ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber33StateAt 5) (mtFiber33StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber33StateAt 5) (mtFiber33StateAt 9)
    (mtFiber33RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber33Key mtFiber33Expected
        (mtFiber33RowAt 9) (by decide) mtFiber33ReverseRow_9_ok
      simpa [mtFiber33StateAt, mtFiber33RowAt, mtFiber33Rows, listGetD, directRow] using h)

theorem mtFiber33ReverseRow_10_ok :
    mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber33Chunk5_ok
  change (mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 10) &&
    mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber33ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber33StateAt 6) (mtFiber33StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber33StateAt 6) (mtFiber33StateAt 10)
    (mtFiber33RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber33Key mtFiber33Expected
        (mtFiber33RowAt 10) (by decide) mtFiber33ReverseRow_10_ok
      simpa [mtFiber33StateAt, mtFiber33RowAt, mtFiber33Rows, listGetD, directRow] using h)

theorem mtFiber33ReverseRow_11_ok :
    mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber33Chunk5_ok
  change (mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 10) &&
    mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber33ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber33StateAt 7) (mtFiber33StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber33StateAt 7) (mtFiber33StateAt 11)
    (mtFiber33RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber33Key mtFiber33Expected
        (mtFiber33RowAt 11) (by decide) mtFiber33ReverseRow_11_ok
      simpa [mtFiber33StateAt, mtFiber33RowAt, mtFiber33Rows, listGetD, directRow] using h)

theorem mtFiber33ReverseRow_12_ok :
    mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber33Chunk6_ok
  change (mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 12) &&
    mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber33ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber33StateAt 0) (mtFiber33StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber33StateAt 0) (mtFiber33StateAt 12)
    (mtFiber33RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber33Key mtFiber33Expected
        (mtFiber33RowAt 12) (by decide) mtFiber33ReverseRow_12_ok
      simpa [mtFiber33StateAt, mtFiber33RowAt, mtFiber33Rows, listGetD, directRow] using h)

theorem mtFiber33ReverseRow_13_ok :
    mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber33Chunk6_ok
  change (mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 12) &&
    mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber33ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber33StateAt 1) (mtFiber33StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber33StateAt 1) (mtFiber33StateAt 13)
    (mtFiber33RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber33Key mtFiber33Expected
        (mtFiber33RowAt 13) (by decide) mtFiber33ReverseRow_13_ok
      simpa [mtFiber33StateAt, mtFiber33RowAt, mtFiber33Rows, listGetD, directRow] using h)

theorem mtFiber33ReverseRow_14_ok :
    mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber33Chunk7_ok
  change (mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 14) &&
    mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber33ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber33StateAt 2) (mtFiber33StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber33StateAt 2) (mtFiber33StateAt 14)
    (mtFiber33RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber33Key mtFiber33Expected
        (mtFiber33RowAt 14) (by decide) mtFiber33ReverseRow_14_ok
      simpa [mtFiber33StateAt, mtFiber33RowAt, mtFiber33Rows, listGetD, directRow] using h)

theorem mtFiber33ReverseRow_15_ok :
    mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber33Chunk7_ok
  change (mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 14) &&
    mtRowReverseValid mtFiber33Key mtFiber33Expected (mtFiber33RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber33ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber33StateAt 3) (mtFiber33StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber33StateAt 3) (mtFiber33StateAt 15)
    (mtFiber33RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber33Key mtFiber33Expected
        (mtFiber33RowAt 15) (by decide) mtFiber33ReverseRow_15_ok
      simpa [mtFiber33StateAt, mtFiber33RowAt, mtFiber33Rows, listGetD, directRow] using h)

theorem mtFiber33State0_in_close :
    mtFiber33StateAt 0 ∈ closeChainFiber mtWord mtFiber33DirectStates mtFiber33DirectStates.length [mtFiber33StateAt 0] := by
  change mtFiber33StateAt 0 ∈ closeChainFiber mtWord mtFiber33DirectStates 16 [mtFiber33StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber33DirectStates 0 16 [mtFiber33StateAt 0] (mtFiber33StateAt 0) (by simp [closeChainFiber])

theorem mtFiber33State1_in_close :
    mtFiber33StateAt 1 ∈ closeChainFiber mtWord mtFiber33DirectStates mtFiber33DirectStates.length [mtFiber33StateAt 0] := by
  have h0 : mtFiber33StateAt 0 ∈ closeChainFiber mtWord mtFiber33DirectStates 0 [mtFiber33StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber33StateAt 1 ∈ closeChainFiber mtWord mtFiber33DirectStates 1 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 0 [mtFiber33StateAt 0]
      (mtFiber33StateAt 0) (mtFiber33StateAt 1) (by decide) h0 (by decide)
      mtFiber33ReverseSingleStep1
  change mtFiber33StateAt 1 ∈ closeChainFiber mtWord mtFiber33DirectStates (1 + 15) [mtFiber33StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber33DirectStates 1 15 [mtFiber33StateAt 0] (mtFiber33StateAt 1) h1

theorem mtFiber33State2_in_close :
    mtFiber33StateAt 2 ∈ closeChainFiber mtWord mtFiber33DirectStates mtFiber33DirectStates.length [mtFiber33StateAt 0] := by
  have h0 : mtFiber33StateAt 0 ∈ closeChainFiber mtWord mtFiber33DirectStates 0 [mtFiber33StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber33StateAt 2 ∈ closeChainFiber mtWord mtFiber33DirectStates 1 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 0 [mtFiber33StateAt 0]
      (mtFiber33StateAt 0) (mtFiber33StateAt 2) (by decide) h0 (by decide)
      mtFiber33ReverseSingleStep2
  change mtFiber33StateAt 2 ∈ closeChainFiber mtWord mtFiber33DirectStates (1 + 15) [mtFiber33StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber33DirectStates 1 15 [mtFiber33StateAt 0] (mtFiber33StateAt 2) h1

theorem mtFiber33State3_in_close :
    mtFiber33StateAt 3 ∈ closeChainFiber mtWord mtFiber33DirectStates mtFiber33DirectStates.length [mtFiber33StateAt 0] := by
  have h0 : mtFiber33StateAt 0 ∈ closeChainFiber mtWord mtFiber33DirectStates 0 [mtFiber33StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber33StateAt 1 ∈ closeChainFiber mtWord mtFiber33DirectStates 1 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 0 [mtFiber33StateAt 0]
      (mtFiber33StateAt 0) (mtFiber33StateAt 1) (by decide) h0 (by decide)
      mtFiber33ReverseSingleStep1
  have h2 : mtFiber33StateAt 3 ∈ closeChainFiber mtWord mtFiber33DirectStates 2 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 1 [mtFiber33StateAt 0]
      (mtFiber33StateAt 1) (mtFiber33StateAt 3) (by decide) h1 (by decide)
      mtFiber33ReverseSingleStep3
  change mtFiber33StateAt 3 ∈ closeChainFiber mtWord mtFiber33DirectStates (2 + 14) [mtFiber33StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber33DirectStates 2 14 [mtFiber33StateAt 0] (mtFiber33StateAt 3) h2

theorem mtFiber33State4_in_close :
    mtFiber33StateAt 4 ∈ closeChainFiber mtWord mtFiber33DirectStates mtFiber33DirectStates.length [mtFiber33StateAt 0] := by
  have h0 : mtFiber33StateAt 0 ∈ closeChainFiber mtWord mtFiber33DirectStates 0 [mtFiber33StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber33StateAt 4 ∈ closeChainFiber mtWord mtFiber33DirectStates 1 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 0 [mtFiber33StateAt 0]
      (mtFiber33StateAt 0) (mtFiber33StateAt 4) (by decide) h0 (by decide)
      mtFiber33ReverseSingleStep4
  change mtFiber33StateAt 4 ∈ closeChainFiber mtWord mtFiber33DirectStates (1 + 15) [mtFiber33StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber33DirectStates 1 15 [mtFiber33StateAt 0] (mtFiber33StateAt 4) h1

theorem mtFiber33State5_in_close :
    mtFiber33StateAt 5 ∈ closeChainFiber mtWord mtFiber33DirectStates mtFiber33DirectStates.length [mtFiber33StateAt 0] := by
  have h0 : mtFiber33StateAt 0 ∈ closeChainFiber mtWord mtFiber33DirectStates 0 [mtFiber33StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber33StateAt 1 ∈ closeChainFiber mtWord mtFiber33DirectStates 1 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 0 [mtFiber33StateAt 0]
      (mtFiber33StateAt 0) (mtFiber33StateAt 1) (by decide) h0 (by decide)
      mtFiber33ReverseSingleStep1
  have h2 : mtFiber33StateAt 5 ∈ closeChainFiber mtWord mtFiber33DirectStates 2 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 1 [mtFiber33StateAt 0]
      (mtFiber33StateAt 1) (mtFiber33StateAt 5) (by decide) h1 (by decide)
      mtFiber33ReverseSingleStep5
  change mtFiber33StateAt 5 ∈ closeChainFiber mtWord mtFiber33DirectStates (2 + 14) [mtFiber33StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber33DirectStates 2 14 [mtFiber33StateAt 0] (mtFiber33StateAt 5) h2

theorem mtFiber33State6_in_close :
    mtFiber33StateAt 6 ∈ closeChainFiber mtWord mtFiber33DirectStates mtFiber33DirectStates.length [mtFiber33StateAt 0] := by
  have h0 : mtFiber33StateAt 0 ∈ closeChainFiber mtWord mtFiber33DirectStates 0 [mtFiber33StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber33StateAt 2 ∈ closeChainFiber mtWord mtFiber33DirectStates 1 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 0 [mtFiber33StateAt 0]
      (mtFiber33StateAt 0) (mtFiber33StateAt 2) (by decide) h0 (by decide)
      mtFiber33ReverseSingleStep2
  have h2 : mtFiber33StateAt 6 ∈ closeChainFiber mtWord mtFiber33DirectStates 2 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 1 [mtFiber33StateAt 0]
      (mtFiber33StateAt 2) (mtFiber33StateAt 6) (by decide) h1 (by decide)
      mtFiber33ReverseSingleStep6
  change mtFiber33StateAt 6 ∈ closeChainFiber mtWord mtFiber33DirectStates (2 + 14) [mtFiber33StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber33DirectStates 2 14 [mtFiber33StateAt 0] (mtFiber33StateAt 6) h2

theorem mtFiber33State7_in_close :
    mtFiber33StateAt 7 ∈ closeChainFiber mtWord mtFiber33DirectStates mtFiber33DirectStates.length [mtFiber33StateAt 0] := by
  have h0 : mtFiber33StateAt 0 ∈ closeChainFiber mtWord mtFiber33DirectStates 0 [mtFiber33StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber33StateAt 1 ∈ closeChainFiber mtWord mtFiber33DirectStates 1 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 0 [mtFiber33StateAt 0]
      (mtFiber33StateAt 0) (mtFiber33StateAt 1) (by decide) h0 (by decide)
      mtFiber33ReverseSingleStep1
  have h2 : mtFiber33StateAt 3 ∈ closeChainFiber mtWord mtFiber33DirectStates 2 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 1 [mtFiber33StateAt 0]
      (mtFiber33StateAt 1) (mtFiber33StateAt 3) (by decide) h1 (by decide)
      mtFiber33ReverseSingleStep3
  have h3 : mtFiber33StateAt 7 ∈ closeChainFiber mtWord mtFiber33DirectStates 3 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 2 [mtFiber33StateAt 0]
      (mtFiber33StateAt 3) (mtFiber33StateAt 7) (by decide) h2 (by decide)
      mtFiber33ReverseSingleStep7
  change mtFiber33StateAt 7 ∈ closeChainFiber mtWord mtFiber33DirectStates (3 + 13) [mtFiber33StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber33DirectStates 3 13 [mtFiber33StateAt 0] (mtFiber33StateAt 7) h3

theorem mtFiber33State8_in_close :
    mtFiber33StateAt 8 ∈ closeChainFiber mtWord mtFiber33DirectStates mtFiber33DirectStates.length [mtFiber33StateAt 0] := by
  have h0 : mtFiber33StateAt 0 ∈ closeChainFiber mtWord mtFiber33DirectStates 0 [mtFiber33StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber33StateAt 4 ∈ closeChainFiber mtWord mtFiber33DirectStates 1 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 0 [mtFiber33StateAt 0]
      (mtFiber33StateAt 0) (mtFiber33StateAt 4) (by decide) h0 (by decide)
      mtFiber33ReverseSingleStep4
  have h2 : mtFiber33StateAt 8 ∈ closeChainFiber mtWord mtFiber33DirectStates 2 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 1 [mtFiber33StateAt 0]
      (mtFiber33StateAt 4) (mtFiber33StateAt 8) (by decide) h1 (by decide)
      mtFiber33ReverseSingleStep8
  change mtFiber33StateAt 8 ∈ closeChainFiber mtWord mtFiber33DirectStates (2 + 14) [mtFiber33StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber33DirectStates 2 14 [mtFiber33StateAt 0] (mtFiber33StateAt 8) h2

theorem mtFiber33State9_in_close :
    mtFiber33StateAt 9 ∈ closeChainFiber mtWord mtFiber33DirectStates mtFiber33DirectStates.length [mtFiber33StateAt 0] := by
  have h0 : mtFiber33StateAt 0 ∈ closeChainFiber mtWord mtFiber33DirectStates 0 [mtFiber33StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber33StateAt 1 ∈ closeChainFiber mtWord mtFiber33DirectStates 1 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 0 [mtFiber33StateAt 0]
      (mtFiber33StateAt 0) (mtFiber33StateAt 1) (by decide) h0 (by decide)
      mtFiber33ReverseSingleStep1
  have h2 : mtFiber33StateAt 5 ∈ closeChainFiber mtWord mtFiber33DirectStates 2 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 1 [mtFiber33StateAt 0]
      (mtFiber33StateAt 1) (mtFiber33StateAt 5) (by decide) h1 (by decide)
      mtFiber33ReverseSingleStep5
  have h3 : mtFiber33StateAt 9 ∈ closeChainFiber mtWord mtFiber33DirectStates 3 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 2 [mtFiber33StateAt 0]
      (mtFiber33StateAt 5) (mtFiber33StateAt 9) (by decide) h2 (by decide)
      mtFiber33ReverseSingleStep9
  change mtFiber33StateAt 9 ∈ closeChainFiber mtWord mtFiber33DirectStates (3 + 13) [mtFiber33StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber33DirectStates 3 13 [mtFiber33StateAt 0] (mtFiber33StateAt 9) h3

theorem mtFiber33State10_in_close :
    mtFiber33StateAt 10 ∈ closeChainFiber mtWord mtFiber33DirectStates mtFiber33DirectStates.length [mtFiber33StateAt 0] := by
  have h0 : mtFiber33StateAt 0 ∈ closeChainFiber mtWord mtFiber33DirectStates 0 [mtFiber33StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber33StateAt 2 ∈ closeChainFiber mtWord mtFiber33DirectStates 1 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 0 [mtFiber33StateAt 0]
      (mtFiber33StateAt 0) (mtFiber33StateAt 2) (by decide) h0 (by decide)
      mtFiber33ReverseSingleStep2
  have h2 : mtFiber33StateAt 6 ∈ closeChainFiber mtWord mtFiber33DirectStates 2 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 1 [mtFiber33StateAt 0]
      (mtFiber33StateAt 2) (mtFiber33StateAt 6) (by decide) h1 (by decide)
      mtFiber33ReverseSingleStep6
  have h3 : mtFiber33StateAt 10 ∈ closeChainFiber mtWord mtFiber33DirectStates 3 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 2 [mtFiber33StateAt 0]
      (mtFiber33StateAt 6) (mtFiber33StateAt 10) (by decide) h2 (by decide)
      mtFiber33ReverseSingleStep10
  change mtFiber33StateAt 10 ∈ closeChainFiber mtWord mtFiber33DirectStates (3 + 13) [mtFiber33StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber33DirectStates 3 13 [mtFiber33StateAt 0] (mtFiber33StateAt 10) h3

theorem mtFiber33State11_in_close :
    mtFiber33StateAt 11 ∈ closeChainFiber mtWord mtFiber33DirectStates mtFiber33DirectStates.length [mtFiber33StateAt 0] := by
  have h0 : mtFiber33StateAt 0 ∈ closeChainFiber mtWord mtFiber33DirectStates 0 [mtFiber33StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber33StateAt 1 ∈ closeChainFiber mtWord mtFiber33DirectStates 1 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 0 [mtFiber33StateAt 0]
      (mtFiber33StateAt 0) (mtFiber33StateAt 1) (by decide) h0 (by decide)
      mtFiber33ReverseSingleStep1
  have h2 : mtFiber33StateAt 3 ∈ closeChainFiber mtWord mtFiber33DirectStates 2 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 1 [mtFiber33StateAt 0]
      (mtFiber33StateAt 1) (mtFiber33StateAt 3) (by decide) h1 (by decide)
      mtFiber33ReverseSingleStep3
  have h3 : mtFiber33StateAt 7 ∈ closeChainFiber mtWord mtFiber33DirectStates 3 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 2 [mtFiber33StateAt 0]
      (mtFiber33StateAt 3) (mtFiber33StateAt 7) (by decide) h2 (by decide)
      mtFiber33ReverseSingleStep7
  have h4 : mtFiber33StateAt 11 ∈ closeChainFiber mtWord mtFiber33DirectStates 4 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 3 [mtFiber33StateAt 0]
      (mtFiber33StateAt 7) (mtFiber33StateAt 11) (by decide) h3 (by decide)
      mtFiber33ReverseSingleStep11
  change mtFiber33StateAt 11 ∈ closeChainFiber mtWord mtFiber33DirectStates (4 + 12) [mtFiber33StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber33DirectStates 4 12 [mtFiber33StateAt 0] (mtFiber33StateAt 11) h4

theorem mtFiber33State12_in_close :
    mtFiber33StateAt 12 ∈ closeChainFiber mtWord mtFiber33DirectStates mtFiber33DirectStates.length [mtFiber33StateAt 0] := by
  have h0 : mtFiber33StateAt 0 ∈ closeChainFiber mtWord mtFiber33DirectStates 0 [mtFiber33StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber33StateAt 12 ∈ closeChainFiber mtWord mtFiber33DirectStates 1 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 0 [mtFiber33StateAt 0]
      (mtFiber33StateAt 0) (mtFiber33StateAt 12) (by decide) h0 (by decide)
      mtFiber33ReverseSingleStep12
  change mtFiber33StateAt 12 ∈ closeChainFiber mtWord mtFiber33DirectStates (1 + 15) [mtFiber33StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber33DirectStates 1 15 [mtFiber33StateAt 0] (mtFiber33StateAt 12) h1

theorem mtFiber33State13_in_close :
    mtFiber33StateAt 13 ∈ closeChainFiber mtWord mtFiber33DirectStates mtFiber33DirectStates.length [mtFiber33StateAt 0] := by
  have h0 : mtFiber33StateAt 0 ∈ closeChainFiber mtWord mtFiber33DirectStates 0 [mtFiber33StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber33StateAt 1 ∈ closeChainFiber mtWord mtFiber33DirectStates 1 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 0 [mtFiber33StateAt 0]
      (mtFiber33StateAt 0) (mtFiber33StateAt 1) (by decide) h0 (by decide)
      mtFiber33ReverseSingleStep1
  have h2 : mtFiber33StateAt 13 ∈ closeChainFiber mtWord mtFiber33DirectStates 2 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 1 [mtFiber33StateAt 0]
      (mtFiber33StateAt 1) (mtFiber33StateAt 13) (by decide) h1 (by decide)
      mtFiber33ReverseSingleStep13
  change mtFiber33StateAt 13 ∈ closeChainFiber mtWord mtFiber33DirectStates (2 + 14) [mtFiber33StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber33DirectStates 2 14 [mtFiber33StateAt 0] (mtFiber33StateAt 13) h2

theorem mtFiber33State14_in_close :
    mtFiber33StateAt 14 ∈ closeChainFiber mtWord mtFiber33DirectStates mtFiber33DirectStates.length [mtFiber33StateAt 0] := by
  have h0 : mtFiber33StateAt 0 ∈ closeChainFiber mtWord mtFiber33DirectStates 0 [mtFiber33StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber33StateAt 2 ∈ closeChainFiber mtWord mtFiber33DirectStates 1 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 0 [mtFiber33StateAt 0]
      (mtFiber33StateAt 0) (mtFiber33StateAt 2) (by decide) h0 (by decide)
      mtFiber33ReverseSingleStep2
  have h2 : mtFiber33StateAt 14 ∈ closeChainFiber mtWord mtFiber33DirectStates 2 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 1 [mtFiber33StateAt 0]
      (mtFiber33StateAt 2) (mtFiber33StateAt 14) (by decide) h1 (by decide)
      mtFiber33ReverseSingleStep14
  change mtFiber33StateAt 14 ∈ closeChainFiber mtWord mtFiber33DirectStates (2 + 14) [mtFiber33StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber33DirectStates 2 14 [mtFiber33StateAt 0] (mtFiber33StateAt 14) h2

theorem mtFiber33State15_in_close :
    mtFiber33StateAt 15 ∈ closeChainFiber mtWord mtFiber33DirectStates mtFiber33DirectStates.length [mtFiber33StateAt 0] := by
  have h0 : mtFiber33StateAt 0 ∈ closeChainFiber mtWord mtFiber33DirectStates 0 [mtFiber33StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber33StateAt 1 ∈ closeChainFiber mtWord mtFiber33DirectStates 1 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 0 [mtFiber33StateAt 0]
      (mtFiber33StateAt 0) (mtFiber33StateAt 1) (by decide) h0 (by decide)
      mtFiber33ReverseSingleStep1
  have h2 : mtFiber33StateAt 3 ∈ closeChainFiber mtWord mtFiber33DirectStates 2 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 1 [mtFiber33StateAt 0]
      (mtFiber33StateAt 1) (mtFiber33StateAt 3) (by decide) h1 (by decide)
      mtFiber33ReverseSingleStep3
  have h3 : mtFiber33StateAt 15 ∈ closeChainFiber mtWord mtFiber33DirectStates 3 [mtFiber33StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber33DirectStates 2 [mtFiber33StateAt 0]
      (mtFiber33StateAt 3) (mtFiber33StateAt 15) (by decide) h2 (by decide)
      mtFiber33ReverseSingleStep15
  change mtFiber33StateAt 15 ∈ closeChainFiber mtWord mtFiber33DirectStates (3 + 13) [mtFiber33StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber33DirectStates 3 13 [mtFiber33StateAt 0] (mtFiber33StateAt 15) h3

theorem mtFiber33DirectConnected :
    chainFiberConnected mtWord mtFiber33DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber33DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber33State0_in_close
  · subst state
    exact mtFiber33State1_in_close
  · subst state
    exact mtFiber33State2_in_close
  · subst state
    exact mtFiber33State3_in_close
  · subst state
    exact mtFiber33State4_in_close
  · subst state
    exact mtFiber33State5_in_close
  · subst state
    exact mtFiber33State6_in_close
  · subst state
    exact mtFiber33State7_in_close
  · subst state
    exact mtFiber33State8_in_close
  · subst state
    exact mtFiber33State9_in_close
  · subst state
    exact mtFiber33State10_in_close
  · subst state
    exact mtFiber33State11_in_close
  · subst state
    exact mtFiber33State12_in_close
  · subst state
    exact mtFiber33State13_in_close
  · subst state
    exact mtFiber33State14_in_close
  · subst state
    exact mtFiber33State15_in_close
  · cases h
def mtFiber35StateAt (i : Nat) : List TauState :=
  directStates (mtFiber35RowAt i).sourceLeft (mtFiber35RowAt i).sourceRight

def mtFiber35DirectStates : List (List TauState) :=
  [mtFiber35StateAt 0, mtFiber35StateAt 1, mtFiber35StateAt 2, mtFiber35StateAt 3, mtFiber35StateAt 4, mtFiber35StateAt 5, mtFiber35StateAt 6, mtFiber35StateAt 7, mtFiber35StateAt 8, mtFiber35StateAt 9, mtFiber35StateAt 10, mtFiber35StateAt 11, mtFiber35StateAt 12, mtFiber35StateAt 13, mtFiber35StateAt 14, mtFiber35StateAt 15]

theorem mtFiber35ReverseRow_1_ok :
    mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber35Chunk0_ok
  change (mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 0) &&
    mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber35ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber35StateAt 0) (mtFiber35StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber35StateAt 0) (mtFiber35StateAt 1)
    (mtFiber35RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber35Key mtFiber35Expected
        (mtFiber35RowAt 1) (by decide) mtFiber35ReverseRow_1_ok
      simpa [mtFiber35StateAt, mtFiber35RowAt, mtFiber35Rows, listGetD, directRow] using h)

theorem mtFiber35ReverseRow_2_ok :
    mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber35Chunk1_ok
  change (mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 2) &&
    mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber35ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber35StateAt 0) (mtFiber35StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber35StateAt 0) (mtFiber35StateAt 2)
    (mtFiber35RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber35Key mtFiber35Expected
        (mtFiber35RowAt 2) (by decide) mtFiber35ReverseRow_2_ok
      simpa [mtFiber35StateAt, mtFiber35RowAt, mtFiber35Rows, listGetD, directRow] using h)

theorem mtFiber35ReverseRow_3_ok :
    mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber35Chunk1_ok
  change (mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 2) &&
    mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber35ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber35StateAt 1) (mtFiber35StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber35StateAt 1) (mtFiber35StateAt 3)
    (mtFiber35RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber35Key mtFiber35Expected
        (mtFiber35RowAt 3) (by decide) mtFiber35ReverseRow_3_ok
      simpa [mtFiber35StateAt, mtFiber35RowAt, mtFiber35Rows, listGetD, directRow] using h)

theorem mtFiber35ReverseRow_4_ok :
    mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber35Chunk2_ok
  change (mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 4) &&
    mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber35ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber35StateAt 0) (mtFiber35StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber35StateAt 0) (mtFiber35StateAt 4)
    (mtFiber35RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber35Key mtFiber35Expected
        (mtFiber35RowAt 4) (by decide) mtFiber35ReverseRow_4_ok
      simpa [mtFiber35StateAt, mtFiber35RowAt, mtFiber35Rows, listGetD, directRow] using h)

theorem mtFiber35ReverseRow_5_ok :
    mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber35Chunk2_ok
  change (mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 4) &&
    mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber35ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber35StateAt 1) (mtFiber35StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber35StateAt 1) (mtFiber35StateAt 5)
    (mtFiber35RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber35Key mtFiber35Expected
        (mtFiber35RowAt 5) (by decide) mtFiber35ReverseRow_5_ok
      simpa [mtFiber35StateAt, mtFiber35RowAt, mtFiber35Rows, listGetD, directRow] using h)

theorem mtFiber35ReverseRow_6_ok :
    mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber35Chunk3_ok
  change (mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 6) &&
    mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber35ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber35StateAt 2) (mtFiber35StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber35StateAt 2) (mtFiber35StateAt 6)
    (mtFiber35RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber35Key mtFiber35Expected
        (mtFiber35RowAt 6) (by decide) mtFiber35ReverseRow_6_ok
      simpa [mtFiber35StateAt, mtFiber35RowAt, mtFiber35Rows, listGetD, directRow] using h)

theorem mtFiber35ReverseRow_7_ok :
    mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber35Chunk3_ok
  change (mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 6) &&
    mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber35ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber35StateAt 3) (mtFiber35StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber35StateAt 3) (mtFiber35StateAt 7)
    (mtFiber35RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber35Key mtFiber35Expected
        (mtFiber35RowAt 7) (by decide) mtFiber35ReverseRow_7_ok
      simpa [mtFiber35StateAt, mtFiber35RowAt, mtFiber35Rows, listGetD, directRow] using h)

theorem mtFiber35ReverseRow_8_ok :
    mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber35Chunk4_ok
  change (mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 8) &&
    mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber35ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber35StateAt 4) (mtFiber35StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber35StateAt 4) (mtFiber35StateAt 8)
    (mtFiber35RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber35Key mtFiber35Expected
        (mtFiber35RowAt 8) (by decide) mtFiber35ReverseRow_8_ok
      simpa [mtFiber35StateAt, mtFiber35RowAt, mtFiber35Rows, listGetD, directRow] using h)

theorem mtFiber35ReverseRow_9_ok :
    mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber35Chunk4_ok
  change (mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 8) &&
    mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber35ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber35StateAt 5) (mtFiber35StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber35StateAt 5) (mtFiber35StateAt 9)
    (mtFiber35RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber35Key mtFiber35Expected
        (mtFiber35RowAt 9) (by decide) mtFiber35ReverseRow_9_ok
      simpa [mtFiber35StateAt, mtFiber35RowAt, mtFiber35Rows, listGetD, directRow] using h)

theorem mtFiber35ReverseRow_10_ok :
    mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber35Chunk5_ok
  change (mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 10) &&
    mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber35ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber35StateAt 6) (mtFiber35StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber35StateAt 6) (mtFiber35StateAt 10)
    (mtFiber35RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber35Key mtFiber35Expected
        (mtFiber35RowAt 10) (by decide) mtFiber35ReverseRow_10_ok
      simpa [mtFiber35StateAt, mtFiber35RowAt, mtFiber35Rows, listGetD, directRow] using h)

theorem mtFiber35ReverseRow_11_ok :
    mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber35Chunk5_ok
  change (mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 10) &&
    mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber35ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber35StateAt 7) (mtFiber35StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber35StateAt 7) (mtFiber35StateAt 11)
    (mtFiber35RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber35Key mtFiber35Expected
        (mtFiber35RowAt 11) (by decide) mtFiber35ReverseRow_11_ok
      simpa [mtFiber35StateAt, mtFiber35RowAt, mtFiber35Rows, listGetD, directRow] using h)

theorem mtFiber35ReverseRow_12_ok :
    mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber35Chunk6_ok
  change (mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 12) &&
    mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber35ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber35StateAt 0) (mtFiber35StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber35StateAt 0) (mtFiber35StateAt 12)
    (mtFiber35RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber35Key mtFiber35Expected
        (mtFiber35RowAt 12) (by decide) mtFiber35ReverseRow_12_ok
      simpa [mtFiber35StateAt, mtFiber35RowAt, mtFiber35Rows, listGetD, directRow] using h)

theorem mtFiber35ReverseRow_13_ok :
    mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber35Chunk6_ok
  change (mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 12) &&
    mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber35ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber35StateAt 1) (mtFiber35StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber35StateAt 1) (mtFiber35StateAt 13)
    (mtFiber35RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber35Key mtFiber35Expected
        (mtFiber35RowAt 13) (by decide) mtFiber35ReverseRow_13_ok
      simpa [mtFiber35StateAt, mtFiber35RowAt, mtFiber35Rows, listGetD, directRow] using h)

theorem mtFiber35ReverseRow_14_ok :
    mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber35Chunk7_ok
  change (mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 14) &&
    mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber35ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber35StateAt 2) (mtFiber35StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber35StateAt 2) (mtFiber35StateAt 14)
    (mtFiber35RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber35Key mtFiber35Expected
        (mtFiber35RowAt 14) (by decide) mtFiber35ReverseRow_14_ok
      simpa [mtFiber35StateAt, mtFiber35RowAt, mtFiber35Rows, listGetD, directRow] using h)

theorem mtFiber35ReverseRow_15_ok :
    mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber35Chunk7_ok
  change (mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 14) &&
    mtRowReverseValid mtFiber35Key mtFiber35Expected (mtFiber35RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber35ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber35StateAt 3) (mtFiber35StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber35StateAt 3) (mtFiber35StateAt 15)
    (mtFiber35RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber35Key mtFiber35Expected
        (mtFiber35RowAt 15) (by decide) mtFiber35ReverseRow_15_ok
      simpa [mtFiber35StateAt, mtFiber35RowAt, mtFiber35Rows, listGetD, directRow] using h)

theorem mtFiber35State0_in_close :
    mtFiber35StateAt 0 ∈ closeChainFiber mtWord mtFiber35DirectStates mtFiber35DirectStates.length [mtFiber35StateAt 0] := by
  change mtFiber35StateAt 0 ∈ closeChainFiber mtWord mtFiber35DirectStates 16 [mtFiber35StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber35DirectStates 0 16 [mtFiber35StateAt 0] (mtFiber35StateAt 0) (by simp [closeChainFiber])

theorem mtFiber35State1_in_close :
    mtFiber35StateAt 1 ∈ closeChainFiber mtWord mtFiber35DirectStates mtFiber35DirectStates.length [mtFiber35StateAt 0] := by
  have h0 : mtFiber35StateAt 0 ∈ closeChainFiber mtWord mtFiber35DirectStates 0 [mtFiber35StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber35StateAt 1 ∈ closeChainFiber mtWord mtFiber35DirectStates 1 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 0 [mtFiber35StateAt 0]
      (mtFiber35StateAt 0) (mtFiber35StateAt 1) (by decide) h0 (by decide)
      mtFiber35ReverseSingleStep1
  change mtFiber35StateAt 1 ∈ closeChainFiber mtWord mtFiber35DirectStates (1 + 15) [mtFiber35StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber35DirectStates 1 15 [mtFiber35StateAt 0] (mtFiber35StateAt 1) h1

theorem mtFiber35State2_in_close :
    mtFiber35StateAt 2 ∈ closeChainFiber mtWord mtFiber35DirectStates mtFiber35DirectStates.length [mtFiber35StateAt 0] := by
  have h0 : mtFiber35StateAt 0 ∈ closeChainFiber mtWord mtFiber35DirectStates 0 [mtFiber35StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber35StateAt 2 ∈ closeChainFiber mtWord mtFiber35DirectStates 1 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 0 [mtFiber35StateAt 0]
      (mtFiber35StateAt 0) (mtFiber35StateAt 2) (by decide) h0 (by decide)
      mtFiber35ReverseSingleStep2
  change mtFiber35StateAt 2 ∈ closeChainFiber mtWord mtFiber35DirectStates (1 + 15) [mtFiber35StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber35DirectStates 1 15 [mtFiber35StateAt 0] (mtFiber35StateAt 2) h1

theorem mtFiber35State3_in_close :
    mtFiber35StateAt 3 ∈ closeChainFiber mtWord mtFiber35DirectStates mtFiber35DirectStates.length [mtFiber35StateAt 0] := by
  have h0 : mtFiber35StateAt 0 ∈ closeChainFiber mtWord mtFiber35DirectStates 0 [mtFiber35StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber35StateAt 1 ∈ closeChainFiber mtWord mtFiber35DirectStates 1 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 0 [mtFiber35StateAt 0]
      (mtFiber35StateAt 0) (mtFiber35StateAt 1) (by decide) h0 (by decide)
      mtFiber35ReverseSingleStep1
  have h2 : mtFiber35StateAt 3 ∈ closeChainFiber mtWord mtFiber35DirectStates 2 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 1 [mtFiber35StateAt 0]
      (mtFiber35StateAt 1) (mtFiber35StateAt 3) (by decide) h1 (by decide)
      mtFiber35ReverseSingleStep3
  change mtFiber35StateAt 3 ∈ closeChainFiber mtWord mtFiber35DirectStates (2 + 14) [mtFiber35StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber35DirectStates 2 14 [mtFiber35StateAt 0] (mtFiber35StateAt 3) h2

theorem mtFiber35State4_in_close :
    mtFiber35StateAt 4 ∈ closeChainFiber mtWord mtFiber35DirectStates mtFiber35DirectStates.length [mtFiber35StateAt 0] := by
  have h0 : mtFiber35StateAt 0 ∈ closeChainFiber mtWord mtFiber35DirectStates 0 [mtFiber35StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber35StateAt 4 ∈ closeChainFiber mtWord mtFiber35DirectStates 1 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 0 [mtFiber35StateAt 0]
      (mtFiber35StateAt 0) (mtFiber35StateAt 4) (by decide) h0 (by decide)
      mtFiber35ReverseSingleStep4
  change mtFiber35StateAt 4 ∈ closeChainFiber mtWord mtFiber35DirectStates (1 + 15) [mtFiber35StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber35DirectStates 1 15 [mtFiber35StateAt 0] (mtFiber35StateAt 4) h1

theorem mtFiber35State5_in_close :
    mtFiber35StateAt 5 ∈ closeChainFiber mtWord mtFiber35DirectStates mtFiber35DirectStates.length [mtFiber35StateAt 0] := by
  have h0 : mtFiber35StateAt 0 ∈ closeChainFiber mtWord mtFiber35DirectStates 0 [mtFiber35StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber35StateAt 1 ∈ closeChainFiber mtWord mtFiber35DirectStates 1 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 0 [mtFiber35StateAt 0]
      (mtFiber35StateAt 0) (mtFiber35StateAt 1) (by decide) h0 (by decide)
      mtFiber35ReverseSingleStep1
  have h2 : mtFiber35StateAt 5 ∈ closeChainFiber mtWord mtFiber35DirectStates 2 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 1 [mtFiber35StateAt 0]
      (mtFiber35StateAt 1) (mtFiber35StateAt 5) (by decide) h1 (by decide)
      mtFiber35ReverseSingleStep5
  change mtFiber35StateAt 5 ∈ closeChainFiber mtWord mtFiber35DirectStates (2 + 14) [mtFiber35StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber35DirectStates 2 14 [mtFiber35StateAt 0] (mtFiber35StateAt 5) h2

theorem mtFiber35State6_in_close :
    mtFiber35StateAt 6 ∈ closeChainFiber mtWord mtFiber35DirectStates mtFiber35DirectStates.length [mtFiber35StateAt 0] := by
  have h0 : mtFiber35StateAt 0 ∈ closeChainFiber mtWord mtFiber35DirectStates 0 [mtFiber35StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber35StateAt 2 ∈ closeChainFiber mtWord mtFiber35DirectStates 1 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 0 [mtFiber35StateAt 0]
      (mtFiber35StateAt 0) (mtFiber35StateAt 2) (by decide) h0 (by decide)
      mtFiber35ReverseSingleStep2
  have h2 : mtFiber35StateAt 6 ∈ closeChainFiber mtWord mtFiber35DirectStates 2 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 1 [mtFiber35StateAt 0]
      (mtFiber35StateAt 2) (mtFiber35StateAt 6) (by decide) h1 (by decide)
      mtFiber35ReverseSingleStep6
  change mtFiber35StateAt 6 ∈ closeChainFiber mtWord mtFiber35DirectStates (2 + 14) [mtFiber35StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber35DirectStates 2 14 [mtFiber35StateAt 0] (mtFiber35StateAt 6) h2

theorem mtFiber35State7_in_close :
    mtFiber35StateAt 7 ∈ closeChainFiber mtWord mtFiber35DirectStates mtFiber35DirectStates.length [mtFiber35StateAt 0] := by
  have h0 : mtFiber35StateAt 0 ∈ closeChainFiber mtWord mtFiber35DirectStates 0 [mtFiber35StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber35StateAt 1 ∈ closeChainFiber mtWord mtFiber35DirectStates 1 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 0 [mtFiber35StateAt 0]
      (mtFiber35StateAt 0) (mtFiber35StateAt 1) (by decide) h0 (by decide)
      mtFiber35ReverseSingleStep1
  have h2 : mtFiber35StateAt 3 ∈ closeChainFiber mtWord mtFiber35DirectStates 2 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 1 [mtFiber35StateAt 0]
      (mtFiber35StateAt 1) (mtFiber35StateAt 3) (by decide) h1 (by decide)
      mtFiber35ReverseSingleStep3
  have h3 : mtFiber35StateAt 7 ∈ closeChainFiber mtWord mtFiber35DirectStates 3 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 2 [mtFiber35StateAt 0]
      (mtFiber35StateAt 3) (mtFiber35StateAt 7) (by decide) h2 (by decide)
      mtFiber35ReverseSingleStep7
  change mtFiber35StateAt 7 ∈ closeChainFiber mtWord mtFiber35DirectStates (3 + 13) [mtFiber35StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber35DirectStates 3 13 [mtFiber35StateAt 0] (mtFiber35StateAt 7) h3

theorem mtFiber35State8_in_close :
    mtFiber35StateAt 8 ∈ closeChainFiber mtWord mtFiber35DirectStates mtFiber35DirectStates.length [mtFiber35StateAt 0] := by
  have h0 : mtFiber35StateAt 0 ∈ closeChainFiber mtWord mtFiber35DirectStates 0 [mtFiber35StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber35StateAt 4 ∈ closeChainFiber mtWord mtFiber35DirectStates 1 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 0 [mtFiber35StateAt 0]
      (mtFiber35StateAt 0) (mtFiber35StateAt 4) (by decide) h0 (by decide)
      mtFiber35ReverseSingleStep4
  have h2 : mtFiber35StateAt 8 ∈ closeChainFiber mtWord mtFiber35DirectStates 2 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 1 [mtFiber35StateAt 0]
      (mtFiber35StateAt 4) (mtFiber35StateAt 8) (by decide) h1 (by decide)
      mtFiber35ReverseSingleStep8
  change mtFiber35StateAt 8 ∈ closeChainFiber mtWord mtFiber35DirectStates (2 + 14) [mtFiber35StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber35DirectStates 2 14 [mtFiber35StateAt 0] (mtFiber35StateAt 8) h2

theorem mtFiber35State9_in_close :
    mtFiber35StateAt 9 ∈ closeChainFiber mtWord mtFiber35DirectStates mtFiber35DirectStates.length [mtFiber35StateAt 0] := by
  have h0 : mtFiber35StateAt 0 ∈ closeChainFiber mtWord mtFiber35DirectStates 0 [mtFiber35StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber35StateAt 1 ∈ closeChainFiber mtWord mtFiber35DirectStates 1 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 0 [mtFiber35StateAt 0]
      (mtFiber35StateAt 0) (mtFiber35StateAt 1) (by decide) h0 (by decide)
      mtFiber35ReverseSingleStep1
  have h2 : mtFiber35StateAt 5 ∈ closeChainFiber mtWord mtFiber35DirectStates 2 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 1 [mtFiber35StateAt 0]
      (mtFiber35StateAt 1) (mtFiber35StateAt 5) (by decide) h1 (by decide)
      mtFiber35ReverseSingleStep5
  have h3 : mtFiber35StateAt 9 ∈ closeChainFiber mtWord mtFiber35DirectStates 3 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 2 [mtFiber35StateAt 0]
      (mtFiber35StateAt 5) (mtFiber35StateAt 9) (by decide) h2 (by decide)
      mtFiber35ReverseSingleStep9
  change mtFiber35StateAt 9 ∈ closeChainFiber mtWord mtFiber35DirectStates (3 + 13) [mtFiber35StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber35DirectStates 3 13 [mtFiber35StateAt 0] (mtFiber35StateAt 9) h3

theorem mtFiber35State10_in_close :
    mtFiber35StateAt 10 ∈ closeChainFiber mtWord mtFiber35DirectStates mtFiber35DirectStates.length [mtFiber35StateAt 0] := by
  have h0 : mtFiber35StateAt 0 ∈ closeChainFiber mtWord mtFiber35DirectStates 0 [mtFiber35StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber35StateAt 2 ∈ closeChainFiber mtWord mtFiber35DirectStates 1 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 0 [mtFiber35StateAt 0]
      (mtFiber35StateAt 0) (mtFiber35StateAt 2) (by decide) h0 (by decide)
      mtFiber35ReverseSingleStep2
  have h2 : mtFiber35StateAt 6 ∈ closeChainFiber mtWord mtFiber35DirectStates 2 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 1 [mtFiber35StateAt 0]
      (mtFiber35StateAt 2) (mtFiber35StateAt 6) (by decide) h1 (by decide)
      mtFiber35ReverseSingleStep6
  have h3 : mtFiber35StateAt 10 ∈ closeChainFiber mtWord mtFiber35DirectStates 3 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 2 [mtFiber35StateAt 0]
      (mtFiber35StateAt 6) (mtFiber35StateAt 10) (by decide) h2 (by decide)
      mtFiber35ReverseSingleStep10
  change mtFiber35StateAt 10 ∈ closeChainFiber mtWord mtFiber35DirectStates (3 + 13) [mtFiber35StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber35DirectStates 3 13 [mtFiber35StateAt 0] (mtFiber35StateAt 10) h3

theorem mtFiber35State11_in_close :
    mtFiber35StateAt 11 ∈ closeChainFiber mtWord mtFiber35DirectStates mtFiber35DirectStates.length [mtFiber35StateAt 0] := by
  have h0 : mtFiber35StateAt 0 ∈ closeChainFiber mtWord mtFiber35DirectStates 0 [mtFiber35StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber35StateAt 1 ∈ closeChainFiber mtWord mtFiber35DirectStates 1 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 0 [mtFiber35StateAt 0]
      (mtFiber35StateAt 0) (mtFiber35StateAt 1) (by decide) h0 (by decide)
      mtFiber35ReverseSingleStep1
  have h2 : mtFiber35StateAt 3 ∈ closeChainFiber mtWord mtFiber35DirectStates 2 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 1 [mtFiber35StateAt 0]
      (mtFiber35StateAt 1) (mtFiber35StateAt 3) (by decide) h1 (by decide)
      mtFiber35ReverseSingleStep3
  have h3 : mtFiber35StateAt 7 ∈ closeChainFiber mtWord mtFiber35DirectStates 3 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 2 [mtFiber35StateAt 0]
      (mtFiber35StateAt 3) (mtFiber35StateAt 7) (by decide) h2 (by decide)
      mtFiber35ReverseSingleStep7
  have h4 : mtFiber35StateAt 11 ∈ closeChainFiber mtWord mtFiber35DirectStates 4 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 3 [mtFiber35StateAt 0]
      (mtFiber35StateAt 7) (mtFiber35StateAt 11) (by decide) h3 (by decide)
      mtFiber35ReverseSingleStep11
  change mtFiber35StateAt 11 ∈ closeChainFiber mtWord mtFiber35DirectStates (4 + 12) [mtFiber35StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber35DirectStates 4 12 [mtFiber35StateAt 0] (mtFiber35StateAt 11) h4

theorem mtFiber35State12_in_close :
    mtFiber35StateAt 12 ∈ closeChainFiber mtWord mtFiber35DirectStates mtFiber35DirectStates.length [mtFiber35StateAt 0] := by
  have h0 : mtFiber35StateAt 0 ∈ closeChainFiber mtWord mtFiber35DirectStates 0 [mtFiber35StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber35StateAt 12 ∈ closeChainFiber mtWord mtFiber35DirectStates 1 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 0 [mtFiber35StateAt 0]
      (mtFiber35StateAt 0) (mtFiber35StateAt 12) (by decide) h0 (by decide)
      mtFiber35ReverseSingleStep12
  change mtFiber35StateAt 12 ∈ closeChainFiber mtWord mtFiber35DirectStates (1 + 15) [mtFiber35StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber35DirectStates 1 15 [mtFiber35StateAt 0] (mtFiber35StateAt 12) h1

theorem mtFiber35State13_in_close :
    mtFiber35StateAt 13 ∈ closeChainFiber mtWord mtFiber35DirectStates mtFiber35DirectStates.length [mtFiber35StateAt 0] := by
  have h0 : mtFiber35StateAt 0 ∈ closeChainFiber mtWord mtFiber35DirectStates 0 [mtFiber35StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber35StateAt 1 ∈ closeChainFiber mtWord mtFiber35DirectStates 1 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 0 [mtFiber35StateAt 0]
      (mtFiber35StateAt 0) (mtFiber35StateAt 1) (by decide) h0 (by decide)
      mtFiber35ReverseSingleStep1
  have h2 : mtFiber35StateAt 13 ∈ closeChainFiber mtWord mtFiber35DirectStates 2 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 1 [mtFiber35StateAt 0]
      (mtFiber35StateAt 1) (mtFiber35StateAt 13) (by decide) h1 (by decide)
      mtFiber35ReverseSingleStep13
  change mtFiber35StateAt 13 ∈ closeChainFiber mtWord mtFiber35DirectStates (2 + 14) [mtFiber35StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber35DirectStates 2 14 [mtFiber35StateAt 0] (mtFiber35StateAt 13) h2

theorem mtFiber35State14_in_close :
    mtFiber35StateAt 14 ∈ closeChainFiber mtWord mtFiber35DirectStates mtFiber35DirectStates.length [mtFiber35StateAt 0] := by
  have h0 : mtFiber35StateAt 0 ∈ closeChainFiber mtWord mtFiber35DirectStates 0 [mtFiber35StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber35StateAt 2 ∈ closeChainFiber mtWord mtFiber35DirectStates 1 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 0 [mtFiber35StateAt 0]
      (mtFiber35StateAt 0) (mtFiber35StateAt 2) (by decide) h0 (by decide)
      mtFiber35ReverseSingleStep2
  have h2 : mtFiber35StateAt 14 ∈ closeChainFiber mtWord mtFiber35DirectStates 2 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 1 [mtFiber35StateAt 0]
      (mtFiber35StateAt 2) (mtFiber35StateAt 14) (by decide) h1 (by decide)
      mtFiber35ReverseSingleStep14
  change mtFiber35StateAt 14 ∈ closeChainFiber mtWord mtFiber35DirectStates (2 + 14) [mtFiber35StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber35DirectStates 2 14 [mtFiber35StateAt 0] (mtFiber35StateAt 14) h2

theorem mtFiber35State15_in_close :
    mtFiber35StateAt 15 ∈ closeChainFiber mtWord mtFiber35DirectStates mtFiber35DirectStates.length [mtFiber35StateAt 0] := by
  have h0 : mtFiber35StateAt 0 ∈ closeChainFiber mtWord mtFiber35DirectStates 0 [mtFiber35StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber35StateAt 1 ∈ closeChainFiber mtWord mtFiber35DirectStates 1 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 0 [mtFiber35StateAt 0]
      (mtFiber35StateAt 0) (mtFiber35StateAt 1) (by decide) h0 (by decide)
      mtFiber35ReverseSingleStep1
  have h2 : mtFiber35StateAt 3 ∈ closeChainFiber mtWord mtFiber35DirectStates 2 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 1 [mtFiber35StateAt 0]
      (mtFiber35StateAt 1) (mtFiber35StateAt 3) (by decide) h1 (by decide)
      mtFiber35ReverseSingleStep3
  have h3 : mtFiber35StateAt 15 ∈ closeChainFiber mtWord mtFiber35DirectStates 3 [mtFiber35StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber35DirectStates 2 [mtFiber35StateAt 0]
      (mtFiber35StateAt 3) (mtFiber35StateAt 15) (by decide) h2 (by decide)
      mtFiber35ReverseSingleStep15
  change mtFiber35StateAt 15 ∈ closeChainFiber mtWord mtFiber35DirectStates (3 + 13) [mtFiber35StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber35DirectStates 3 13 [mtFiber35StateAt 0] (mtFiber35StateAt 15) h3

theorem mtFiber35DirectConnected :
    chainFiberConnected mtWord mtFiber35DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber35DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber35State0_in_close
  · subst state
    exact mtFiber35State1_in_close
  · subst state
    exact mtFiber35State2_in_close
  · subst state
    exact mtFiber35State3_in_close
  · subst state
    exact mtFiber35State4_in_close
  · subst state
    exact mtFiber35State5_in_close
  · subst state
    exact mtFiber35State6_in_close
  · subst state
    exact mtFiber35State7_in_close
  · subst state
    exact mtFiber35State8_in_close
  · subst state
    exact mtFiber35State9_in_close
  · subst state
    exact mtFiber35State10_in_close
  · subst state
    exact mtFiber35State11_in_close
  · subst state
    exact mtFiber35State12_in_close
  · subst state
    exact mtFiber35State13_in_close
  · subst state
    exact mtFiber35State14_in_close
  · subst state
    exact mtFiber35State15_in_close
  · cases h
def mtFiber37StateAt (i : Nat) : List TauState :=
  directStates (mtFiber37RowAt i).sourceLeft (mtFiber37RowAt i).sourceRight

def mtFiber37DirectStates : List (List TauState) :=
  [mtFiber37StateAt 0, mtFiber37StateAt 1, mtFiber37StateAt 2, mtFiber37StateAt 3, mtFiber37StateAt 4, mtFiber37StateAt 5, mtFiber37StateAt 6, mtFiber37StateAt 7, mtFiber37StateAt 8, mtFiber37StateAt 9, mtFiber37StateAt 10, mtFiber37StateAt 11, mtFiber37StateAt 12, mtFiber37StateAt 13, mtFiber37StateAt 14, mtFiber37StateAt 15]

theorem mtFiber37ReverseRow_1_ok :
    mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber37Chunk0_ok
  change (mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 0) &&
    mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber37ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber37StateAt 0) (mtFiber37StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber37StateAt 0) (mtFiber37StateAt 1)
    (mtFiber37RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber37Key mtFiber37Expected
        (mtFiber37RowAt 1) (by decide) mtFiber37ReverseRow_1_ok
      simpa [mtFiber37StateAt, mtFiber37RowAt, mtFiber37Rows, listGetD, directRow] using h)

theorem mtFiber37ReverseRow_2_ok :
    mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber37Chunk1_ok
  change (mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 2) &&
    mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber37ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber37StateAt 0) (mtFiber37StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber37StateAt 0) (mtFiber37StateAt 2)
    (mtFiber37RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber37Key mtFiber37Expected
        (mtFiber37RowAt 2) (by decide) mtFiber37ReverseRow_2_ok
      simpa [mtFiber37StateAt, mtFiber37RowAt, mtFiber37Rows, listGetD, directRow] using h)

theorem mtFiber37ReverseRow_3_ok :
    mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber37Chunk1_ok
  change (mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 2) &&
    mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber37ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber37StateAt 1) (mtFiber37StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber37StateAt 1) (mtFiber37StateAt 3)
    (mtFiber37RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber37Key mtFiber37Expected
        (mtFiber37RowAt 3) (by decide) mtFiber37ReverseRow_3_ok
      simpa [mtFiber37StateAt, mtFiber37RowAt, mtFiber37Rows, listGetD, directRow] using h)

theorem mtFiber37ReverseRow_4_ok :
    mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber37Chunk2_ok
  change (mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 4) &&
    mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber37ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber37StateAt 0) (mtFiber37StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber37StateAt 0) (mtFiber37StateAt 4)
    (mtFiber37RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber37Key mtFiber37Expected
        (mtFiber37RowAt 4) (by decide) mtFiber37ReverseRow_4_ok
      simpa [mtFiber37StateAt, mtFiber37RowAt, mtFiber37Rows, listGetD, directRow] using h)

theorem mtFiber37ReverseRow_5_ok :
    mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber37Chunk2_ok
  change (mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 4) &&
    mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber37ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber37StateAt 1) (mtFiber37StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber37StateAt 1) (mtFiber37StateAt 5)
    (mtFiber37RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber37Key mtFiber37Expected
        (mtFiber37RowAt 5) (by decide) mtFiber37ReverseRow_5_ok
      simpa [mtFiber37StateAt, mtFiber37RowAt, mtFiber37Rows, listGetD, directRow] using h)

theorem mtFiber37ReverseRow_6_ok :
    mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber37Chunk3_ok
  change (mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 6) &&
    mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber37ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber37StateAt 2) (mtFiber37StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber37StateAt 2) (mtFiber37StateAt 6)
    (mtFiber37RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber37Key mtFiber37Expected
        (mtFiber37RowAt 6) (by decide) mtFiber37ReverseRow_6_ok
      simpa [mtFiber37StateAt, mtFiber37RowAt, mtFiber37Rows, listGetD, directRow] using h)

theorem mtFiber37ReverseRow_7_ok :
    mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber37Chunk3_ok
  change (mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 6) &&
    mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber37ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber37StateAt 3) (mtFiber37StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber37StateAt 3) (mtFiber37StateAt 7)
    (mtFiber37RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber37Key mtFiber37Expected
        (mtFiber37RowAt 7) (by decide) mtFiber37ReverseRow_7_ok
      simpa [mtFiber37StateAt, mtFiber37RowAt, mtFiber37Rows, listGetD, directRow] using h)

theorem mtFiber37ReverseRow_8_ok :
    mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber37Chunk4_ok
  change (mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 8) &&
    mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber37ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber37StateAt 4) (mtFiber37StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber37StateAt 4) (mtFiber37StateAt 8)
    (mtFiber37RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber37Key mtFiber37Expected
        (mtFiber37RowAt 8) (by decide) mtFiber37ReverseRow_8_ok
      simpa [mtFiber37StateAt, mtFiber37RowAt, mtFiber37Rows, listGetD, directRow] using h)

theorem mtFiber37ReverseRow_9_ok :
    mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber37Chunk4_ok
  change (mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 8) &&
    mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber37ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber37StateAt 5) (mtFiber37StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber37StateAt 5) (mtFiber37StateAt 9)
    (mtFiber37RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber37Key mtFiber37Expected
        (mtFiber37RowAt 9) (by decide) mtFiber37ReverseRow_9_ok
      simpa [mtFiber37StateAt, mtFiber37RowAt, mtFiber37Rows, listGetD, directRow] using h)

theorem mtFiber37ReverseRow_10_ok :
    mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber37Chunk5_ok
  change (mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 10) &&
    mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber37ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber37StateAt 6) (mtFiber37StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber37StateAt 6) (mtFiber37StateAt 10)
    (mtFiber37RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber37Key mtFiber37Expected
        (mtFiber37RowAt 10) (by decide) mtFiber37ReverseRow_10_ok
      simpa [mtFiber37StateAt, mtFiber37RowAt, mtFiber37Rows, listGetD, directRow] using h)

theorem mtFiber37ReverseRow_11_ok :
    mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber37Chunk5_ok
  change (mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 10) &&
    mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber37ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber37StateAt 7) (mtFiber37StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber37StateAt 7) (mtFiber37StateAt 11)
    (mtFiber37RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber37Key mtFiber37Expected
        (mtFiber37RowAt 11) (by decide) mtFiber37ReverseRow_11_ok
      simpa [mtFiber37StateAt, mtFiber37RowAt, mtFiber37Rows, listGetD, directRow] using h)

theorem mtFiber37ReverseRow_12_ok :
    mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber37Chunk6_ok
  change (mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 12) &&
    mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber37ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber37StateAt 0) (mtFiber37StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber37StateAt 0) (mtFiber37StateAt 12)
    (mtFiber37RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber37Key mtFiber37Expected
        (mtFiber37RowAt 12) (by decide) mtFiber37ReverseRow_12_ok
      simpa [mtFiber37StateAt, mtFiber37RowAt, mtFiber37Rows, listGetD, directRow] using h)

theorem mtFiber37ReverseRow_13_ok :
    mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber37Chunk6_ok
  change (mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 12) &&
    mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber37ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber37StateAt 1) (mtFiber37StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber37StateAt 1) (mtFiber37StateAt 13)
    (mtFiber37RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber37Key mtFiber37Expected
        (mtFiber37RowAt 13) (by decide) mtFiber37ReverseRow_13_ok
      simpa [mtFiber37StateAt, mtFiber37RowAt, mtFiber37Rows, listGetD, directRow] using h)

theorem mtFiber37ReverseRow_14_ok :
    mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber37Chunk7_ok
  change (mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 14) &&
    mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber37ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber37StateAt 2) (mtFiber37StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber37StateAt 2) (mtFiber37StateAt 14)
    (mtFiber37RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber37Key mtFiber37Expected
        (mtFiber37RowAt 14) (by decide) mtFiber37ReverseRow_14_ok
      simpa [mtFiber37StateAt, mtFiber37RowAt, mtFiber37Rows, listGetD, directRow] using h)

theorem mtFiber37ReverseRow_15_ok :
    mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber37Chunk7_ok
  change (mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 14) &&
    mtRowReverseValid mtFiber37Key mtFiber37Expected (mtFiber37RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber37ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber37StateAt 3) (mtFiber37StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber37StateAt 3) (mtFiber37StateAt 15)
    (mtFiber37RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber37Key mtFiber37Expected
        (mtFiber37RowAt 15) (by decide) mtFiber37ReverseRow_15_ok
      simpa [mtFiber37StateAt, mtFiber37RowAt, mtFiber37Rows, listGetD, directRow] using h)

theorem mtFiber37State0_in_close :
    mtFiber37StateAt 0 ∈ closeChainFiber mtWord mtFiber37DirectStates mtFiber37DirectStates.length [mtFiber37StateAt 0] := by
  change mtFiber37StateAt 0 ∈ closeChainFiber mtWord mtFiber37DirectStates 16 [mtFiber37StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber37DirectStates 0 16 [mtFiber37StateAt 0] (mtFiber37StateAt 0) (by simp [closeChainFiber])

theorem mtFiber37State1_in_close :
    mtFiber37StateAt 1 ∈ closeChainFiber mtWord mtFiber37DirectStates mtFiber37DirectStates.length [mtFiber37StateAt 0] := by
  have h0 : mtFiber37StateAt 0 ∈ closeChainFiber mtWord mtFiber37DirectStates 0 [mtFiber37StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber37StateAt 1 ∈ closeChainFiber mtWord mtFiber37DirectStates 1 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 0 [mtFiber37StateAt 0]
      (mtFiber37StateAt 0) (mtFiber37StateAt 1) (by decide) h0 (by decide)
      mtFiber37ReverseSingleStep1
  change mtFiber37StateAt 1 ∈ closeChainFiber mtWord mtFiber37DirectStates (1 + 15) [mtFiber37StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber37DirectStates 1 15 [mtFiber37StateAt 0] (mtFiber37StateAt 1) h1

theorem mtFiber37State2_in_close :
    mtFiber37StateAt 2 ∈ closeChainFiber mtWord mtFiber37DirectStates mtFiber37DirectStates.length [mtFiber37StateAt 0] := by
  have h0 : mtFiber37StateAt 0 ∈ closeChainFiber mtWord mtFiber37DirectStates 0 [mtFiber37StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber37StateAt 2 ∈ closeChainFiber mtWord mtFiber37DirectStates 1 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 0 [mtFiber37StateAt 0]
      (mtFiber37StateAt 0) (mtFiber37StateAt 2) (by decide) h0 (by decide)
      mtFiber37ReverseSingleStep2
  change mtFiber37StateAt 2 ∈ closeChainFiber mtWord mtFiber37DirectStates (1 + 15) [mtFiber37StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber37DirectStates 1 15 [mtFiber37StateAt 0] (mtFiber37StateAt 2) h1

theorem mtFiber37State3_in_close :
    mtFiber37StateAt 3 ∈ closeChainFiber mtWord mtFiber37DirectStates mtFiber37DirectStates.length [mtFiber37StateAt 0] := by
  have h0 : mtFiber37StateAt 0 ∈ closeChainFiber mtWord mtFiber37DirectStates 0 [mtFiber37StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber37StateAt 1 ∈ closeChainFiber mtWord mtFiber37DirectStates 1 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 0 [mtFiber37StateAt 0]
      (mtFiber37StateAt 0) (mtFiber37StateAt 1) (by decide) h0 (by decide)
      mtFiber37ReverseSingleStep1
  have h2 : mtFiber37StateAt 3 ∈ closeChainFiber mtWord mtFiber37DirectStates 2 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 1 [mtFiber37StateAt 0]
      (mtFiber37StateAt 1) (mtFiber37StateAt 3) (by decide) h1 (by decide)
      mtFiber37ReverseSingleStep3
  change mtFiber37StateAt 3 ∈ closeChainFiber mtWord mtFiber37DirectStates (2 + 14) [mtFiber37StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber37DirectStates 2 14 [mtFiber37StateAt 0] (mtFiber37StateAt 3) h2

theorem mtFiber37State4_in_close :
    mtFiber37StateAt 4 ∈ closeChainFiber mtWord mtFiber37DirectStates mtFiber37DirectStates.length [mtFiber37StateAt 0] := by
  have h0 : mtFiber37StateAt 0 ∈ closeChainFiber mtWord mtFiber37DirectStates 0 [mtFiber37StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber37StateAt 4 ∈ closeChainFiber mtWord mtFiber37DirectStates 1 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 0 [mtFiber37StateAt 0]
      (mtFiber37StateAt 0) (mtFiber37StateAt 4) (by decide) h0 (by decide)
      mtFiber37ReverseSingleStep4
  change mtFiber37StateAt 4 ∈ closeChainFiber mtWord mtFiber37DirectStates (1 + 15) [mtFiber37StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber37DirectStates 1 15 [mtFiber37StateAt 0] (mtFiber37StateAt 4) h1

theorem mtFiber37State5_in_close :
    mtFiber37StateAt 5 ∈ closeChainFiber mtWord mtFiber37DirectStates mtFiber37DirectStates.length [mtFiber37StateAt 0] := by
  have h0 : mtFiber37StateAt 0 ∈ closeChainFiber mtWord mtFiber37DirectStates 0 [mtFiber37StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber37StateAt 1 ∈ closeChainFiber mtWord mtFiber37DirectStates 1 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 0 [mtFiber37StateAt 0]
      (mtFiber37StateAt 0) (mtFiber37StateAt 1) (by decide) h0 (by decide)
      mtFiber37ReverseSingleStep1
  have h2 : mtFiber37StateAt 5 ∈ closeChainFiber mtWord mtFiber37DirectStates 2 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 1 [mtFiber37StateAt 0]
      (mtFiber37StateAt 1) (mtFiber37StateAt 5) (by decide) h1 (by decide)
      mtFiber37ReverseSingleStep5
  change mtFiber37StateAt 5 ∈ closeChainFiber mtWord mtFiber37DirectStates (2 + 14) [mtFiber37StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber37DirectStates 2 14 [mtFiber37StateAt 0] (mtFiber37StateAt 5) h2

theorem mtFiber37State6_in_close :
    mtFiber37StateAt 6 ∈ closeChainFiber mtWord mtFiber37DirectStates mtFiber37DirectStates.length [mtFiber37StateAt 0] := by
  have h0 : mtFiber37StateAt 0 ∈ closeChainFiber mtWord mtFiber37DirectStates 0 [mtFiber37StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber37StateAt 2 ∈ closeChainFiber mtWord mtFiber37DirectStates 1 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 0 [mtFiber37StateAt 0]
      (mtFiber37StateAt 0) (mtFiber37StateAt 2) (by decide) h0 (by decide)
      mtFiber37ReverseSingleStep2
  have h2 : mtFiber37StateAt 6 ∈ closeChainFiber mtWord mtFiber37DirectStates 2 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 1 [mtFiber37StateAt 0]
      (mtFiber37StateAt 2) (mtFiber37StateAt 6) (by decide) h1 (by decide)
      mtFiber37ReverseSingleStep6
  change mtFiber37StateAt 6 ∈ closeChainFiber mtWord mtFiber37DirectStates (2 + 14) [mtFiber37StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber37DirectStates 2 14 [mtFiber37StateAt 0] (mtFiber37StateAt 6) h2

theorem mtFiber37State7_in_close :
    mtFiber37StateAt 7 ∈ closeChainFiber mtWord mtFiber37DirectStates mtFiber37DirectStates.length [mtFiber37StateAt 0] := by
  have h0 : mtFiber37StateAt 0 ∈ closeChainFiber mtWord mtFiber37DirectStates 0 [mtFiber37StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber37StateAt 1 ∈ closeChainFiber mtWord mtFiber37DirectStates 1 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 0 [mtFiber37StateAt 0]
      (mtFiber37StateAt 0) (mtFiber37StateAt 1) (by decide) h0 (by decide)
      mtFiber37ReverseSingleStep1
  have h2 : mtFiber37StateAt 3 ∈ closeChainFiber mtWord mtFiber37DirectStates 2 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 1 [mtFiber37StateAt 0]
      (mtFiber37StateAt 1) (mtFiber37StateAt 3) (by decide) h1 (by decide)
      mtFiber37ReverseSingleStep3
  have h3 : mtFiber37StateAt 7 ∈ closeChainFiber mtWord mtFiber37DirectStates 3 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 2 [mtFiber37StateAt 0]
      (mtFiber37StateAt 3) (mtFiber37StateAt 7) (by decide) h2 (by decide)
      mtFiber37ReverseSingleStep7
  change mtFiber37StateAt 7 ∈ closeChainFiber mtWord mtFiber37DirectStates (3 + 13) [mtFiber37StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber37DirectStates 3 13 [mtFiber37StateAt 0] (mtFiber37StateAt 7) h3

theorem mtFiber37State8_in_close :
    mtFiber37StateAt 8 ∈ closeChainFiber mtWord mtFiber37DirectStates mtFiber37DirectStates.length [mtFiber37StateAt 0] := by
  have h0 : mtFiber37StateAt 0 ∈ closeChainFiber mtWord mtFiber37DirectStates 0 [mtFiber37StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber37StateAt 4 ∈ closeChainFiber mtWord mtFiber37DirectStates 1 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 0 [mtFiber37StateAt 0]
      (mtFiber37StateAt 0) (mtFiber37StateAt 4) (by decide) h0 (by decide)
      mtFiber37ReverseSingleStep4
  have h2 : mtFiber37StateAt 8 ∈ closeChainFiber mtWord mtFiber37DirectStates 2 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 1 [mtFiber37StateAt 0]
      (mtFiber37StateAt 4) (mtFiber37StateAt 8) (by decide) h1 (by decide)
      mtFiber37ReverseSingleStep8
  change mtFiber37StateAt 8 ∈ closeChainFiber mtWord mtFiber37DirectStates (2 + 14) [mtFiber37StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber37DirectStates 2 14 [mtFiber37StateAt 0] (mtFiber37StateAt 8) h2

theorem mtFiber37State9_in_close :
    mtFiber37StateAt 9 ∈ closeChainFiber mtWord mtFiber37DirectStates mtFiber37DirectStates.length [mtFiber37StateAt 0] := by
  have h0 : mtFiber37StateAt 0 ∈ closeChainFiber mtWord mtFiber37DirectStates 0 [mtFiber37StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber37StateAt 1 ∈ closeChainFiber mtWord mtFiber37DirectStates 1 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 0 [mtFiber37StateAt 0]
      (mtFiber37StateAt 0) (mtFiber37StateAt 1) (by decide) h0 (by decide)
      mtFiber37ReverseSingleStep1
  have h2 : mtFiber37StateAt 5 ∈ closeChainFiber mtWord mtFiber37DirectStates 2 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 1 [mtFiber37StateAt 0]
      (mtFiber37StateAt 1) (mtFiber37StateAt 5) (by decide) h1 (by decide)
      mtFiber37ReverseSingleStep5
  have h3 : mtFiber37StateAt 9 ∈ closeChainFiber mtWord mtFiber37DirectStates 3 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 2 [mtFiber37StateAt 0]
      (mtFiber37StateAt 5) (mtFiber37StateAt 9) (by decide) h2 (by decide)
      mtFiber37ReverseSingleStep9
  change mtFiber37StateAt 9 ∈ closeChainFiber mtWord mtFiber37DirectStates (3 + 13) [mtFiber37StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber37DirectStates 3 13 [mtFiber37StateAt 0] (mtFiber37StateAt 9) h3

theorem mtFiber37State10_in_close :
    mtFiber37StateAt 10 ∈ closeChainFiber mtWord mtFiber37DirectStates mtFiber37DirectStates.length [mtFiber37StateAt 0] := by
  have h0 : mtFiber37StateAt 0 ∈ closeChainFiber mtWord mtFiber37DirectStates 0 [mtFiber37StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber37StateAt 2 ∈ closeChainFiber mtWord mtFiber37DirectStates 1 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 0 [mtFiber37StateAt 0]
      (mtFiber37StateAt 0) (mtFiber37StateAt 2) (by decide) h0 (by decide)
      mtFiber37ReverseSingleStep2
  have h2 : mtFiber37StateAt 6 ∈ closeChainFiber mtWord mtFiber37DirectStates 2 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 1 [mtFiber37StateAt 0]
      (mtFiber37StateAt 2) (mtFiber37StateAt 6) (by decide) h1 (by decide)
      mtFiber37ReverseSingleStep6
  have h3 : mtFiber37StateAt 10 ∈ closeChainFiber mtWord mtFiber37DirectStates 3 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 2 [mtFiber37StateAt 0]
      (mtFiber37StateAt 6) (mtFiber37StateAt 10) (by decide) h2 (by decide)
      mtFiber37ReverseSingleStep10
  change mtFiber37StateAt 10 ∈ closeChainFiber mtWord mtFiber37DirectStates (3 + 13) [mtFiber37StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber37DirectStates 3 13 [mtFiber37StateAt 0] (mtFiber37StateAt 10) h3

theorem mtFiber37State11_in_close :
    mtFiber37StateAt 11 ∈ closeChainFiber mtWord mtFiber37DirectStates mtFiber37DirectStates.length [mtFiber37StateAt 0] := by
  have h0 : mtFiber37StateAt 0 ∈ closeChainFiber mtWord mtFiber37DirectStates 0 [mtFiber37StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber37StateAt 1 ∈ closeChainFiber mtWord mtFiber37DirectStates 1 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 0 [mtFiber37StateAt 0]
      (mtFiber37StateAt 0) (mtFiber37StateAt 1) (by decide) h0 (by decide)
      mtFiber37ReverseSingleStep1
  have h2 : mtFiber37StateAt 3 ∈ closeChainFiber mtWord mtFiber37DirectStates 2 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 1 [mtFiber37StateAt 0]
      (mtFiber37StateAt 1) (mtFiber37StateAt 3) (by decide) h1 (by decide)
      mtFiber37ReverseSingleStep3
  have h3 : mtFiber37StateAt 7 ∈ closeChainFiber mtWord mtFiber37DirectStates 3 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 2 [mtFiber37StateAt 0]
      (mtFiber37StateAt 3) (mtFiber37StateAt 7) (by decide) h2 (by decide)
      mtFiber37ReverseSingleStep7
  have h4 : mtFiber37StateAt 11 ∈ closeChainFiber mtWord mtFiber37DirectStates 4 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 3 [mtFiber37StateAt 0]
      (mtFiber37StateAt 7) (mtFiber37StateAt 11) (by decide) h3 (by decide)
      mtFiber37ReverseSingleStep11
  change mtFiber37StateAt 11 ∈ closeChainFiber mtWord mtFiber37DirectStates (4 + 12) [mtFiber37StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber37DirectStates 4 12 [mtFiber37StateAt 0] (mtFiber37StateAt 11) h4

theorem mtFiber37State12_in_close :
    mtFiber37StateAt 12 ∈ closeChainFiber mtWord mtFiber37DirectStates mtFiber37DirectStates.length [mtFiber37StateAt 0] := by
  have h0 : mtFiber37StateAt 0 ∈ closeChainFiber mtWord mtFiber37DirectStates 0 [mtFiber37StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber37StateAt 12 ∈ closeChainFiber mtWord mtFiber37DirectStates 1 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 0 [mtFiber37StateAt 0]
      (mtFiber37StateAt 0) (mtFiber37StateAt 12) (by decide) h0 (by decide)
      mtFiber37ReverseSingleStep12
  change mtFiber37StateAt 12 ∈ closeChainFiber mtWord mtFiber37DirectStates (1 + 15) [mtFiber37StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber37DirectStates 1 15 [mtFiber37StateAt 0] (mtFiber37StateAt 12) h1

theorem mtFiber37State13_in_close :
    mtFiber37StateAt 13 ∈ closeChainFiber mtWord mtFiber37DirectStates mtFiber37DirectStates.length [mtFiber37StateAt 0] := by
  have h0 : mtFiber37StateAt 0 ∈ closeChainFiber mtWord mtFiber37DirectStates 0 [mtFiber37StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber37StateAt 1 ∈ closeChainFiber mtWord mtFiber37DirectStates 1 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 0 [mtFiber37StateAt 0]
      (mtFiber37StateAt 0) (mtFiber37StateAt 1) (by decide) h0 (by decide)
      mtFiber37ReverseSingleStep1
  have h2 : mtFiber37StateAt 13 ∈ closeChainFiber mtWord mtFiber37DirectStates 2 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 1 [mtFiber37StateAt 0]
      (mtFiber37StateAt 1) (mtFiber37StateAt 13) (by decide) h1 (by decide)
      mtFiber37ReverseSingleStep13
  change mtFiber37StateAt 13 ∈ closeChainFiber mtWord mtFiber37DirectStates (2 + 14) [mtFiber37StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber37DirectStates 2 14 [mtFiber37StateAt 0] (mtFiber37StateAt 13) h2

theorem mtFiber37State14_in_close :
    mtFiber37StateAt 14 ∈ closeChainFiber mtWord mtFiber37DirectStates mtFiber37DirectStates.length [mtFiber37StateAt 0] := by
  have h0 : mtFiber37StateAt 0 ∈ closeChainFiber mtWord mtFiber37DirectStates 0 [mtFiber37StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber37StateAt 2 ∈ closeChainFiber mtWord mtFiber37DirectStates 1 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 0 [mtFiber37StateAt 0]
      (mtFiber37StateAt 0) (mtFiber37StateAt 2) (by decide) h0 (by decide)
      mtFiber37ReverseSingleStep2
  have h2 : mtFiber37StateAt 14 ∈ closeChainFiber mtWord mtFiber37DirectStates 2 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 1 [mtFiber37StateAt 0]
      (mtFiber37StateAt 2) (mtFiber37StateAt 14) (by decide) h1 (by decide)
      mtFiber37ReverseSingleStep14
  change mtFiber37StateAt 14 ∈ closeChainFiber mtWord mtFiber37DirectStates (2 + 14) [mtFiber37StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber37DirectStates 2 14 [mtFiber37StateAt 0] (mtFiber37StateAt 14) h2

theorem mtFiber37State15_in_close :
    mtFiber37StateAt 15 ∈ closeChainFiber mtWord mtFiber37DirectStates mtFiber37DirectStates.length [mtFiber37StateAt 0] := by
  have h0 : mtFiber37StateAt 0 ∈ closeChainFiber mtWord mtFiber37DirectStates 0 [mtFiber37StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber37StateAt 1 ∈ closeChainFiber mtWord mtFiber37DirectStates 1 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 0 [mtFiber37StateAt 0]
      (mtFiber37StateAt 0) (mtFiber37StateAt 1) (by decide) h0 (by decide)
      mtFiber37ReverseSingleStep1
  have h2 : mtFiber37StateAt 3 ∈ closeChainFiber mtWord mtFiber37DirectStates 2 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 1 [mtFiber37StateAt 0]
      (mtFiber37StateAt 1) (mtFiber37StateAt 3) (by decide) h1 (by decide)
      mtFiber37ReverseSingleStep3
  have h3 : mtFiber37StateAt 15 ∈ closeChainFiber mtWord mtFiber37DirectStates 3 [mtFiber37StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber37DirectStates 2 [mtFiber37StateAt 0]
      (mtFiber37StateAt 3) (mtFiber37StateAt 15) (by decide) h2 (by decide)
      mtFiber37ReverseSingleStep15
  change mtFiber37StateAt 15 ∈ closeChainFiber mtWord mtFiber37DirectStates (3 + 13) [mtFiber37StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber37DirectStates 3 13 [mtFiber37StateAt 0] (mtFiber37StateAt 15) h3

theorem mtFiber37DirectConnected :
    chainFiberConnected mtWord mtFiber37DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber37DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber37State0_in_close
  · subst state
    exact mtFiber37State1_in_close
  · subst state
    exact mtFiber37State2_in_close
  · subst state
    exact mtFiber37State3_in_close
  · subst state
    exact mtFiber37State4_in_close
  · subst state
    exact mtFiber37State5_in_close
  · subst state
    exact mtFiber37State6_in_close
  · subst state
    exact mtFiber37State7_in_close
  · subst state
    exact mtFiber37State8_in_close
  · subst state
    exact mtFiber37State9_in_close
  · subst state
    exact mtFiber37State10_in_close
  · subst state
    exact mtFiber37State11_in_close
  · subst state
    exact mtFiber37State12_in_close
  · subst state
    exact mtFiber37State13_in_close
  · subst state
    exact mtFiber37State14_in_close
  · subst state
    exact mtFiber37State15_in_close
  · cases h
end GoertzelLemma818LengthTwoMTBridge

end Mettapedia.GraphTheory.FourColor
