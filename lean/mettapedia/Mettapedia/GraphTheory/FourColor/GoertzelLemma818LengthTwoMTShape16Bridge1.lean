import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for size-16 `mirror,normal` length-two fibers, group 1

This module proves direct connectedness for generated `mirror,normal` size-16 fibers from row-local reverse certificate chunks.
-/

namespace GoertzelLemma818LengthTwoMTBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorTauCertificate
open GoertzelLemma818MirrorTauReverseAudit

def mtFiber17StateAt (i : Nat) : List TauState :=
  directStates (mtFiber17RowAt i).sourceLeft (mtFiber17RowAt i).sourceRight

def mtFiber17DirectStates : List (List TauState) :=
  [mtFiber17StateAt 0, mtFiber17StateAt 1, mtFiber17StateAt 2, mtFiber17StateAt 3, mtFiber17StateAt 4, mtFiber17StateAt 5, mtFiber17StateAt 6, mtFiber17StateAt 7, mtFiber17StateAt 8, mtFiber17StateAt 9, mtFiber17StateAt 10, mtFiber17StateAt 11, mtFiber17StateAt 12, mtFiber17StateAt 13, mtFiber17StateAt 14, mtFiber17StateAt 15]

theorem mtFiber17ReverseRow_1_ok :
    mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber17Chunk0_ok
  change (mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 0) &&
    mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber17ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber17StateAt 0) (mtFiber17StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber17StateAt 0) (mtFiber17StateAt 1)
    (mtFiber17RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber17Key mtFiber17Expected
        (mtFiber17RowAt 1) (by decide) mtFiber17ReverseRow_1_ok
      simpa [mtFiber17StateAt, mtFiber17RowAt, mtFiber17Rows, listGetD, directRow] using h)

theorem mtFiber17ReverseRow_2_ok :
    mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber17Chunk1_ok
  change (mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 2) &&
    mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber17ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber17StateAt 1) (mtFiber17StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber17StateAt 1) (mtFiber17StateAt 2)
    (mtFiber17RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber17Key mtFiber17Expected
        (mtFiber17RowAt 2) (by decide) mtFiber17ReverseRow_2_ok
      simpa [mtFiber17StateAt, mtFiber17RowAt, mtFiber17Rows, listGetD, directRow] using h)

theorem mtFiber17ReverseRow_3_ok :
    mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber17Chunk1_ok
  change (mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 2) &&
    mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber17ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber17StateAt 0) (mtFiber17StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber17StateAt 0) (mtFiber17StateAt 3)
    (mtFiber17RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber17Key mtFiber17Expected
        (mtFiber17RowAt 3) (by decide) mtFiber17ReverseRow_3_ok
      simpa [mtFiber17StateAt, mtFiber17RowAt, mtFiber17Rows, listGetD, directRow] using h)

theorem mtFiber17ReverseRow_4_ok :
    mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber17Chunk2_ok
  change (mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 4) &&
    mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber17ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber17StateAt 0) (mtFiber17StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber17StateAt 0) (mtFiber17StateAt 4)
    (mtFiber17RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber17Key mtFiber17Expected
        (mtFiber17RowAt 4) (by decide) mtFiber17ReverseRow_4_ok
      simpa [mtFiber17StateAt, mtFiber17RowAt, mtFiber17Rows, listGetD, directRow] using h)

theorem mtFiber17ReverseRow_5_ok :
    mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber17Chunk2_ok
  change (mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 4) &&
    mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber17ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber17StateAt 1) (mtFiber17StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber17StateAt 1) (mtFiber17StateAt 5)
    (mtFiber17RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber17Key mtFiber17Expected
        (mtFiber17RowAt 5) (by decide) mtFiber17ReverseRow_5_ok
      simpa [mtFiber17StateAt, mtFiber17RowAt, mtFiber17Rows, listGetD, directRow] using h)

theorem mtFiber17ReverseRow_6_ok :
    mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber17Chunk3_ok
  change (mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 6) &&
    mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber17ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber17StateAt 2) (mtFiber17StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber17StateAt 2) (mtFiber17StateAt 6)
    (mtFiber17RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber17Key mtFiber17Expected
        (mtFiber17RowAt 6) (by decide) mtFiber17ReverseRow_6_ok
      simpa [mtFiber17StateAt, mtFiber17RowAt, mtFiber17Rows, listGetD, directRow] using h)

theorem mtFiber17ReverseRow_7_ok :
    mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber17Chunk3_ok
  change (mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 6) &&
    mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber17ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber17StateAt 3) (mtFiber17StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber17StateAt 3) (mtFiber17StateAt 7)
    (mtFiber17RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber17Key mtFiber17Expected
        (mtFiber17RowAt 7) (by decide) mtFiber17ReverseRow_7_ok
      simpa [mtFiber17StateAt, mtFiber17RowAt, mtFiber17Rows, listGetD, directRow] using h)

theorem mtFiber17ReverseRow_8_ok :
    mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber17Chunk4_ok
  change (mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 8) &&
    mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber17ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber17StateAt 0) (mtFiber17StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber17StateAt 0) (mtFiber17StateAt 8)
    (mtFiber17RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber17Key mtFiber17Expected
        (mtFiber17RowAt 8) (by decide) mtFiber17ReverseRow_8_ok
      simpa [mtFiber17StateAt, mtFiber17RowAt, mtFiber17Rows, listGetD, directRow] using h)

theorem mtFiber17ReverseRow_9_ok :
    mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber17Chunk4_ok
  change (mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 8) &&
    mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber17ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber17StateAt 1) (mtFiber17StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber17StateAt 1) (mtFiber17StateAt 9)
    (mtFiber17RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber17Key mtFiber17Expected
        (mtFiber17RowAt 9) (by decide) mtFiber17ReverseRow_9_ok
      simpa [mtFiber17StateAt, mtFiber17RowAt, mtFiber17Rows, listGetD, directRow] using h)

theorem mtFiber17ReverseRow_10_ok :
    mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber17Chunk5_ok
  change (mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 10) &&
    mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber17ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber17StateAt 2) (mtFiber17StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber17StateAt 2) (mtFiber17StateAt 10)
    (mtFiber17RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber17Key mtFiber17Expected
        (mtFiber17RowAt 10) (by decide) mtFiber17ReverseRow_10_ok
      simpa [mtFiber17StateAt, mtFiber17RowAt, mtFiber17Rows, listGetD, directRow] using h)

theorem mtFiber17ReverseRow_11_ok :
    mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber17Chunk5_ok
  change (mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 10) &&
    mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber17ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber17StateAt 3) (mtFiber17StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber17StateAt 3) (mtFiber17StateAt 11)
    (mtFiber17RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber17Key mtFiber17Expected
        (mtFiber17RowAt 11) (by decide) mtFiber17ReverseRow_11_ok
      simpa [mtFiber17StateAt, mtFiber17RowAt, mtFiber17Rows, listGetD, directRow] using h)

theorem mtFiber17ReverseRow_12_ok :
    mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber17Chunk6_ok
  change (mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 12) &&
    mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber17ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber17StateAt 4) (mtFiber17StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber17StateAt 4) (mtFiber17StateAt 12)
    (mtFiber17RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber17Key mtFiber17Expected
        (mtFiber17RowAt 12) (by decide) mtFiber17ReverseRow_12_ok
      simpa [mtFiber17StateAt, mtFiber17RowAt, mtFiber17Rows, listGetD, directRow] using h)

theorem mtFiber17ReverseRow_13_ok :
    mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber17Chunk6_ok
  change (mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 12) &&
    mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber17ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber17StateAt 5) (mtFiber17StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber17StateAt 5) (mtFiber17StateAt 13)
    (mtFiber17RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber17Key mtFiber17Expected
        (mtFiber17RowAt 13) (by decide) mtFiber17ReverseRow_13_ok
      simpa [mtFiber17StateAt, mtFiber17RowAt, mtFiber17Rows, listGetD, directRow] using h)

theorem mtFiber17ReverseRow_14_ok :
    mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber17Chunk7_ok
  change (mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 14) &&
    mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber17ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber17StateAt 6) (mtFiber17StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber17StateAt 6) (mtFiber17StateAt 14)
    (mtFiber17RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber17Key mtFiber17Expected
        (mtFiber17RowAt 14) (by decide) mtFiber17ReverseRow_14_ok
      simpa [mtFiber17StateAt, mtFiber17RowAt, mtFiber17Rows, listGetD, directRow] using h)

theorem mtFiber17ReverseRow_15_ok :
    mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber17Chunk7_ok
  change (mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 14) &&
    mtRowReverseValid mtFiber17Key mtFiber17Expected (mtFiber17RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber17ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber17StateAt 7) (mtFiber17StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber17StateAt 7) (mtFiber17StateAt 15)
    (mtFiber17RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber17Key mtFiber17Expected
        (mtFiber17RowAt 15) (by decide) mtFiber17ReverseRow_15_ok
      simpa [mtFiber17StateAt, mtFiber17RowAt, mtFiber17Rows, listGetD, directRow] using h)

theorem mtFiber17State0_in_close :
    mtFiber17StateAt 0 ∈ closeChainFiber mtWord mtFiber17DirectStates mtFiber17DirectStates.length [mtFiber17StateAt 0] := by
  change mtFiber17StateAt 0 ∈ closeChainFiber mtWord mtFiber17DirectStates 16 [mtFiber17StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber17DirectStates 0 16 [mtFiber17StateAt 0] (mtFiber17StateAt 0) (by simp [closeChainFiber])

theorem mtFiber17State1_in_close :
    mtFiber17StateAt 1 ∈ closeChainFiber mtWord mtFiber17DirectStates mtFiber17DirectStates.length [mtFiber17StateAt 0] := by
  have h0 : mtFiber17StateAt 0 ∈ closeChainFiber mtWord mtFiber17DirectStates 0 [mtFiber17StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber17StateAt 1 ∈ closeChainFiber mtWord mtFiber17DirectStates 1 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 0 [mtFiber17StateAt 0]
      (mtFiber17StateAt 0) (mtFiber17StateAt 1) (by decide) h0 (by decide)
      mtFiber17ReverseSingleStep1
  change mtFiber17StateAt 1 ∈ closeChainFiber mtWord mtFiber17DirectStates (1 + 15) [mtFiber17StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber17DirectStates 1 15 [mtFiber17StateAt 0] (mtFiber17StateAt 1) h1

theorem mtFiber17State2_in_close :
    mtFiber17StateAt 2 ∈ closeChainFiber mtWord mtFiber17DirectStates mtFiber17DirectStates.length [mtFiber17StateAt 0] := by
  have h0 : mtFiber17StateAt 0 ∈ closeChainFiber mtWord mtFiber17DirectStates 0 [mtFiber17StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber17StateAt 1 ∈ closeChainFiber mtWord mtFiber17DirectStates 1 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 0 [mtFiber17StateAt 0]
      (mtFiber17StateAt 0) (mtFiber17StateAt 1) (by decide) h0 (by decide)
      mtFiber17ReverseSingleStep1
  have h2 : mtFiber17StateAt 2 ∈ closeChainFiber mtWord mtFiber17DirectStates 2 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 1 [mtFiber17StateAt 0]
      (mtFiber17StateAt 1) (mtFiber17StateAt 2) (by decide) h1 (by decide)
      mtFiber17ReverseSingleStep2
  change mtFiber17StateAt 2 ∈ closeChainFiber mtWord mtFiber17DirectStates (2 + 14) [mtFiber17StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber17DirectStates 2 14 [mtFiber17StateAt 0] (mtFiber17StateAt 2) h2

theorem mtFiber17State3_in_close :
    mtFiber17StateAt 3 ∈ closeChainFiber mtWord mtFiber17DirectStates mtFiber17DirectStates.length [mtFiber17StateAt 0] := by
  have h0 : mtFiber17StateAt 0 ∈ closeChainFiber mtWord mtFiber17DirectStates 0 [mtFiber17StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber17StateAt 3 ∈ closeChainFiber mtWord mtFiber17DirectStates 1 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 0 [mtFiber17StateAt 0]
      (mtFiber17StateAt 0) (mtFiber17StateAt 3) (by decide) h0 (by decide)
      mtFiber17ReverseSingleStep3
  change mtFiber17StateAt 3 ∈ closeChainFiber mtWord mtFiber17DirectStates (1 + 15) [mtFiber17StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber17DirectStates 1 15 [mtFiber17StateAt 0] (mtFiber17StateAt 3) h1

theorem mtFiber17State4_in_close :
    mtFiber17StateAt 4 ∈ closeChainFiber mtWord mtFiber17DirectStates mtFiber17DirectStates.length [mtFiber17StateAt 0] := by
  have h0 : mtFiber17StateAt 0 ∈ closeChainFiber mtWord mtFiber17DirectStates 0 [mtFiber17StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber17StateAt 4 ∈ closeChainFiber mtWord mtFiber17DirectStates 1 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 0 [mtFiber17StateAt 0]
      (mtFiber17StateAt 0) (mtFiber17StateAt 4) (by decide) h0 (by decide)
      mtFiber17ReverseSingleStep4
  change mtFiber17StateAt 4 ∈ closeChainFiber mtWord mtFiber17DirectStates (1 + 15) [mtFiber17StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber17DirectStates 1 15 [mtFiber17StateAt 0] (mtFiber17StateAt 4) h1

theorem mtFiber17State5_in_close :
    mtFiber17StateAt 5 ∈ closeChainFiber mtWord mtFiber17DirectStates mtFiber17DirectStates.length [mtFiber17StateAt 0] := by
  have h0 : mtFiber17StateAt 0 ∈ closeChainFiber mtWord mtFiber17DirectStates 0 [mtFiber17StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber17StateAt 1 ∈ closeChainFiber mtWord mtFiber17DirectStates 1 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 0 [mtFiber17StateAt 0]
      (mtFiber17StateAt 0) (mtFiber17StateAt 1) (by decide) h0 (by decide)
      mtFiber17ReverseSingleStep1
  have h2 : mtFiber17StateAt 5 ∈ closeChainFiber mtWord mtFiber17DirectStates 2 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 1 [mtFiber17StateAt 0]
      (mtFiber17StateAt 1) (mtFiber17StateAt 5) (by decide) h1 (by decide)
      mtFiber17ReverseSingleStep5
  change mtFiber17StateAt 5 ∈ closeChainFiber mtWord mtFiber17DirectStates (2 + 14) [mtFiber17StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber17DirectStates 2 14 [mtFiber17StateAt 0] (mtFiber17StateAt 5) h2

theorem mtFiber17State6_in_close :
    mtFiber17StateAt 6 ∈ closeChainFiber mtWord mtFiber17DirectStates mtFiber17DirectStates.length [mtFiber17StateAt 0] := by
  have h0 : mtFiber17StateAt 0 ∈ closeChainFiber mtWord mtFiber17DirectStates 0 [mtFiber17StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber17StateAt 1 ∈ closeChainFiber mtWord mtFiber17DirectStates 1 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 0 [mtFiber17StateAt 0]
      (mtFiber17StateAt 0) (mtFiber17StateAt 1) (by decide) h0 (by decide)
      mtFiber17ReverseSingleStep1
  have h2 : mtFiber17StateAt 2 ∈ closeChainFiber mtWord mtFiber17DirectStates 2 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 1 [mtFiber17StateAt 0]
      (mtFiber17StateAt 1) (mtFiber17StateAt 2) (by decide) h1 (by decide)
      mtFiber17ReverseSingleStep2
  have h3 : mtFiber17StateAt 6 ∈ closeChainFiber mtWord mtFiber17DirectStates 3 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 2 [mtFiber17StateAt 0]
      (mtFiber17StateAt 2) (mtFiber17StateAt 6) (by decide) h2 (by decide)
      mtFiber17ReverseSingleStep6
  change mtFiber17StateAt 6 ∈ closeChainFiber mtWord mtFiber17DirectStates (3 + 13) [mtFiber17StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber17DirectStates 3 13 [mtFiber17StateAt 0] (mtFiber17StateAt 6) h3

theorem mtFiber17State7_in_close :
    mtFiber17StateAt 7 ∈ closeChainFiber mtWord mtFiber17DirectStates mtFiber17DirectStates.length [mtFiber17StateAt 0] := by
  have h0 : mtFiber17StateAt 0 ∈ closeChainFiber mtWord mtFiber17DirectStates 0 [mtFiber17StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber17StateAt 3 ∈ closeChainFiber mtWord mtFiber17DirectStates 1 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 0 [mtFiber17StateAt 0]
      (mtFiber17StateAt 0) (mtFiber17StateAt 3) (by decide) h0 (by decide)
      mtFiber17ReverseSingleStep3
  have h2 : mtFiber17StateAt 7 ∈ closeChainFiber mtWord mtFiber17DirectStates 2 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 1 [mtFiber17StateAt 0]
      (mtFiber17StateAt 3) (mtFiber17StateAt 7) (by decide) h1 (by decide)
      mtFiber17ReverseSingleStep7
  change mtFiber17StateAt 7 ∈ closeChainFiber mtWord mtFiber17DirectStates (2 + 14) [mtFiber17StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber17DirectStates 2 14 [mtFiber17StateAt 0] (mtFiber17StateAt 7) h2

theorem mtFiber17State8_in_close :
    mtFiber17StateAt 8 ∈ closeChainFiber mtWord mtFiber17DirectStates mtFiber17DirectStates.length [mtFiber17StateAt 0] := by
  have h0 : mtFiber17StateAt 0 ∈ closeChainFiber mtWord mtFiber17DirectStates 0 [mtFiber17StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber17StateAt 8 ∈ closeChainFiber mtWord mtFiber17DirectStates 1 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 0 [mtFiber17StateAt 0]
      (mtFiber17StateAt 0) (mtFiber17StateAt 8) (by decide) h0 (by decide)
      mtFiber17ReverseSingleStep8
  change mtFiber17StateAt 8 ∈ closeChainFiber mtWord mtFiber17DirectStates (1 + 15) [mtFiber17StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber17DirectStates 1 15 [mtFiber17StateAt 0] (mtFiber17StateAt 8) h1

theorem mtFiber17State9_in_close :
    mtFiber17StateAt 9 ∈ closeChainFiber mtWord mtFiber17DirectStates mtFiber17DirectStates.length [mtFiber17StateAt 0] := by
  have h0 : mtFiber17StateAt 0 ∈ closeChainFiber mtWord mtFiber17DirectStates 0 [mtFiber17StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber17StateAt 1 ∈ closeChainFiber mtWord mtFiber17DirectStates 1 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 0 [mtFiber17StateAt 0]
      (mtFiber17StateAt 0) (mtFiber17StateAt 1) (by decide) h0 (by decide)
      mtFiber17ReverseSingleStep1
  have h2 : mtFiber17StateAt 9 ∈ closeChainFiber mtWord mtFiber17DirectStates 2 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 1 [mtFiber17StateAt 0]
      (mtFiber17StateAt 1) (mtFiber17StateAt 9) (by decide) h1 (by decide)
      mtFiber17ReverseSingleStep9
  change mtFiber17StateAt 9 ∈ closeChainFiber mtWord mtFiber17DirectStates (2 + 14) [mtFiber17StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber17DirectStates 2 14 [mtFiber17StateAt 0] (mtFiber17StateAt 9) h2

theorem mtFiber17State10_in_close :
    mtFiber17StateAt 10 ∈ closeChainFiber mtWord mtFiber17DirectStates mtFiber17DirectStates.length [mtFiber17StateAt 0] := by
  have h0 : mtFiber17StateAt 0 ∈ closeChainFiber mtWord mtFiber17DirectStates 0 [mtFiber17StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber17StateAt 1 ∈ closeChainFiber mtWord mtFiber17DirectStates 1 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 0 [mtFiber17StateAt 0]
      (mtFiber17StateAt 0) (mtFiber17StateAt 1) (by decide) h0 (by decide)
      mtFiber17ReverseSingleStep1
  have h2 : mtFiber17StateAt 2 ∈ closeChainFiber mtWord mtFiber17DirectStates 2 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 1 [mtFiber17StateAt 0]
      (mtFiber17StateAt 1) (mtFiber17StateAt 2) (by decide) h1 (by decide)
      mtFiber17ReverseSingleStep2
  have h3 : mtFiber17StateAt 10 ∈ closeChainFiber mtWord mtFiber17DirectStates 3 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 2 [mtFiber17StateAt 0]
      (mtFiber17StateAt 2) (mtFiber17StateAt 10) (by decide) h2 (by decide)
      mtFiber17ReverseSingleStep10
  change mtFiber17StateAt 10 ∈ closeChainFiber mtWord mtFiber17DirectStates (3 + 13) [mtFiber17StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber17DirectStates 3 13 [mtFiber17StateAt 0] (mtFiber17StateAt 10) h3

theorem mtFiber17State11_in_close :
    mtFiber17StateAt 11 ∈ closeChainFiber mtWord mtFiber17DirectStates mtFiber17DirectStates.length [mtFiber17StateAt 0] := by
  have h0 : mtFiber17StateAt 0 ∈ closeChainFiber mtWord mtFiber17DirectStates 0 [mtFiber17StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber17StateAt 3 ∈ closeChainFiber mtWord mtFiber17DirectStates 1 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 0 [mtFiber17StateAt 0]
      (mtFiber17StateAt 0) (mtFiber17StateAt 3) (by decide) h0 (by decide)
      mtFiber17ReverseSingleStep3
  have h2 : mtFiber17StateAt 11 ∈ closeChainFiber mtWord mtFiber17DirectStates 2 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 1 [mtFiber17StateAt 0]
      (mtFiber17StateAt 3) (mtFiber17StateAt 11) (by decide) h1 (by decide)
      mtFiber17ReverseSingleStep11
  change mtFiber17StateAt 11 ∈ closeChainFiber mtWord mtFiber17DirectStates (2 + 14) [mtFiber17StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber17DirectStates 2 14 [mtFiber17StateAt 0] (mtFiber17StateAt 11) h2

theorem mtFiber17State12_in_close :
    mtFiber17StateAt 12 ∈ closeChainFiber mtWord mtFiber17DirectStates mtFiber17DirectStates.length [mtFiber17StateAt 0] := by
  have h0 : mtFiber17StateAt 0 ∈ closeChainFiber mtWord mtFiber17DirectStates 0 [mtFiber17StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber17StateAt 4 ∈ closeChainFiber mtWord mtFiber17DirectStates 1 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 0 [mtFiber17StateAt 0]
      (mtFiber17StateAt 0) (mtFiber17StateAt 4) (by decide) h0 (by decide)
      mtFiber17ReverseSingleStep4
  have h2 : mtFiber17StateAt 12 ∈ closeChainFiber mtWord mtFiber17DirectStates 2 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 1 [mtFiber17StateAt 0]
      (mtFiber17StateAt 4) (mtFiber17StateAt 12) (by decide) h1 (by decide)
      mtFiber17ReverseSingleStep12
  change mtFiber17StateAt 12 ∈ closeChainFiber mtWord mtFiber17DirectStates (2 + 14) [mtFiber17StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber17DirectStates 2 14 [mtFiber17StateAt 0] (mtFiber17StateAt 12) h2

theorem mtFiber17State13_in_close :
    mtFiber17StateAt 13 ∈ closeChainFiber mtWord mtFiber17DirectStates mtFiber17DirectStates.length [mtFiber17StateAt 0] := by
  have h0 : mtFiber17StateAt 0 ∈ closeChainFiber mtWord mtFiber17DirectStates 0 [mtFiber17StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber17StateAt 1 ∈ closeChainFiber mtWord mtFiber17DirectStates 1 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 0 [mtFiber17StateAt 0]
      (mtFiber17StateAt 0) (mtFiber17StateAt 1) (by decide) h0 (by decide)
      mtFiber17ReverseSingleStep1
  have h2 : mtFiber17StateAt 5 ∈ closeChainFiber mtWord mtFiber17DirectStates 2 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 1 [mtFiber17StateAt 0]
      (mtFiber17StateAt 1) (mtFiber17StateAt 5) (by decide) h1 (by decide)
      mtFiber17ReverseSingleStep5
  have h3 : mtFiber17StateAt 13 ∈ closeChainFiber mtWord mtFiber17DirectStates 3 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 2 [mtFiber17StateAt 0]
      (mtFiber17StateAt 5) (mtFiber17StateAt 13) (by decide) h2 (by decide)
      mtFiber17ReverseSingleStep13
  change mtFiber17StateAt 13 ∈ closeChainFiber mtWord mtFiber17DirectStates (3 + 13) [mtFiber17StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber17DirectStates 3 13 [mtFiber17StateAt 0] (mtFiber17StateAt 13) h3

theorem mtFiber17State14_in_close :
    mtFiber17StateAt 14 ∈ closeChainFiber mtWord mtFiber17DirectStates mtFiber17DirectStates.length [mtFiber17StateAt 0] := by
  have h0 : mtFiber17StateAt 0 ∈ closeChainFiber mtWord mtFiber17DirectStates 0 [mtFiber17StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber17StateAt 1 ∈ closeChainFiber mtWord mtFiber17DirectStates 1 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 0 [mtFiber17StateAt 0]
      (mtFiber17StateAt 0) (mtFiber17StateAt 1) (by decide) h0 (by decide)
      mtFiber17ReverseSingleStep1
  have h2 : mtFiber17StateAt 2 ∈ closeChainFiber mtWord mtFiber17DirectStates 2 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 1 [mtFiber17StateAt 0]
      (mtFiber17StateAt 1) (mtFiber17StateAt 2) (by decide) h1 (by decide)
      mtFiber17ReverseSingleStep2
  have h3 : mtFiber17StateAt 6 ∈ closeChainFiber mtWord mtFiber17DirectStates 3 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 2 [mtFiber17StateAt 0]
      (mtFiber17StateAt 2) (mtFiber17StateAt 6) (by decide) h2 (by decide)
      mtFiber17ReverseSingleStep6
  have h4 : mtFiber17StateAt 14 ∈ closeChainFiber mtWord mtFiber17DirectStates 4 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 3 [mtFiber17StateAt 0]
      (mtFiber17StateAt 6) (mtFiber17StateAt 14) (by decide) h3 (by decide)
      mtFiber17ReverseSingleStep14
  change mtFiber17StateAt 14 ∈ closeChainFiber mtWord mtFiber17DirectStates (4 + 12) [mtFiber17StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber17DirectStates 4 12 [mtFiber17StateAt 0] (mtFiber17StateAt 14) h4

theorem mtFiber17State15_in_close :
    mtFiber17StateAt 15 ∈ closeChainFiber mtWord mtFiber17DirectStates mtFiber17DirectStates.length [mtFiber17StateAt 0] := by
  have h0 : mtFiber17StateAt 0 ∈ closeChainFiber mtWord mtFiber17DirectStates 0 [mtFiber17StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber17StateAt 3 ∈ closeChainFiber mtWord mtFiber17DirectStates 1 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 0 [mtFiber17StateAt 0]
      (mtFiber17StateAt 0) (mtFiber17StateAt 3) (by decide) h0 (by decide)
      mtFiber17ReverseSingleStep3
  have h2 : mtFiber17StateAt 7 ∈ closeChainFiber mtWord mtFiber17DirectStates 2 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 1 [mtFiber17StateAt 0]
      (mtFiber17StateAt 3) (mtFiber17StateAt 7) (by decide) h1 (by decide)
      mtFiber17ReverseSingleStep7
  have h3 : mtFiber17StateAt 15 ∈ closeChainFiber mtWord mtFiber17DirectStates 3 [mtFiber17StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber17DirectStates 2 [mtFiber17StateAt 0]
      (mtFiber17StateAt 7) (mtFiber17StateAt 15) (by decide) h2 (by decide)
      mtFiber17ReverseSingleStep15
  change mtFiber17StateAt 15 ∈ closeChainFiber mtWord mtFiber17DirectStates (3 + 13) [mtFiber17StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber17DirectStates 3 13 [mtFiber17StateAt 0] (mtFiber17StateAt 15) h3

theorem mtFiber17DirectConnected :
    chainFiberConnected mtWord mtFiber17DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber17DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber17State0_in_close
  · subst state
    exact mtFiber17State1_in_close
  · subst state
    exact mtFiber17State2_in_close
  · subst state
    exact mtFiber17State3_in_close
  · subst state
    exact mtFiber17State4_in_close
  · subst state
    exact mtFiber17State5_in_close
  · subst state
    exact mtFiber17State6_in_close
  · subst state
    exact mtFiber17State7_in_close
  · subst state
    exact mtFiber17State8_in_close
  · subst state
    exact mtFiber17State9_in_close
  · subst state
    exact mtFiber17State10_in_close
  · subst state
    exact mtFiber17State11_in_close
  · subst state
    exact mtFiber17State12_in_close
  · subst state
    exact mtFiber17State13_in_close
  · subst state
    exact mtFiber17State14_in_close
  · subst state
    exact mtFiber17State15_in_close
  · cases h
def mtFiber18StateAt (i : Nat) : List TauState :=
  directStates (mtFiber18RowAt i).sourceLeft (mtFiber18RowAt i).sourceRight

def mtFiber18DirectStates : List (List TauState) :=
  [mtFiber18StateAt 0, mtFiber18StateAt 1, mtFiber18StateAt 2, mtFiber18StateAt 3, mtFiber18StateAt 4, mtFiber18StateAt 5, mtFiber18StateAt 6, mtFiber18StateAt 7, mtFiber18StateAt 8, mtFiber18StateAt 9, mtFiber18StateAt 10, mtFiber18StateAt 11, mtFiber18StateAt 12, mtFiber18StateAt 13, mtFiber18StateAt 14, mtFiber18StateAt 15]

theorem mtFiber18ReverseRow_1_ok :
    mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber18Chunk0_ok
  change (mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 0) &&
    mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber18ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber18StateAt 0) (mtFiber18StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber18StateAt 0) (mtFiber18StateAt 1)
    (mtFiber18RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber18Key mtFiber18Expected
        (mtFiber18RowAt 1) (by decide) mtFiber18ReverseRow_1_ok
      simpa [mtFiber18StateAt, mtFiber18RowAt, mtFiber18Rows, listGetD, directRow] using h)

theorem mtFiber18ReverseRow_2_ok :
    mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber18Chunk1_ok
  change (mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 2) &&
    mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber18ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber18StateAt 0) (mtFiber18StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber18StateAt 0) (mtFiber18StateAt 2)
    (mtFiber18RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber18Key mtFiber18Expected
        (mtFiber18RowAt 2) (by decide) mtFiber18ReverseRow_2_ok
      simpa [mtFiber18StateAt, mtFiber18RowAt, mtFiber18Rows, listGetD, directRow] using h)

theorem mtFiber18ReverseRow_3_ok :
    mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber18Chunk1_ok
  change (mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 2) &&
    mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber18ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber18StateAt 1) (mtFiber18StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber18StateAt 1) (mtFiber18StateAt 3)
    (mtFiber18RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber18Key mtFiber18Expected
        (mtFiber18RowAt 3) (by decide) mtFiber18ReverseRow_3_ok
      simpa [mtFiber18StateAt, mtFiber18RowAt, mtFiber18Rows, listGetD, directRow] using h)

theorem mtFiber18ReverseRow_4_ok :
    mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber18Chunk2_ok
  change (mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 4) &&
    mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber18ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber18StateAt 0) (mtFiber18StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber18StateAt 0) (mtFiber18StateAt 4)
    (mtFiber18RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber18Key mtFiber18Expected
        (mtFiber18RowAt 4) (by decide) mtFiber18ReverseRow_4_ok
      simpa [mtFiber18StateAt, mtFiber18RowAt, mtFiber18Rows, listGetD, directRow] using h)

theorem mtFiber18ReverseRow_5_ok :
    mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber18Chunk2_ok
  change (mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 4) &&
    mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber18ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber18StateAt 1) (mtFiber18StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber18StateAt 1) (mtFiber18StateAt 5)
    (mtFiber18RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber18Key mtFiber18Expected
        (mtFiber18RowAt 5) (by decide) mtFiber18ReverseRow_5_ok
      simpa [mtFiber18StateAt, mtFiber18RowAt, mtFiber18Rows, listGetD, directRow] using h)

theorem mtFiber18ReverseRow_6_ok :
    mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber18Chunk3_ok
  change (mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 6) &&
    mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber18ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber18StateAt 2) (mtFiber18StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber18StateAt 2) (mtFiber18StateAt 6)
    (mtFiber18RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber18Key mtFiber18Expected
        (mtFiber18RowAt 6) (by decide) mtFiber18ReverseRow_6_ok
      simpa [mtFiber18StateAt, mtFiber18RowAt, mtFiber18Rows, listGetD, directRow] using h)

theorem mtFiber18ReverseRow_7_ok :
    mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber18Chunk3_ok
  change (mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 6) &&
    mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber18ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber18StateAt 3) (mtFiber18StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber18StateAt 3) (mtFiber18StateAt 7)
    (mtFiber18RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber18Key mtFiber18Expected
        (mtFiber18RowAt 7) (by decide) mtFiber18ReverseRow_7_ok
      simpa [mtFiber18StateAt, mtFiber18RowAt, mtFiber18Rows, listGetD, directRow] using h)

theorem mtFiber18ReverseRow_8_ok :
    mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber18Chunk4_ok
  change (mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 8) &&
    mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber18ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber18StateAt 0) (mtFiber18StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber18StateAt 0) (mtFiber18StateAt 8)
    (mtFiber18RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber18Key mtFiber18Expected
        (mtFiber18RowAt 8) (by decide) mtFiber18ReverseRow_8_ok
      simpa [mtFiber18StateAt, mtFiber18RowAt, mtFiber18Rows, listGetD, directRow] using h)

theorem mtFiber18ReverseRow_9_ok :
    mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber18Chunk4_ok
  change (mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 8) &&
    mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber18ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber18StateAt 1) (mtFiber18StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber18StateAt 1) (mtFiber18StateAt 9)
    (mtFiber18RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber18Key mtFiber18Expected
        (mtFiber18RowAt 9) (by decide) mtFiber18ReverseRow_9_ok
      simpa [mtFiber18StateAt, mtFiber18RowAt, mtFiber18Rows, listGetD, directRow] using h)

theorem mtFiber18ReverseRow_10_ok :
    mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber18Chunk5_ok
  change (mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 10) &&
    mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber18ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber18StateAt 2) (mtFiber18StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber18StateAt 2) (mtFiber18StateAt 10)
    (mtFiber18RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber18Key mtFiber18Expected
        (mtFiber18RowAt 10) (by decide) mtFiber18ReverseRow_10_ok
      simpa [mtFiber18StateAt, mtFiber18RowAt, mtFiber18Rows, listGetD, directRow] using h)

theorem mtFiber18ReverseRow_11_ok :
    mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber18Chunk5_ok
  change (mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 10) &&
    mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber18ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber18StateAt 3) (mtFiber18StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber18StateAt 3) (mtFiber18StateAt 11)
    (mtFiber18RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber18Key mtFiber18Expected
        (mtFiber18RowAt 11) (by decide) mtFiber18ReverseRow_11_ok
      simpa [mtFiber18StateAt, mtFiber18RowAt, mtFiber18Rows, listGetD, directRow] using h)

theorem mtFiber18ReverseRow_12_ok :
    mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber18Chunk6_ok
  change (mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 12) &&
    mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber18ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber18StateAt 4) (mtFiber18StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber18StateAt 4) (mtFiber18StateAt 12)
    (mtFiber18RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber18Key mtFiber18Expected
        (mtFiber18RowAt 12) (by decide) mtFiber18ReverseRow_12_ok
      simpa [mtFiber18StateAt, mtFiber18RowAt, mtFiber18Rows, listGetD, directRow] using h)

theorem mtFiber18ReverseRow_13_ok :
    mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber18Chunk6_ok
  change (mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 12) &&
    mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber18ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber18StateAt 5) (mtFiber18StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber18StateAt 5) (mtFiber18StateAt 13)
    (mtFiber18RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber18Key mtFiber18Expected
        (mtFiber18RowAt 13) (by decide) mtFiber18ReverseRow_13_ok
      simpa [mtFiber18StateAt, mtFiber18RowAt, mtFiber18Rows, listGetD, directRow] using h)

theorem mtFiber18ReverseRow_14_ok :
    mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber18Chunk7_ok
  change (mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 14) &&
    mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber18ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber18StateAt 6) (mtFiber18StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber18StateAt 6) (mtFiber18StateAt 14)
    (mtFiber18RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber18Key mtFiber18Expected
        (mtFiber18RowAt 14) (by decide) mtFiber18ReverseRow_14_ok
      simpa [mtFiber18StateAt, mtFiber18RowAt, mtFiber18Rows, listGetD, directRow] using h)

theorem mtFiber18ReverseRow_15_ok :
    mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber18Chunk7_ok
  change (mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 14) &&
    mtRowReverseValid mtFiber18Key mtFiber18Expected (mtFiber18RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber18ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber18StateAt 7) (mtFiber18StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber18StateAt 7) (mtFiber18StateAt 15)
    (mtFiber18RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber18Key mtFiber18Expected
        (mtFiber18RowAt 15) (by decide) mtFiber18ReverseRow_15_ok
      simpa [mtFiber18StateAt, mtFiber18RowAt, mtFiber18Rows, listGetD, directRow] using h)

theorem mtFiber18State0_in_close :
    mtFiber18StateAt 0 ∈ closeChainFiber mtWord mtFiber18DirectStates mtFiber18DirectStates.length [mtFiber18StateAt 0] := by
  change mtFiber18StateAt 0 ∈ closeChainFiber mtWord mtFiber18DirectStates 16 [mtFiber18StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber18DirectStates 0 16 [mtFiber18StateAt 0] (mtFiber18StateAt 0) (by simp [closeChainFiber])

theorem mtFiber18State1_in_close :
    mtFiber18StateAt 1 ∈ closeChainFiber mtWord mtFiber18DirectStates mtFiber18DirectStates.length [mtFiber18StateAt 0] := by
  have h0 : mtFiber18StateAt 0 ∈ closeChainFiber mtWord mtFiber18DirectStates 0 [mtFiber18StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber18StateAt 1 ∈ closeChainFiber mtWord mtFiber18DirectStates 1 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 0 [mtFiber18StateAt 0]
      (mtFiber18StateAt 0) (mtFiber18StateAt 1) (by decide) h0 (by decide)
      mtFiber18ReverseSingleStep1
  change mtFiber18StateAt 1 ∈ closeChainFiber mtWord mtFiber18DirectStates (1 + 15) [mtFiber18StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber18DirectStates 1 15 [mtFiber18StateAt 0] (mtFiber18StateAt 1) h1

theorem mtFiber18State2_in_close :
    mtFiber18StateAt 2 ∈ closeChainFiber mtWord mtFiber18DirectStates mtFiber18DirectStates.length [mtFiber18StateAt 0] := by
  have h0 : mtFiber18StateAt 0 ∈ closeChainFiber mtWord mtFiber18DirectStates 0 [mtFiber18StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber18StateAt 2 ∈ closeChainFiber mtWord mtFiber18DirectStates 1 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 0 [mtFiber18StateAt 0]
      (mtFiber18StateAt 0) (mtFiber18StateAt 2) (by decide) h0 (by decide)
      mtFiber18ReverseSingleStep2
  change mtFiber18StateAt 2 ∈ closeChainFiber mtWord mtFiber18DirectStates (1 + 15) [mtFiber18StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber18DirectStates 1 15 [mtFiber18StateAt 0] (mtFiber18StateAt 2) h1

theorem mtFiber18State3_in_close :
    mtFiber18StateAt 3 ∈ closeChainFiber mtWord mtFiber18DirectStates mtFiber18DirectStates.length [mtFiber18StateAt 0] := by
  have h0 : mtFiber18StateAt 0 ∈ closeChainFiber mtWord mtFiber18DirectStates 0 [mtFiber18StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber18StateAt 1 ∈ closeChainFiber mtWord mtFiber18DirectStates 1 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 0 [mtFiber18StateAt 0]
      (mtFiber18StateAt 0) (mtFiber18StateAt 1) (by decide) h0 (by decide)
      mtFiber18ReverseSingleStep1
  have h2 : mtFiber18StateAt 3 ∈ closeChainFiber mtWord mtFiber18DirectStates 2 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 1 [mtFiber18StateAt 0]
      (mtFiber18StateAt 1) (mtFiber18StateAt 3) (by decide) h1 (by decide)
      mtFiber18ReverseSingleStep3
  change mtFiber18StateAt 3 ∈ closeChainFiber mtWord mtFiber18DirectStates (2 + 14) [mtFiber18StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber18DirectStates 2 14 [mtFiber18StateAt 0] (mtFiber18StateAt 3) h2

theorem mtFiber18State4_in_close :
    mtFiber18StateAt 4 ∈ closeChainFiber mtWord mtFiber18DirectStates mtFiber18DirectStates.length [mtFiber18StateAt 0] := by
  have h0 : mtFiber18StateAt 0 ∈ closeChainFiber mtWord mtFiber18DirectStates 0 [mtFiber18StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber18StateAt 4 ∈ closeChainFiber mtWord mtFiber18DirectStates 1 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 0 [mtFiber18StateAt 0]
      (mtFiber18StateAt 0) (mtFiber18StateAt 4) (by decide) h0 (by decide)
      mtFiber18ReverseSingleStep4
  change mtFiber18StateAt 4 ∈ closeChainFiber mtWord mtFiber18DirectStates (1 + 15) [mtFiber18StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber18DirectStates 1 15 [mtFiber18StateAt 0] (mtFiber18StateAt 4) h1

theorem mtFiber18State5_in_close :
    mtFiber18StateAt 5 ∈ closeChainFiber mtWord mtFiber18DirectStates mtFiber18DirectStates.length [mtFiber18StateAt 0] := by
  have h0 : mtFiber18StateAt 0 ∈ closeChainFiber mtWord mtFiber18DirectStates 0 [mtFiber18StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber18StateAt 1 ∈ closeChainFiber mtWord mtFiber18DirectStates 1 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 0 [mtFiber18StateAt 0]
      (mtFiber18StateAt 0) (mtFiber18StateAt 1) (by decide) h0 (by decide)
      mtFiber18ReverseSingleStep1
  have h2 : mtFiber18StateAt 5 ∈ closeChainFiber mtWord mtFiber18DirectStates 2 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 1 [mtFiber18StateAt 0]
      (mtFiber18StateAt 1) (mtFiber18StateAt 5) (by decide) h1 (by decide)
      mtFiber18ReverseSingleStep5
  change mtFiber18StateAt 5 ∈ closeChainFiber mtWord mtFiber18DirectStates (2 + 14) [mtFiber18StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber18DirectStates 2 14 [mtFiber18StateAt 0] (mtFiber18StateAt 5) h2

theorem mtFiber18State6_in_close :
    mtFiber18StateAt 6 ∈ closeChainFiber mtWord mtFiber18DirectStates mtFiber18DirectStates.length [mtFiber18StateAt 0] := by
  have h0 : mtFiber18StateAt 0 ∈ closeChainFiber mtWord mtFiber18DirectStates 0 [mtFiber18StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber18StateAt 2 ∈ closeChainFiber mtWord mtFiber18DirectStates 1 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 0 [mtFiber18StateAt 0]
      (mtFiber18StateAt 0) (mtFiber18StateAt 2) (by decide) h0 (by decide)
      mtFiber18ReverseSingleStep2
  have h2 : mtFiber18StateAt 6 ∈ closeChainFiber mtWord mtFiber18DirectStates 2 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 1 [mtFiber18StateAt 0]
      (mtFiber18StateAt 2) (mtFiber18StateAt 6) (by decide) h1 (by decide)
      mtFiber18ReverseSingleStep6
  change mtFiber18StateAt 6 ∈ closeChainFiber mtWord mtFiber18DirectStates (2 + 14) [mtFiber18StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber18DirectStates 2 14 [mtFiber18StateAt 0] (mtFiber18StateAt 6) h2

theorem mtFiber18State7_in_close :
    mtFiber18StateAt 7 ∈ closeChainFiber mtWord mtFiber18DirectStates mtFiber18DirectStates.length [mtFiber18StateAt 0] := by
  have h0 : mtFiber18StateAt 0 ∈ closeChainFiber mtWord mtFiber18DirectStates 0 [mtFiber18StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber18StateAt 1 ∈ closeChainFiber mtWord mtFiber18DirectStates 1 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 0 [mtFiber18StateAt 0]
      (mtFiber18StateAt 0) (mtFiber18StateAt 1) (by decide) h0 (by decide)
      mtFiber18ReverseSingleStep1
  have h2 : mtFiber18StateAt 3 ∈ closeChainFiber mtWord mtFiber18DirectStates 2 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 1 [mtFiber18StateAt 0]
      (mtFiber18StateAt 1) (mtFiber18StateAt 3) (by decide) h1 (by decide)
      mtFiber18ReverseSingleStep3
  have h3 : mtFiber18StateAt 7 ∈ closeChainFiber mtWord mtFiber18DirectStates 3 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 2 [mtFiber18StateAt 0]
      (mtFiber18StateAt 3) (mtFiber18StateAt 7) (by decide) h2 (by decide)
      mtFiber18ReverseSingleStep7
  change mtFiber18StateAt 7 ∈ closeChainFiber mtWord mtFiber18DirectStates (3 + 13) [mtFiber18StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber18DirectStates 3 13 [mtFiber18StateAt 0] (mtFiber18StateAt 7) h3

theorem mtFiber18State8_in_close :
    mtFiber18StateAt 8 ∈ closeChainFiber mtWord mtFiber18DirectStates mtFiber18DirectStates.length [mtFiber18StateAt 0] := by
  have h0 : mtFiber18StateAt 0 ∈ closeChainFiber mtWord mtFiber18DirectStates 0 [mtFiber18StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber18StateAt 8 ∈ closeChainFiber mtWord mtFiber18DirectStates 1 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 0 [mtFiber18StateAt 0]
      (mtFiber18StateAt 0) (mtFiber18StateAt 8) (by decide) h0 (by decide)
      mtFiber18ReverseSingleStep8
  change mtFiber18StateAt 8 ∈ closeChainFiber mtWord mtFiber18DirectStates (1 + 15) [mtFiber18StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber18DirectStates 1 15 [mtFiber18StateAt 0] (mtFiber18StateAt 8) h1

theorem mtFiber18State9_in_close :
    mtFiber18StateAt 9 ∈ closeChainFiber mtWord mtFiber18DirectStates mtFiber18DirectStates.length [mtFiber18StateAt 0] := by
  have h0 : mtFiber18StateAt 0 ∈ closeChainFiber mtWord mtFiber18DirectStates 0 [mtFiber18StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber18StateAt 1 ∈ closeChainFiber mtWord mtFiber18DirectStates 1 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 0 [mtFiber18StateAt 0]
      (mtFiber18StateAt 0) (mtFiber18StateAt 1) (by decide) h0 (by decide)
      mtFiber18ReverseSingleStep1
  have h2 : mtFiber18StateAt 9 ∈ closeChainFiber mtWord mtFiber18DirectStates 2 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 1 [mtFiber18StateAt 0]
      (mtFiber18StateAt 1) (mtFiber18StateAt 9) (by decide) h1 (by decide)
      mtFiber18ReverseSingleStep9
  change mtFiber18StateAt 9 ∈ closeChainFiber mtWord mtFiber18DirectStates (2 + 14) [mtFiber18StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber18DirectStates 2 14 [mtFiber18StateAt 0] (mtFiber18StateAt 9) h2

theorem mtFiber18State10_in_close :
    mtFiber18StateAt 10 ∈ closeChainFiber mtWord mtFiber18DirectStates mtFiber18DirectStates.length [mtFiber18StateAt 0] := by
  have h0 : mtFiber18StateAt 0 ∈ closeChainFiber mtWord mtFiber18DirectStates 0 [mtFiber18StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber18StateAt 2 ∈ closeChainFiber mtWord mtFiber18DirectStates 1 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 0 [mtFiber18StateAt 0]
      (mtFiber18StateAt 0) (mtFiber18StateAt 2) (by decide) h0 (by decide)
      mtFiber18ReverseSingleStep2
  have h2 : mtFiber18StateAt 10 ∈ closeChainFiber mtWord mtFiber18DirectStates 2 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 1 [mtFiber18StateAt 0]
      (mtFiber18StateAt 2) (mtFiber18StateAt 10) (by decide) h1 (by decide)
      mtFiber18ReverseSingleStep10
  change mtFiber18StateAt 10 ∈ closeChainFiber mtWord mtFiber18DirectStates (2 + 14) [mtFiber18StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber18DirectStates 2 14 [mtFiber18StateAt 0] (mtFiber18StateAt 10) h2

theorem mtFiber18State11_in_close :
    mtFiber18StateAt 11 ∈ closeChainFiber mtWord mtFiber18DirectStates mtFiber18DirectStates.length [mtFiber18StateAt 0] := by
  have h0 : mtFiber18StateAt 0 ∈ closeChainFiber mtWord mtFiber18DirectStates 0 [mtFiber18StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber18StateAt 1 ∈ closeChainFiber mtWord mtFiber18DirectStates 1 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 0 [mtFiber18StateAt 0]
      (mtFiber18StateAt 0) (mtFiber18StateAt 1) (by decide) h0 (by decide)
      mtFiber18ReverseSingleStep1
  have h2 : mtFiber18StateAt 3 ∈ closeChainFiber mtWord mtFiber18DirectStates 2 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 1 [mtFiber18StateAt 0]
      (mtFiber18StateAt 1) (mtFiber18StateAt 3) (by decide) h1 (by decide)
      mtFiber18ReverseSingleStep3
  have h3 : mtFiber18StateAt 11 ∈ closeChainFiber mtWord mtFiber18DirectStates 3 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 2 [mtFiber18StateAt 0]
      (mtFiber18StateAt 3) (mtFiber18StateAt 11) (by decide) h2 (by decide)
      mtFiber18ReverseSingleStep11
  change mtFiber18StateAt 11 ∈ closeChainFiber mtWord mtFiber18DirectStates (3 + 13) [mtFiber18StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber18DirectStates 3 13 [mtFiber18StateAt 0] (mtFiber18StateAt 11) h3

theorem mtFiber18State12_in_close :
    mtFiber18StateAt 12 ∈ closeChainFiber mtWord mtFiber18DirectStates mtFiber18DirectStates.length [mtFiber18StateAt 0] := by
  have h0 : mtFiber18StateAt 0 ∈ closeChainFiber mtWord mtFiber18DirectStates 0 [mtFiber18StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber18StateAt 4 ∈ closeChainFiber mtWord mtFiber18DirectStates 1 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 0 [mtFiber18StateAt 0]
      (mtFiber18StateAt 0) (mtFiber18StateAt 4) (by decide) h0 (by decide)
      mtFiber18ReverseSingleStep4
  have h2 : mtFiber18StateAt 12 ∈ closeChainFiber mtWord mtFiber18DirectStates 2 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 1 [mtFiber18StateAt 0]
      (mtFiber18StateAt 4) (mtFiber18StateAt 12) (by decide) h1 (by decide)
      mtFiber18ReverseSingleStep12
  change mtFiber18StateAt 12 ∈ closeChainFiber mtWord mtFiber18DirectStates (2 + 14) [mtFiber18StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber18DirectStates 2 14 [mtFiber18StateAt 0] (mtFiber18StateAt 12) h2

theorem mtFiber18State13_in_close :
    mtFiber18StateAt 13 ∈ closeChainFiber mtWord mtFiber18DirectStates mtFiber18DirectStates.length [mtFiber18StateAt 0] := by
  have h0 : mtFiber18StateAt 0 ∈ closeChainFiber mtWord mtFiber18DirectStates 0 [mtFiber18StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber18StateAt 1 ∈ closeChainFiber mtWord mtFiber18DirectStates 1 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 0 [mtFiber18StateAt 0]
      (mtFiber18StateAt 0) (mtFiber18StateAt 1) (by decide) h0 (by decide)
      mtFiber18ReverseSingleStep1
  have h2 : mtFiber18StateAt 5 ∈ closeChainFiber mtWord mtFiber18DirectStates 2 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 1 [mtFiber18StateAt 0]
      (mtFiber18StateAt 1) (mtFiber18StateAt 5) (by decide) h1 (by decide)
      mtFiber18ReverseSingleStep5
  have h3 : mtFiber18StateAt 13 ∈ closeChainFiber mtWord mtFiber18DirectStates 3 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 2 [mtFiber18StateAt 0]
      (mtFiber18StateAt 5) (mtFiber18StateAt 13) (by decide) h2 (by decide)
      mtFiber18ReverseSingleStep13
  change mtFiber18StateAt 13 ∈ closeChainFiber mtWord mtFiber18DirectStates (3 + 13) [mtFiber18StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber18DirectStates 3 13 [mtFiber18StateAt 0] (mtFiber18StateAt 13) h3

theorem mtFiber18State14_in_close :
    mtFiber18StateAt 14 ∈ closeChainFiber mtWord mtFiber18DirectStates mtFiber18DirectStates.length [mtFiber18StateAt 0] := by
  have h0 : mtFiber18StateAt 0 ∈ closeChainFiber mtWord mtFiber18DirectStates 0 [mtFiber18StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber18StateAt 2 ∈ closeChainFiber mtWord mtFiber18DirectStates 1 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 0 [mtFiber18StateAt 0]
      (mtFiber18StateAt 0) (mtFiber18StateAt 2) (by decide) h0 (by decide)
      mtFiber18ReverseSingleStep2
  have h2 : mtFiber18StateAt 6 ∈ closeChainFiber mtWord mtFiber18DirectStates 2 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 1 [mtFiber18StateAt 0]
      (mtFiber18StateAt 2) (mtFiber18StateAt 6) (by decide) h1 (by decide)
      mtFiber18ReverseSingleStep6
  have h3 : mtFiber18StateAt 14 ∈ closeChainFiber mtWord mtFiber18DirectStates 3 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 2 [mtFiber18StateAt 0]
      (mtFiber18StateAt 6) (mtFiber18StateAt 14) (by decide) h2 (by decide)
      mtFiber18ReverseSingleStep14
  change mtFiber18StateAt 14 ∈ closeChainFiber mtWord mtFiber18DirectStates (3 + 13) [mtFiber18StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber18DirectStates 3 13 [mtFiber18StateAt 0] (mtFiber18StateAt 14) h3

theorem mtFiber18State15_in_close :
    mtFiber18StateAt 15 ∈ closeChainFiber mtWord mtFiber18DirectStates mtFiber18DirectStates.length [mtFiber18StateAt 0] := by
  have h0 : mtFiber18StateAt 0 ∈ closeChainFiber mtWord mtFiber18DirectStates 0 [mtFiber18StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber18StateAt 1 ∈ closeChainFiber mtWord mtFiber18DirectStates 1 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 0 [mtFiber18StateAt 0]
      (mtFiber18StateAt 0) (mtFiber18StateAt 1) (by decide) h0 (by decide)
      mtFiber18ReverseSingleStep1
  have h2 : mtFiber18StateAt 3 ∈ closeChainFiber mtWord mtFiber18DirectStates 2 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 1 [mtFiber18StateAt 0]
      (mtFiber18StateAt 1) (mtFiber18StateAt 3) (by decide) h1 (by decide)
      mtFiber18ReverseSingleStep3
  have h3 : mtFiber18StateAt 7 ∈ closeChainFiber mtWord mtFiber18DirectStates 3 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 2 [mtFiber18StateAt 0]
      (mtFiber18StateAt 3) (mtFiber18StateAt 7) (by decide) h2 (by decide)
      mtFiber18ReverseSingleStep7
  have h4 : mtFiber18StateAt 15 ∈ closeChainFiber mtWord mtFiber18DirectStates 4 [mtFiber18StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber18DirectStates 3 [mtFiber18StateAt 0]
      (mtFiber18StateAt 7) (mtFiber18StateAt 15) (by decide) h3 (by decide)
      mtFiber18ReverseSingleStep15
  change mtFiber18StateAt 15 ∈ closeChainFiber mtWord mtFiber18DirectStates (4 + 12) [mtFiber18StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber18DirectStates 4 12 [mtFiber18StateAt 0] (mtFiber18StateAt 15) h4

theorem mtFiber18DirectConnected :
    chainFiberConnected mtWord mtFiber18DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber18DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber18State0_in_close
  · subst state
    exact mtFiber18State1_in_close
  · subst state
    exact mtFiber18State2_in_close
  · subst state
    exact mtFiber18State3_in_close
  · subst state
    exact mtFiber18State4_in_close
  · subst state
    exact mtFiber18State5_in_close
  · subst state
    exact mtFiber18State6_in_close
  · subst state
    exact mtFiber18State7_in_close
  · subst state
    exact mtFiber18State8_in_close
  · subst state
    exact mtFiber18State9_in_close
  · subst state
    exact mtFiber18State10_in_close
  · subst state
    exact mtFiber18State11_in_close
  · subst state
    exact mtFiber18State12_in_close
  · subst state
    exact mtFiber18State13_in_close
  · subst state
    exact mtFiber18State14_in_close
  · subst state
    exact mtFiber18State15_in_close
  · cases h
def mtFiber22StateAt (i : Nat) : List TauState :=
  directStates (mtFiber22RowAt i).sourceLeft (mtFiber22RowAt i).sourceRight

def mtFiber22DirectStates : List (List TauState) :=
  [mtFiber22StateAt 0, mtFiber22StateAt 1, mtFiber22StateAt 2, mtFiber22StateAt 3, mtFiber22StateAt 4, mtFiber22StateAt 5, mtFiber22StateAt 6, mtFiber22StateAt 7, mtFiber22StateAt 8, mtFiber22StateAt 9, mtFiber22StateAt 10, mtFiber22StateAt 11, mtFiber22StateAt 12, mtFiber22StateAt 13, mtFiber22StateAt 14, mtFiber22StateAt 15]

theorem mtFiber22ReverseRow_1_ok :
    mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber22Chunk0_ok
  change (mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 0) &&
    mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber22ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber22StateAt 0) (mtFiber22StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber22StateAt 0) (mtFiber22StateAt 1)
    (mtFiber22RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber22Key mtFiber22Expected
        (mtFiber22RowAt 1) (by decide) mtFiber22ReverseRow_1_ok
      simpa [mtFiber22StateAt, mtFiber22RowAt, mtFiber22Rows, listGetD, directRow] using h)

theorem mtFiber22ReverseRow_2_ok :
    mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber22Chunk1_ok
  change (mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 2) &&
    mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber22ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber22StateAt 0) (mtFiber22StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber22StateAt 0) (mtFiber22StateAt 2)
    (mtFiber22RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber22Key mtFiber22Expected
        (mtFiber22RowAt 2) (by decide) mtFiber22ReverseRow_2_ok
      simpa [mtFiber22StateAt, mtFiber22RowAt, mtFiber22Rows, listGetD, directRow] using h)

theorem mtFiber22ReverseRow_3_ok :
    mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber22Chunk1_ok
  change (mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 2) &&
    mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber22ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber22StateAt 1) (mtFiber22StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber22StateAt 1) (mtFiber22StateAt 3)
    (mtFiber22RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber22Key mtFiber22Expected
        (mtFiber22RowAt 3) (by decide) mtFiber22ReverseRow_3_ok
      simpa [mtFiber22StateAt, mtFiber22RowAt, mtFiber22Rows, listGetD, directRow] using h)

theorem mtFiber22ReverseRow_4_ok :
    mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber22Chunk2_ok
  change (mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 4) &&
    mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber22ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber22StateAt 0) (mtFiber22StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber22StateAt 0) (mtFiber22StateAt 4)
    (mtFiber22RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber22Key mtFiber22Expected
        (mtFiber22RowAt 4) (by decide) mtFiber22ReverseRow_4_ok
      simpa [mtFiber22StateAt, mtFiber22RowAt, mtFiber22Rows, listGetD, directRow] using h)

theorem mtFiber22ReverseRow_5_ok :
    mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber22Chunk2_ok
  change (mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 4) &&
    mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber22ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber22StateAt 1) (mtFiber22StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber22StateAt 1) (mtFiber22StateAt 5)
    (mtFiber22RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber22Key mtFiber22Expected
        (mtFiber22RowAt 5) (by decide) mtFiber22ReverseRow_5_ok
      simpa [mtFiber22StateAt, mtFiber22RowAt, mtFiber22Rows, listGetD, directRow] using h)

theorem mtFiber22ReverseRow_6_ok :
    mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber22Chunk3_ok
  change (mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 6) &&
    mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber22ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber22StateAt 2) (mtFiber22StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber22StateAt 2) (mtFiber22StateAt 6)
    (mtFiber22RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber22Key mtFiber22Expected
        (mtFiber22RowAt 6) (by decide) mtFiber22ReverseRow_6_ok
      simpa [mtFiber22StateAt, mtFiber22RowAt, mtFiber22Rows, listGetD, directRow] using h)

theorem mtFiber22ReverseRow_7_ok :
    mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber22Chunk3_ok
  change (mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 6) &&
    mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber22ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber22StateAt 3) (mtFiber22StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber22StateAt 3) (mtFiber22StateAt 7)
    (mtFiber22RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber22Key mtFiber22Expected
        (mtFiber22RowAt 7) (by decide) mtFiber22ReverseRow_7_ok
      simpa [mtFiber22StateAt, mtFiber22RowAt, mtFiber22Rows, listGetD, directRow] using h)

theorem mtFiber22ReverseRow_8_ok :
    mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber22Chunk4_ok
  change (mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 8) &&
    mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber22ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber22StateAt 0) (mtFiber22StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber22StateAt 0) (mtFiber22StateAt 8)
    (mtFiber22RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber22Key mtFiber22Expected
        (mtFiber22RowAt 8) (by decide) mtFiber22ReverseRow_8_ok
      simpa [mtFiber22StateAt, mtFiber22RowAt, mtFiber22Rows, listGetD, directRow] using h)

theorem mtFiber22ReverseRow_9_ok :
    mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber22Chunk4_ok
  change (mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 8) &&
    mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber22ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber22StateAt 1) (mtFiber22StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber22StateAt 1) (mtFiber22StateAt 9)
    (mtFiber22RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber22Key mtFiber22Expected
        (mtFiber22RowAt 9) (by decide) mtFiber22ReverseRow_9_ok
      simpa [mtFiber22StateAt, mtFiber22RowAt, mtFiber22Rows, listGetD, directRow] using h)

theorem mtFiber22ReverseRow_10_ok :
    mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber22Chunk5_ok
  change (mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 10) &&
    mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber22ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber22StateAt 2) (mtFiber22StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber22StateAt 2) (mtFiber22StateAt 10)
    (mtFiber22RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber22Key mtFiber22Expected
        (mtFiber22RowAt 10) (by decide) mtFiber22ReverseRow_10_ok
      simpa [mtFiber22StateAt, mtFiber22RowAt, mtFiber22Rows, listGetD, directRow] using h)

theorem mtFiber22ReverseRow_11_ok :
    mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber22Chunk5_ok
  change (mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 10) &&
    mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber22ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber22StateAt 3) (mtFiber22StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber22StateAt 3) (mtFiber22StateAt 11)
    (mtFiber22RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber22Key mtFiber22Expected
        (mtFiber22RowAt 11) (by decide) mtFiber22ReverseRow_11_ok
      simpa [mtFiber22StateAt, mtFiber22RowAt, mtFiber22Rows, listGetD, directRow] using h)

theorem mtFiber22ReverseRow_12_ok :
    mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber22Chunk6_ok
  change (mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 12) &&
    mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber22ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber22StateAt 4) (mtFiber22StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber22StateAt 4) (mtFiber22StateAt 12)
    (mtFiber22RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber22Key mtFiber22Expected
        (mtFiber22RowAt 12) (by decide) mtFiber22ReverseRow_12_ok
      simpa [mtFiber22StateAt, mtFiber22RowAt, mtFiber22Rows, listGetD, directRow] using h)

theorem mtFiber22ReverseRow_13_ok :
    mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber22Chunk6_ok
  change (mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 12) &&
    mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber22ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber22StateAt 5) (mtFiber22StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber22StateAt 5) (mtFiber22StateAt 13)
    (mtFiber22RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber22Key mtFiber22Expected
        (mtFiber22RowAt 13) (by decide) mtFiber22ReverseRow_13_ok
      simpa [mtFiber22StateAt, mtFiber22RowAt, mtFiber22Rows, listGetD, directRow] using h)

theorem mtFiber22ReverseRow_14_ok :
    mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber22Chunk7_ok
  change (mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 14) &&
    mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber22ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber22StateAt 6) (mtFiber22StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber22StateAt 6) (mtFiber22StateAt 14)
    (mtFiber22RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber22Key mtFiber22Expected
        (mtFiber22RowAt 14) (by decide) mtFiber22ReverseRow_14_ok
      simpa [mtFiber22StateAt, mtFiber22RowAt, mtFiber22Rows, listGetD, directRow] using h)

theorem mtFiber22ReverseRow_15_ok :
    mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber22Chunk7_ok
  change (mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 14) &&
    mtRowReverseValid mtFiber22Key mtFiber22Expected (mtFiber22RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber22ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber22StateAt 7) (mtFiber22StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber22StateAt 7) (mtFiber22StateAt 15)
    (mtFiber22RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber22Key mtFiber22Expected
        (mtFiber22RowAt 15) (by decide) mtFiber22ReverseRow_15_ok
      simpa [mtFiber22StateAt, mtFiber22RowAt, mtFiber22Rows, listGetD, directRow] using h)

theorem mtFiber22State0_in_close :
    mtFiber22StateAt 0 ∈ closeChainFiber mtWord mtFiber22DirectStates mtFiber22DirectStates.length [mtFiber22StateAt 0] := by
  change mtFiber22StateAt 0 ∈ closeChainFiber mtWord mtFiber22DirectStates 16 [mtFiber22StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber22DirectStates 0 16 [mtFiber22StateAt 0] (mtFiber22StateAt 0) (by simp [closeChainFiber])

theorem mtFiber22State1_in_close :
    mtFiber22StateAt 1 ∈ closeChainFiber mtWord mtFiber22DirectStates mtFiber22DirectStates.length [mtFiber22StateAt 0] := by
  have h0 : mtFiber22StateAt 0 ∈ closeChainFiber mtWord mtFiber22DirectStates 0 [mtFiber22StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber22StateAt 1 ∈ closeChainFiber mtWord mtFiber22DirectStates 1 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 0 [mtFiber22StateAt 0]
      (mtFiber22StateAt 0) (mtFiber22StateAt 1) (by decide) h0 (by decide)
      mtFiber22ReverseSingleStep1
  change mtFiber22StateAt 1 ∈ closeChainFiber mtWord mtFiber22DirectStates (1 + 15) [mtFiber22StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber22DirectStates 1 15 [mtFiber22StateAt 0] (mtFiber22StateAt 1) h1

theorem mtFiber22State2_in_close :
    mtFiber22StateAt 2 ∈ closeChainFiber mtWord mtFiber22DirectStates mtFiber22DirectStates.length [mtFiber22StateAt 0] := by
  have h0 : mtFiber22StateAt 0 ∈ closeChainFiber mtWord mtFiber22DirectStates 0 [mtFiber22StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber22StateAt 2 ∈ closeChainFiber mtWord mtFiber22DirectStates 1 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 0 [mtFiber22StateAt 0]
      (mtFiber22StateAt 0) (mtFiber22StateAt 2) (by decide) h0 (by decide)
      mtFiber22ReverseSingleStep2
  change mtFiber22StateAt 2 ∈ closeChainFiber mtWord mtFiber22DirectStates (1 + 15) [mtFiber22StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber22DirectStates 1 15 [mtFiber22StateAt 0] (mtFiber22StateAt 2) h1

theorem mtFiber22State3_in_close :
    mtFiber22StateAt 3 ∈ closeChainFiber mtWord mtFiber22DirectStates mtFiber22DirectStates.length [mtFiber22StateAt 0] := by
  have h0 : mtFiber22StateAt 0 ∈ closeChainFiber mtWord mtFiber22DirectStates 0 [mtFiber22StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber22StateAt 1 ∈ closeChainFiber mtWord mtFiber22DirectStates 1 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 0 [mtFiber22StateAt 0]
      (mtFiber22StateAt 0) (mtFiber22StateAt 1) (by decide) h0 (by decide)
      mtFiber22ReverseSingleStep1
  have h2 : mtFiber22StateAt 3 ∈ closeChainFiber mtWord mtFiber22DirectStates 2 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 1 [mtFiber22StateAt 0]
      (mtFiber22StateAt 1) (mtFiber22StateAt 3) (by decide) h1 (by decide)
      mtFiber22ReverseSingleStep3
  change mtFiber22StateAt 3 ∈ closeChainFiber mtWord mtFiber22DirectStates (2 + 14) [mtFiber22StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber22DirectStates 2 14 [mtFiber22StateAt 0] (mtFiber22StateAt 3) h2

theorem mtFiber22State4_in_close :
    mtFiber22StateAt 4 ∈ closeChainFiber mtWord mtFiber22DirectStates mtFiber22DirectStates.length [mtFiber22StateAt 0] := by
  have h0 : mtFiber22StateAt 0 ∈ closeChainFiber mtWord mtFiber22DirectStates 0 [mtFiber22StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber22StateAt 4 ∈ closeChainFiber mtWord mtFiber22DirectStates 1 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 0 [mtFiber22StateAt 0]
      (mtFiber22StateAt 0) (mtFiber22StateAt 4) (by decide) h0 (by decide)
      mtFiber22ReverseSingleStep4
  change mtFiber22StateAt 4 ∈ closeChainFiber mtWord mtFiber22DirectStates (1 + 15) [mtFiber22StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber22DirectStates 1 15 [mtFiber22StateAt 0] (mtFiber22StateAt 4) h1

theorem mtFiber22State5_in_close :
    mtFiber22StateAt 5 ∈ closeChainFiber mtWord mtFiber22DirectStates mtFiber22DirectStates.length [mtFiber22StateAt 0] := by
  have h0 : mtFiber22StateAt 0 ∈ closeChainFiber mtWord mtFiber22DirectStates 0 [mtFiber22StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber22StateAt 1 ∈ closeChainFiber mtWord mtFiber22DirectStates 1 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 0 [mtFiber22StateAt 0]
      (mtFiber22StateAt 0) (mtFiber22StateAt 1) (by decide) h0 (by decide)
      mtFiber22ReverseSingleStep1
  have h2 : mtFiber22StateAt 5 ∈ closeChainFiber mtWord mtFiber22DirectStates 2 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 1 [mtFiber22StateAt 0]
      (mtFiber22StateAt 1) (mtFiber22StateAt 5) (by decide) h1 (by decide)
      mtFiber22ReverseSingleStep5
  change mtFiber22StateAt 5 ∈ closeChainFiber mtWord mtFiber22DirectStates (2 + 14) [mtFiber22StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber22DirectStates 2 14 [mtFiber22StateAt 0] (mtFiber22StateAt 5) h2

theorem mtFiber22State6_in_close :
    mtFiber22StateAt 6 ∈ closeChainFiber mtWord mtFiber22DirectStates mtFiber22DirectStates.length [mtFiber22StateAt 0] := by
  have h0 : mtFiber22StateAt 0 ∈ closeChainFiber mtWord mtFiber22DirectStates 0 [mtFiber22StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber22StateAt 2 ∈ closeChainFiber mtWord mtFiber22DirectStates 1 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 0 [mtFiber22StateAt 0]
      (mtFiber22StateAt 0) (mtFiber22StateAt 2) (by decide) h0 (by decide)
      mtFiber22ReverseSingleStep2
  have h2 : mtFiber22StateAt 6 ∈ closeChainFiber mtWord mtFiber22DirectStates 2 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 1 [mtFiber22StateAt 0]
      (mtFiber22StateAt 2) (mtFiber22StateAt 6) (by decide) h1 (by decide)
      mtFiber22ReverseSingleStep6
  change mtFiber22StateAt 6 ∈ closeChainFiber mtWord mtFiber22DirectStates (2 + 14) [mtFiber22StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber22DirectStates 2 14 [mtFiber22StateAt 0] (mtFiber22StateAt 6) h2

theorem mtFiber22State7_in_close :
    mtFiber22StateAt 7 ∈ closeChainFiber mtWord mtFiber22DirectStates mtFiber22DirectStates.length [mtFiber22StateAt 0] := by
  have h0 : mtFiber22StateAt 0 ∈ closeChainFiber mtWord mtFiber22DirectStates 0 [mtFiber22StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber22StateAt 1 ∈ closeChainFiber mtWord mtFiber22DirectStates 1 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 0 [mtFiber22StateAt 0]
      (mtFiber22StateAt 0) (mtFiber22StateAt 1) (by decide) h0 (by decide)
      mtFiber22ReverseSingleStep1
  have h2 : mtFiber22StateAt 3 ∈ closeChainFiber mtWord mtFiber22DirectStates 2 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 1 [mtFiber22StateAt 0]
      (mtFiber22StateAt 1) (mtFiber22StateAt 3) (by decide) h1 (by decide)
      mtFiber22ReverseSingleStep3
  have h3 : mtFiber22StateAt 7 ∈ closeChainFiber mtWord mtFiber22DirectStates 3 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 2 [mtFiber22StateAt 0]
      (mtFiber22StateAt 3) (mtFiber22StateAt 7) (by decide) h2 (by decide)
      mtFiber22ReverseSingleStep7
  change mtFiber22StateAt 7 ∈ closeChainFiber mtWord mtFiber22DirectStates (3 + 13) [mtFiber22StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber22DirectStates 3 13 [mtFiber22StateAt 0] (mtFiber22StateAt 7) h3

theorem mtFiber22State8_in_close :
    mtFiber22StateAt 8 ∈ closeChainFiber mtWord mtFiber22DirectStates mtFiber22DirectStates.length [mtFiber22StateAt 0] := by
  have h0 : mtFiber22StateAt 0 ∈ closeChainFiber mtWord mtFiber22DirectStates 0 [mtFiber22StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber22StateAt 8 ∈ closeChainFiber mtWord mtFiber22DirectStates 1 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 0 [mtFiber22StateAt 0]
      (mtFiber22StateAt 0) (mtFiber22StateAt 8) (by decide) h0 (by decide)
      mtFiber22ReverseSingleStep8
  change mtFiber22StateAt 8 ∈ closeChainFiber mtWord mtFiber22DirectStates (1 + 15) [mtFiber22StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber22DirectStates 1 15 [mtFiber22StateAt 0] (mtFiber22StateAt 8) h1

theorem mtFiber22State9_in_close :
    mtFiber22StateAt 9 ∈ closeChainFiber mtWord mtFiber22DirectStates mtFiber22DirectStates.length [mtFiber22StateAt 0] := by
  have h0 : mtFiber22StateAt 0 ∈ closeChainFiber mtWord mtFiber22DirectStates 0 [mtFiber22StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber22StateAt 1 ∈ closeChainFiber mtWord mtFiber22DirectStates 1 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 0 [mtFiber22StateAt 0]
      (mtFiber22StateAt 0) (mtFiber22StateAt 1) (by decide) h0 (by decide)
      mtFiber22ReverseSingleStep1
  have h2 : mtFiber22StateAt 9 ∈ closeChainFiber mtWord mtFiber22DirectStates 2 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 1 [mtFiber22StateAt 0]
      (mtFiber22StateAt 1) (mtFiber22StateAt 9) (by decide) h1 (by decide)
      mtFiber22ReverseSingleStep9
  change mtFiber22StateAt 9 ∈ closeChainFiber mtWord mtFiber22DirectStates (2 + 14) [mtFiber22StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber22DirectStates 2 14 [mtFiber22StateAt 0] (mtFiber22StateAt 9) h2

theorem mtFiber22State10_in_close :
    mtFiber22StateAt 10 ∈ closeChainFiber mtWord mtFiber22DirectStates mtFiber22DirectStates.length [mtFiber22StateAt 0] := by
  have h0 : mtFiber22StateAt 0 ∈ closeChainFiber mtWord mtFiber22DirectStates 0 [mtFiber22StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber22StateAt 2 ∈ closeChainFiber mtWord mtFiber22DirectStates 1 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 0 [mtFiber22StateAt 0]
      (mtFiber22StateAt 0) (mtFiber22StateAt 2) (by decide) h0 (by decide)
      mtFiber22ReverseSingleStep2
  have h2 : mtFiber22StateAt 10 ∈ closeChainFiber mtWord mtFiber22DirectStates 2 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 1 [mtFiber22StateAt 0]
      (mtFiber22StateAt 2) (mtFiber22StateAt 10) (by decide) h1 (by decide)
      mtFiber22ReverseSingleStep10
  change mtFiber22StateAt 10 ∈ closeChainFiber mtWord mtFiber22DirectStates (2 + 14) [mtFiber22StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber22DirectStates 2 14 [mtFiber22StateAt 0] (mtFiber22StateAt 10) h2

theorem mtFiber22State11_in_close :
    mtFiber22StateAt 11 ∈ closeChainFiber mtWord mtFiber22DirectStates mtFiber22DirectStates.length [mtFiber22StateAt 0] := by
  have h0 : mtFiber22StateAt 0 ∈ closeChainFiber mtWord mtFiber22DirectStates 0 [mtFiber22StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber22StateAt 1 ∈ closeChainFiber mtWord mtFiber22DirectStates 1 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 0 [mtFiber22StateAt 0]
      (mtFiber22StateAt 0) (mtFiber22StateAt 1) (by decide) h0 (by decide)
      mtFiber22ReverseSingleStep1
  have h2 : mtFiber22StateAt 3 ∈ closeChainFiber mtWord mtFiber22DirectStates 2 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 1 [mtFiber22StateAt 0]
      (mtFiber22StateAt 1) (mtFiber22StateAt 3) (by decide) h1 (by decide)
      mtFiber22ReverseSingleStep3
  have h3 : mtFiber22StateAt 11 ∈ closeChainFiber mtWord mtFiber22DirectStates 3 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 2 [mtFiber22StateAt 0]
      (mtFiber22StateAt 3) (mtFiber22StateAt 11) (by decide) h2 (by decide)
      mtFiber22ReverseSingleStep11
  change mtFiber22StateAt 11 ∈ closeChainFiber mtWord mtFiber22DirectStates (3 + 13) [mtFiber22StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber22DirectStates 3 13 [mtFiber22StateAt 0] (mtFiber22StateAt 11) h3

theorem mtFiber22State12_in_close :
    mtFiber22StateAt 12 ∈ closeChainFiber mtWord mtFiber22DirectStates mtFiber22DirectStates.length [mtFiber22StateAt 0] := by
  have h0 : mtFiber22StateAt 0 ∈ closeChainFiber mtWord mtFiber22DirectStates 0 [mtFiber22StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber22StateAt 4 ∈ closeChainFiber mtWord mtFiber22DirectStates 1 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 0 [mtFiber22StateAt 0]
      (mtFiber22StateAt 0) (mtFiber22StateAt 4) (by decide) h0 (by decide)
      mtFiber22ReverseSingleStep4
  have h2 : mtFiber22StateAt 12 ∈ closeChainFiber mtWord mtFiber22DirectStates 2 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 1 [mtFiber22StateAt 0]
      (mtFiber22StateAt 4) (mtFiber22StateAt 12) (by decide) h1 (by decide)
      mtFiber22ReverseSingleStep12
  change mtFiber22StateAt 12 ∈ closeChainFiber mtWord mtFiber22DirectStates (2 + 14) [mtFiber22StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber22DirectStates 2 14 [mtFiber22StateAt 0] (mtFiber22StateAt 12) h2

theorem mtFiber22State13_in_close :
    mtFiber22StateAt 13 ∈ closeChainFiber mtWord mtFiber22DirectStates mtFiber22DirectStates.length [mtFiber22StateAt 0] := by
  have h0 : mtFiber22StateAt 0 ∈ closeChainFiber mtWord mtFiber22DirectStates 0 [mtFiber22StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber22StateAt 1 ∈ closeChainFiber mtWord mtFiber22DirectStates 1 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 0 [mtFiber22StateAt 0]
      (mtFiber22StateAt 0) (mtFiber22StateAt 1) (by decide) h0 (by decide)
      mtFiber22ReverseSingleStep1
  have h2 : mtFiber22StateAt 5 ∈ closeChainFiber mtWord mtFiber22DirectStates 2 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 1 [mtFiber22StateAt 0]
      (mtFiber22StateAt 1) (mtFiber22StateAt 5) (by decide) h1 (by decide)
      mtFiber22ReverseSingleStep5
  have h3 : mtFiber22StateAt 13 ∈ closeChainFiber mtWord mtFiber22DirectStates 3 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 2 [mtFiber22StateAt 0]
      (mtFiber22StateAt 5) (mtFiber22StateAt 13) (by decide) h2 (by decide)
      mtFiber22ReverseSingleStep13
  change mtFiber22StateAt 13 ∈ closeChainFiber mtWord mtFiber22DirectStates (3 + 13) [mtFiber22StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber22DirectStates 3 13 [mtFiber22StateAt 0] (mtFiber22StateAt 13) h3

theorem mtFiber22State14_in_close :
    mtFiber22StateAt 14 ∈ closeChainFiber mtWord mtFiber22DirectStates mtFiber22DirectStates.length [mtFiber22StateAt 0] := by
  have h0 : mtFiber22StateAt 0 ∈ closeChainFiber mtWord mtFiber22DirectStates 0 [mtFiber22StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber22StateAt 2 ∈ closeChainFiber mtWord mtFiber22DirectStates 1 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 0 [mtFiber22StateAt 0]
      (mtFiber22StateAt 0) (mtFiber22StateAt 2) (by decide) h0 (by decide)
      mtFiber22ReverseSingleStep2
  have h2 : mtFiber22StateAt 6 ∈ closeChainFiber mtWord mtFiber22DirectStates 2 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 1 [mtFiber22StateAt 0]
      (mtFiber22StateAt 2) (mtFiber22StateAt 6) (by decide) h1 (by decide)
      mtFiber22ReverseSingleStep6
  have h3 : mtFiber22StateAt 14 ∈ closeChainFiber mtWord mtFiber22DirectStates 3 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 2 [mtFiber22StateAt 0]
      (mtFiber22StateAt 6) (mtFiber22StateAt 14) (by decide) h2 (by decide)
      mtFiber22ReverseSingleStep14
  change mtFiber22StateAt 14 ∈ closeChainFiber mtWord mtFiber22DirectStates (3 + 13) [mtFiber22StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber22DirectStates 3 13 [mtFiber22StateAt 0] (mtFiber22StateAt 14) h3

theorem mtFiber22State15_in_close :
    mtFiber22StateAt 15 ∈ closeChainFiber mtWord mtFiber22DirectStates mtFiber22DirectStates.length [mtFiber22StateAt 0] := by
  have h0 : mtFiber22StateAt 0 ∈ closeChainFiber mtWord mtFiber22DirectStates 0 [mtFiber22StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber22StateAt 1 ∈ closeChainFiber mtWord mtFiber22DirectStates 1 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 0 [mtFiber22StateAt 0]
      (mtFiber22StateAt 0) (mtFiber22StateAt 1) (by decide) h0 (by decide)
      mtFiber22ReverseSingleStep1
  have h2 : mtFiber22StateAt 3 ∈ closeChainFiber mtWord mtFiber22DirectStates 2 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 1 [mtFiber22StateAt 0]
      (mtFiber22StateAt 1) (mtFiber22StateAt 3) (by decide) h1 (by decide)
      mtFiber22ReverseSingleStep3
  have h3 : mtFiber22StateAt 7 ∈ closeChainFiber mtWord mtFiber22DirectStates 3 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 2 [mtFiber22StateAt 0]
      (mtFiber22StateAt 3) (mtFiber22StateAt 7) (by decide) h2 (by decide)
      mtFiber22ReverseSingleStep7
  have h4 : mtFiber22StateAt 15 ∈ closeChainFiber mtWord mtFiber22DirectStates 4 [mtFiber22StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber22DirectStates 3 [mtFiber22StateAt 0]
      (mtFiber22StateAt 7) (mtFiber22StateAt 15) (by decide) h3 (by decide)
      mtFiber22ReverseSingleStep15
  change mtFiber22StateAt 15 ∈ closeChainFiber mtWord mtFiber22DirectStates (4 + 12) [mtFiber22StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber22DirectStates 4 12 [mtFiber22StateAt 0] (mtFiber22StateAt 15) h4

theorem mtFiber22DirectConnected :
    chainFiberConnected mtWord mtFiber22DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber22DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber22State0_in_close
  · subst state
    exact mtFiber22State1_in_close
  · subst state
    exact mtFiber22State2_in_close
  · subst state
    exact mtFiber22State3_in_close
  · subst state
    exact mtFiber22State4_in_close
  · subst state
    exact mtFiber22State5_in_close
  · subst state
    exact mtFiber22State6_in_close
  · subst state
    exact mtFiber22State7_in_close
  · subst state
    exact mtFiber22State8_in_close
  · subst state
    exact mtFiber22State9_in_close
  · subst state
    exact mtFiber22State10_in_close
  · subst state
    exact mtFiber22State11_in_close
  · subst state
    exact mtFiber22State12_in_close
  · subst state
    exact mtFiber22State13_in_close
  · subst state
    exact mtFiber22State14_in_close
  · subst state
    exact mtFiber22State15_in_close
  · cases h
def mtFiber23StateAt (i : Nat) : List TauState :=
  directStates (mtFiber23RowAt i).sourceLeft (mtFiber23RowAt i).sourceRight

def mtFiber23DirectStates : List (List TauState) :=
  [mtFiber23StateAt 0, mtFiber23StateAt 1, mtFiber23StateAt 2, mtFiber23StateAt 3, mtFiber23StateAt 4, mtFiber23StateAt 5, mtFiber23StateAt 6, mtFiber23StateAt 7, mtFiber23StateAt 8, mtFiber23StateAt 9, mtFiber23StateAt 10, mtFiber23StateAt 11, mtFiber23StateAt 12, mtFiber23StateAt 13, mtFiber23StateAt 14, mtFiber23StateAt 15]

theorem mtFiber23ReverseRow_1_ok :
    mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 1) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber23Chunk0_ok
  change (mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 0) &&
    mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber23ReverseSingleStep1 :
    chainSingleKempeStep mtWord (mtFiber23StateAt 0) (mtFiber23StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber23StateAt 0) (mtFiber23StateAt 1)
    (mtFiber23RowAt 1).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber23Key mtFiber23Expected
        (mtFiber23RowAt 1) (by decide) mtFiber23ReverseRow_1_ok
      simpa [mtFiber23StateAt, mtFiber23RowAt, mtFiber23Rows, listGetD, directRow] using h)

theorem mtFiber23ReverseRow_2_ok :
    mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 2) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber23Chunk1_ok
  change (mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 2) &&
    mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber23ReverseSingleStep2 :
    chainSingleKempeStep mtWord (mtFiber23StateAt 1) (mtFiber23StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber23StateAt 1) (mtFiber23StateAt 2)
    (mtFiber23RowAt 2).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber23Key mtFiber23Expected
        (mtFiber23RowAt 2) (by decide) mtFiber23ReverseRow_2_ok
      simpa [mtFiber23StateAt, mtFiber23RowAt, mtFiber23Rows, listGetD, directRow] using h)

theorem mtFiber23ReverseRow_3_ok :
    mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 3) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber23Chunk1_ok
  change (mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 2) &&
    mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber23ReverseSingleStep3 :
    chainSingleKempeStep mtWord (mtFiber23StateAt 0) (mtFiber23StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber23StateAt 0) (mtFiber23StateAt 3)
    (mtFiber23RowAt 3).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber23Key mtFiber23Expected
        (mtFiber23RowAt 3) (by decide) mtFiber23ReverseRow_3_ok
      simpa [mtFiber23StateAt, mtFiber23RowAt, mtFiber23Rows, listGetD, directRow] using h)

theorem mtFiber23ReverseRow_4_ok :
    mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 4) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber23Chunk2_ok
  change (mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 4) &&
    mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber23ReverseSingleStep4 :
    chainSingleKempeStep mtWord (mtFiber23StateAt 0) (mtFiber23StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber23StateAt 0) (mtFiber23StateAt 4)
    (mtFiber23RowAt 4).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber23Key mtFiber23Expected
        (mtFiber23RowAt 4) (by decide) mtFiber23ReverseRow_4_ok
      simpa [mtFiber23StateAt, mtFiber23RowAt, mtFiber23Rows, listGetD, directRow] using h)

theorem mtFiber23ReverseRow_5_ok :
    mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 5) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber23Chunk2_ok
  change (mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 4) &&
    mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber23ReverseSingleStep5 :
    chainSingleKempeStep mtWord (mtFiber23StateAt 1) (mtFiber23StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber23StateAt 1) (mtFiber23StateAt 5)
    (mtFiber23RowAt 5).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber23Key mtFiber23Expected
        (mtFiber23RowAt 5) (by decide) mtFiber23ReverseRow_5_ok
      simpa [mtFiber23StateAt, mtFiber23RowAt, mtFiber23Rows, listGetD, directRow] using h)

theorem mtFiber23ReverseRow_6_ok :
    mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 6) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber23Chunk3_ok
  change (mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 6) &&
    mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber23ReverseSingleStep6 :
    chainSingleKempeStep mtWord (mtFiber23StateAt 2) (mtFiber23StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber23StateAt 2) (mtFiber23StateAt 6)
    (mtFiber23RowAt 6).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber23Key mtFiber23Expected
        (mtFiber23RowAt 6) (by decide) mtFiber23ReverseRow_6_ok
      simpa [mtFiber23StateAt, mtFiber23RowAt, mtFiber23Rows, listGetD, directRow] using h)

theorem mtFiber23ReverseRow_7_ok :
    mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 7) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber23Chunk3_ok
  change (mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 6) &&
    mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber23ReverseSingleStep7 :
    chainSingleKempeStep mtWord (mtFiber23StateAt 3) (mtFiber23StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber23StateAt 3) (mtFiber23StateAt 7)
    (mtFiber23RowAt 7).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber23Key mtFiber23Expected
        (mtFiber23RowAt 7) (by decide) mtFiber23ReverseRow_7_ok
      simpa [mtFiber23StateAt, mtFiber23RowAt, mtFiber23Rows, listGetD, directRow] using h)

theorem mtFiber23ReverseRow_8_ok :
    mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 8) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber23Chunk4_ok
  change (mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 8) &&
    mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber23ReverseSingleStep8 :
    chainSingleKempeStep mtWord (mtFiber23StateAt 0) (mtFiber23StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber23StateAt 0) (mtFiber23StateAt 8)
    (mtFiber23RowAt 8).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber23Key mtFiber23Expected
        (mtFiber23RowAt 8) (by decide) mtFiber23ReverseRow_8_ok
      simpa [mtFiber23StateAt, mtFiber23RowAt, mtFiber23Rows, listGetD, directRow] using h)

theorem mtFiber23ReverseRow_9_ok :
    mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 9) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber23Chunk4_ok
  change (mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 8) &&
    mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber23ReverseSingleStep9 :
    chainSingleKempeStep mtWord (mtFiber23StateAt 1) (mtFiber23StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber23StateAt 1) (mtFiber23StateAt 9)
    (mtFiber23RowAt 9).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber23Key mtFiber23Expected
        (mtFiber23RowAt 9) (by decide) mtFiber23ReverseRow_9_ok
      simpa [mtFiber23StateAt, mtFiber23RowAt, mtFiber23Rows, listGetD, directRow] using h)

theorem mtFiber23ReverseRow_10_ok :
    mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 10) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber23Chunk5_ok
  change (mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 10) &&
    mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber23ReverseSingleStep10 :
    chainSingleKempeStep mtWord (mtFiber23StateAt 2) (mtFiber23StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber23StateAt 2) (mtFiber23StateAt 10)
    (mtFiber23RowAt 10).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber23Key mtFiber23Expected
        (mtFiber23RowAt 10) (by decide) mtFiber23ReverseRow_10_ok
      simpa [mtFiber23StateAt, mtFiber23RowAt, mtFiber23Rows, listGetD, directRow] using h)

theorem mtFiber23ReverseRow_11_ok :
    mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 11) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber23Chunk5_ok
  change (mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 10) &&
    mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber23ReverseSingleStep11 :
    chainSingleKempeStep mtWord (mtFiber23StateAt 3) (mtFiber23StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber23StateAt 3) (mtFiber23StateAt 11)
    (mtFiber23RowAt 11).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber23Key mtFiber23Expected
        (mtFiber23RowAt 11) (by decide) mtFiber23ReverseRow_11_ok
      simpa [mtFiber23StateAt, mtFiber23RowAt, mtFiber23Rows, listGetD, directRow] using h)

theorem mtFiber23ReverseRow_12_ok :
    mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 12) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber23Chunk6_ok
  change (mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 12) &&
    mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber23ReverseSingleStep12 :
    chainSingleKempeStep mtWord (mtFiber23StateAt 4) (mtFiber23StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber23StateAt 4) (mtFiber23StateAt 12)
    (mtFiber23RowAt 12).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber23Key mtFiber23Expected
        (mtFiber23RowAt 12) (by decide) mtFiber23ReverseRow_12_ok
      simpa [mtFiber23StateAt, mtFiber23RowAt, mtFiber23Rows, listGetD, directRow] using h)

theorem mtFiber23ReverseRow_13_ok :
    mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 13) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber23Chunk6_ok
  change (mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 12) &&
    mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber23ReverseSingleStep13 :
    chainSingleKempeStep mtWord (mtFiber23StateAt 5) (mtFiber23StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber23StateAt 5) (mtFiber23StateAt 13)
    (mtFiber23RowAt 13).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber23Key mtFiber23Expected
        (mtFiber23RowAt 13) (by decide) mtFiber23ReverseRow_13_ok
      simpa [mtFiber23StateAt, mtFiber23RowAt, mtFiber23Rows, listGetD, directRow] using h)

theorem mtFiber23ReverseRow_14_ok :
    mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 14) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber23Chunk7_ok
  change (mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 14) &&
    mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem mtFiber23ReverseSingleStep14 :
    chainSingleKempeStep mtWord (mtFiber23StateAt 6) (mtFiber23StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber23StateAt 6) (mtFiber23StateAt 14)
    (mtFiber23RowAt 14).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber23Key mtFiber23Expected
        (mtFiber23RowAt 14) (by decide) mtFiber23ReverseRow_14_ok
      simpa [mtFiber23StateAt, mtFiber23RowAt, mtFiber23Rows, listGetD, directRow] using h)

theorem mtFiber23ReverseRow_15_ok :
    mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 15) = true := by
  have h := GoertzelLemma818MirrorTauReverseAudit.mtReverseFiber23Chunk7_ok
  change (mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 14) &&
    mtRowReverseValid mtFiber23Key mtFiber23Expected (mtFiber23RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem mtFiber23ReverseSingleStep15 :
    chainSingleKempeStep mtWord (mtFiber23StateAt 7) (mtFiber23StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single mtWord (mtFiber23StateAt 7) (mtFiber23StateAt 15)
    (mtFiber23RowAt 15).move (by decide) (by decide) (by
      have h := mtRowReverseValid_step_of_ne mtFiber23Key mtFiber23Expected
        (mtFiber23RowAt 15) (by decide) mtFiber23ReverseRow_15_ok
      simpa [mtFiber23StateAt, mtFiber23RowAt, mtFiber23Rows, listGetD, directRow] using h)

theorem mtFiber23State0_in_close :
    mtFiber23StateAt 0 ∈ closeChainFiber mtWord mtFiber23DirectStates mtFiber23DirectStates.length [mtFiber23StateAt 0] := by
  change mtFiber23StateAt 0 ∈ closeChainFiber mtWord mtFiber23DirectStates 16 [mtFiber23StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber23DirectStates 0 16 [mtFiber23StateAt 0] (mtFiber23StateAt 0) (by simp [closeChainFiber])

theorem mtFiber23State1_in_close :
    mtFiber23StateAt 1 ∈ closeChainFiber mtWord mtFiber23DirectStates mtFiber23DirectStates.length [mtFiber23StateAt 0] := by
  have h0 : mtFiber23StateAt 0 ∈ closeChainFiber mtWord mtFiber23DirectStates 0 [mtFiber23StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber23StateAt 1 ∈ closeChainFiber mtWord mtFiber23DirectStates 1 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 0 [mtFiber23StateAt 0]
      (mtFiber23StateAt 0) (mtFiber23StateAt 1) (by decide) h0 (by decide)
      mtFiber23ReverseSingleStep1
  change mtFiber23StateAt 1 ∈ closeChainFiber mtWord mtFiber23DirectStates (1 + 15) [mtFiber23StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber23DirectStates 1 15 [mtFiber23StateAt 0] (mtFiber23StateAt 1) h1

theorem mtFiber23State2_in_close :
    mtFiber23StateAt 2 ∈ closeChainFiber mtWord mtFiber23DirectStates mtFiber23DirectStates.length [mtFiber23StateAt 0] := by
  have h0 : mtFiber23StateAt 0 ∈ closeChainFiber mtWord mtFiber23DirectStates 0 [mtFiber23StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber23StateAt 1 ∈ closeChainFiber mtWord mtFiber23DirectStates 1 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 0 [mtFiber23StateAt 0]
      (mtFiber23StateAt 0) (mtFiber23StateAt 1) (by decide) h0 (by decide)
      mtFiber23ReverseSingleStep1
  have h2 : mtFiber23StateAt 2 ∈ closeChainFiber mtWord mtFiber23DirectStates 2 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 1 [mtFiber23StateAt 0]
      (mtFiber23StateAt 1) (mtFiber23StateAt 2) (by decide) h1 (by decide)
      mtFiber23ReverseSingleStep2
  change mtFiber23StateAt 2 ∈ closeChainFiber mtWord mtFiber23DirectStates (2 + 14) [mtFiber23StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber23DirectStates 2 14 [mtFiber23StateAt 0] (mtFiber23StateAt 2) h2

theorem mtFiber23State3_in_close :
    mtFiber23StateAt 3 ∈ closeChainFiber mtWord mtFiber23DirectStates mtFiber23DirectStates.length [mtFiber23StateAt 0] := by
  have h0 : mtFiber23StateAt 0 ∈ closeChainFiber mtWord mtFiber23DirectStates 0 [mtFiber23StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber23StateAt 3 ∈ closeChainFiber mtWord mtFiber23DirectStates 1 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 0 [mtFiber23StateAt 0]
      (mtFiber23StateAt 0) (mtFiber23StateAt 3) (by decide) h0 (by decide)
      mtFiber23ReverseSingleStep3
  change mtFiber23StateAt 3 ∈ closeChainFiber mtWord mtFiber23DirectStates (1 + 15) [mtFiber23StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber23DirectStates 1 15 [mtFiber23StateAt 0] (mtFiber23StateAt 3) h1

theorem mtFiber23State4_in_close :
    mtFiber23StateAt 4 ∈ closeChainFiber mtWord mtFiber23DirectStates mtFiber23DirectStates.length [mtFiber23StateAt 0] := by
  have h0 : mtFiber23StateAt 0 ∈ closeChainFiber mtWord mtFiber23DirectStates 0 [mtFiber23StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber23StateAt 4 ∈ closeChainFiber mtWord mtFiber23DirectStates 1 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 0 [mtFiber23StateAt 0]
      (mtFiber23StateAt 0) (mtFiber23StateAt 4) (by decide) h0 (by decide)
      mtFiber23ReverseSingleStep4
  change mtFiber23StateAt 4 ∈ closeChainFiber mtWord mtFiber23DirectStates (1 + 15) [mtFiber23StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber23DirectStates 1 15 [mtFiber23StateAt 0] (mtFiber23StateAt 4) h1

theorem mtFiber23State5_in_close :
    mtFiber23StateAt 5 ∈ closeChainFiber mtWord mtFiber23DirectStates mtFiber23DirectStates.length [mtFiber23StateAt 0] := by
  have h0 : mtFiber23StateAt 0 ∈ closeChainFiber mtWord mtFiber23DirectStates 0 [mtFiber23StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber23StateAt 1 ∈ closeChainFiber mtWord mtFiber23DirectStates 1 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 0 [mtFiber23StateAt 0]
      (mtFiber23StateAt 0) (mtFiber23StateAt 1) (by decide) h0 (by decide)
      mtFiber23ReverseSingleStep1
  have h2 : mtFiber23StateAt 5 ∈ closeChainFiber mtWord mtFiber23DirectStates 2 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 1 [mtFiber23StateAt 0]
      (mtFiber23StateAt 1) (mtFiber23StateAt 5) (by decide) h1 (by decide)
      mtFiber23ReverseSingleStep5
  change mtFiber23StateAt 5 ∈ closeChainFiber mtWord mtFiber23DirectStates (2 + 14) [mtFiber23StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber23DirectStates 2 14 [mtFiber23StateAt 0] (mtFiber23StateAt 5) h2

theorem mtFiber23State6_in_close :
    mtFiber23StateAt 6 ∈ closeChainFiber mtWord mtFiber23DirectStates mtFiber23DirectStates.length [mtFiber23StateAt 0] := by
  have h0 : mtFiber23StateAt 0 ∈ closeChainFiber mtWord mtFiber23DirectStates 0 [mtFiber23StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber23StateAt 1 ∈ closeChainFiber mtWord mtFiber23DirectStates 1 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 0 [mtFiber23StateAt 0]
      (mtFiber23StateAt 0) (mtFiber23StateAt 1) (by decide) h0 (by decide)
      mtFiber23ReverseSingleStep1
  have h2 : mtFiber23StateAt 2 ∈ closeChainFiber mtWord mtFiber23DirectStates 2 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 1 [mtFiber23StateAt 0]
      (mtFiber23StateAt 1) (mtFiber23StateAt 2) (by decide) h1 (by decide)
      mtFiber23ReverseSingleStep2
  have h3 : mtFiber23StateAt 6 ∈ closeChainFiber mtWord mtFiber23DirectStates 3 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 2 [mtFiber23StateAt 0]
      (mtFiber23StateAt 2) (mtFiber23StateAt 6) (by decide) h2 (by decide)
      mtFiber23ReverseSingleStep6
  change mtFiber23StateAt 6 ∈ closeChainFiber mtWord mtFiber23DirectStates (3 + 13) [mtFiber23StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber23DirectStates 3 13 [mtFiber23StateAt 0] (mtFiber23StateAt 6) h3

theorem mtFiber23State7_in_close :
    mtFiber23StateAt 7 ∈ closeChainFiber mtWord mtFiber23DirectStates mtFiber23DirectStates.length [mtFiber23StateAt 0] := by
  have h0 : mtFiber23StateAt 0 ∈ closeChainFiber mtWord mtFiber23DirectStates 0 [mtFiber23StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber23StateAt 3 ∈ closeChainFiber mtWord mtFiber23DirectStates 1 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 0 [mtFiber23StateAt 0]
      (mtFiber23StateAt 0) (mtFiber23StateAt 3) (by decide) h0 (by decide)
      mtFiber23ReverseSingleStep3
  have h2 : mtFiber23StateAt 7 ∈ closeChainFiber mtWord mtFiber23DirectStates 2 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 1 [mtFiber23StateAt 0]
      (mtFiber23StateAt 3) (mtFiber23StateAt 7) (by decide) h1 (by decide)
      mtFiber23ReverseSingleStep7
  change mtFiber23StateAt 7 ∈ closeChainFiber mtWord mtFiber23DirectStates (2 + 14) [mtFiber23StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber23DirectStates 2 14 [mtFiber23StateAt 0] (mtFiber23StateAt 7) h2

theorem mtFiber23State8_in_close :
    mtFiber23StateAt 8 ∈ closeChainFiber mtWord mtFiber23DirectStates mtFiber23DirectStates.length [mtFiber23StateAt 0] := by
  have h0 : mtFiber23StateAt 0 ∈ closeChainFiber mtWord mtFiber23DirectStates 0 [mtFiber23StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber23StateAt 8 ∈ closeChainFiber mtWord mtFiber23DirectStates 1 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 0 [mtFiber23StateAt 0]
      (mtFiber23StateAt 0) (mtFiber23StateAt 8) (by decide) h0 (by decide)
      mtFiber23ReverseSingleStep8
  change mtFiber23StateAt 8 ∈ closeChainFiber mtWord mtFiber23DirectStates (1 + 15) [mtFiber23StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber23DirectStates 1 15 [mtFiber23StateAt 0] (mtFiber23StateAt 8) h1

theorem mtFiber23State9_in_close :
    mtFiber23StateAt 9 ∈ closeChainFiber mtWord mtFiber23DirectStates mtFiber23DirectStates.length [mtFiber23StateAt 0] := by
  have h0 : mtFiber23StateAt 0 ∈ closeChainFiber mtWord mtFiber23DirectStates 0 [mtFiber23StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber23StateAt 1 ∈ closeChainFiber mtWord mtFiber23DirectStates 1 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 0 [mtFiber23StateAt 0]
      (mtFiber23StateAt 0) (mtFiber23StateAt 1) (by decide) h0 (by decide)
      mtFiber23ReverseSingleStep1
  have h2 : mtFiber23StateAt 9 ∈ closeChainFiber mtWord mtFiber23DirectStates 2 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 1 [mtFiber23StateAt 0]
      (mtFiber23StateAt 1) (mtFiber23StateAt 9) (by decide) h1 (by decide)
      mtFiber23ReverseSingleStep9
  change mtFiber23StateAt 9 ∈ closeChainFiber mtWord mtFiber23DirectStates (2 + 14) [mtFiber23StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber23DirectStates 2 14 [mtFiber23StateAt 0] (mtFiber23StateAt 9) h2

theorem mtFiber23State10_in_close :
    mtFiber23StateAt 10 ∈ closeChainFiber mtWord mtFiber23DirectStates mtFiber23DirectStates.length [mtFiber23StateAt 0] := by
  have h0 : mtFiber23StateAt 0 ∈ closeChainFiber mtWord mtFiber23DirectStates 0 [mtFiber23StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber23StateAt 1 ∈ closeChainFiber mtWord mtFiber23DirectStates 1 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 0 [mtFiber23StateAt 0]
      (mtFiber23StateAt 0) (mtFiber23StateAt 1) (by decide) h0 (by decide)
      mtFiber23ReverseSingleStep1
  have h2 : mtFiber23StateAt 2 ∈ closeChainFiber mtWord mtFiber23DirectStates 2 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 1 [mtFiber23StateAt 0]
      (mtFiber23StateAt 1) (mtFiber23StateAt 2) (by decide) h1 (by decide)
      mtFiber23ReverseSingleStep2
  have h3 : mtFiber23StateAt 10 ∈ closeChainFiber mtWord mtFiber23DirectStates 3 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 2 [mtFiber23StateAt 0]
      (mtFiber23StateAt 2) (mtFiber23StateAt 10) (by decide) h2 (by decide)
      mtFiber23ReverseSingleStep10
  change mtFiber23StateAt 10 ∈ closeChainFiber mtWord mtFiber23DirectStates (3 + 13) [mtFiber23StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber23DirectStates 3 13 [mtFiber23StateAt 0] (mtFiber23StateAt 10) h3

theorem mtFiber23State11_in_close :
    mtFiber23StateAt 11 ∈ closeChainFiber mtWord mtFiber23DirectStates mtFiber23DirectStates.length [mtFiber23StateAt 0] := by
  have h0 : mtFiber23StateAt 0 ∈ closeChainFiber mtWord mtFiber23DirectStates 0 [mtFiber23StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber23StateAt 3 ∈ closeChainFiber mtWord mtFiber23DirectStates 1 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 0 [mtFiber23StateAt 0]
      (mtFiber23StateAt 0) (mtFiber23StateAt 3) (by decide) h0 (by decide)
      mtFiber23ReverseSingleStep3
  have h2 : mtFiber23StateAt 11 ∈ closeChainFiber mtWord mtFiber23DirectStates 2 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 1 [mtFiber23StateAt 0]
      (mtFiber23StateAt 3) (mtFiber23StateAt 11) (by decide) h1 (by decide)
      mtFiber23ReverseSingleStep11
  change mtFiber23StateAt 11 ∈ closeChainFiber mtWord mtFiber23DirectStates (2 + 14) [mtFiber23StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber23DirectStates 2 14 [mtFiber23StateAt 0] (mtFiber23StateAt 11) h2

theorem mtFiber23State12_in_close :
    mtFiber23StateAt 12 ∈ closeChainFiber mtWord mtFiber23DirectStates mtFiber23DirectStates.length [mtFiber23StateAt 0] := by
  have h0 : mtFiber23StateAt 0 ∈ closeChainFiber mtWord mtFiber23DirectStates 0 [mtFiber23StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber23StateAt 4 ∈ closeChainFiber mtWord mtFiber23DirectStates 1 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 0 [mtFiber23StateAt 0]
      (mtFiber23StateAt 0) (mtFiber23StateAt 4) (by decide) h0 (by decide)
      mtFiber23ReverseSingleStep4
  have h2 : mtFiber23StateAt 12 ∈ closeChainFiber mtWord mtFiber23DirectStates 2 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 1 [mtFiber23StateAt 0]
      (mtFiber23StateAt 4) (mtFiber23StateAt 12) (by decide) h1 (by decide)
      mtFiber23ReverseSingleStep12
  change mtFiber23StateAt 12 ∈ closeChainFiber mtWord mtFiber23DirectStates (2 + 14) [mtFiber23StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber23DirectStates 2 14 [mtFiber23StateAt 0] (mtFiber23StateAt 12) h2

theorem mtFiber23State13_in_close :
    mtFiber23StateAt 13 ∈ closeChainFiber mtWord mtFiber23DirectStates mtFiber23DirectStates.length [mtFiber23StateAt 0] := by
  have h0 : mtFiber23StateAt 0 ∈ closeChainFiber mtWord mtFiber23DirectStates 0 [mtFiber23StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber23StateAt 1 ∈ closeChainFiber mtWord mtFiber23DirectStates 1 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 0 [mtFiber23StateAt 0]
      (mtFiber23StateAt 0) (mtFiber23StateAt 1) (by decide) h0 (by decide)
      mtFiber23ReverseSingleStep1
  have h2 : mtFiber23StateAt 5 ∈ closeChainFiber mtWord mtFiber23DirectStates 2 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 1 [mtFiber23StateAt 0]
      (mtFiber23StateAt 1) (mtFiber23StateAt 5) (by decide) h1 (by decide)
      mtFiber23ReverseSingleStep5
  have h3 : mtFiber23StateAt 13 ∈ closeChainFiber mtWord mtFiber23DirectStates 3 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 2 [mtFiber23StateAt 0]
      (mtFiber23StateAt 5) (mtFiber23StateAt 13) (by decide) h2 (by decide)
      mtFiber23ReverseSingleStep13
  change mtFiber23StateAt 13 ∈ closeChainFiber mtWord mtFiber23DirectStates (3 + 13) [mtFiber23StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber23DirectStates 3 13 [mtFiber23StateAt 0] (mtFiber23StateAt 13) h3

theorem mtFiber23State14_in_close :
    mtFiber23StateAt 14 ∈ closeChainFiber mtWord mtFiber23DirectStates mtFiber23DirectStates.length [mtFiber23StateAt 0] := by
  have h0 : mtFiber23StateAt 0 ∈ closeChainFiber mtWord mtFiber23DirectStates 0 [mtFiber23StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber23StateAt 1 ∈ closeChainFiber mtWord mtFiber23DirectStates 1 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 0 [mtFiber23StateAt 0]
      (mtFiber23StateAt 0) (mtFiber23StateAt 1) (by decide) h0 (by decide)
      mtFiber23ReverseSingleStep1
  have h2 : mtFiber23StateAt 2 ∈ closeChainFiber mtWord mtFiber23DirectStates 2 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 1 [mtFiber23StateAt 0]
      (mtFiber23StateAt 1) (mtFiber23StateAt 2) (by decide) h1 (by decide)
      mtFiber23ReverseSingleStep2
  have h3 : mtFiber23StateAt 6 ∈ closeChainFiber mtWord mtFiber23DirectStates 3 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 2 [mtFiber23StateAt 0]
      (mtFiber23StateAt 2) (mtFiber23StateAt 6) (by decide) h2 (by decide)
      mtFiber23ReverseSingleStep6
  have h4 : mtFiber23StateAt 14 ∈ closeChainFiber mtWord mtFiber23DirectStates 4 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 3 [mtFiber23StateAt 0]
      (mtFiber23StateAt 6) (mtFiber23StateAt 14) (by decide) h3 (by decide)
      mtFiber23ReverseSingleStep14
  change mtFiber23StateAt 14 ∈ closeChainFiber mtWord mtFiber23DirectStates (4 + 12) [mtFiber23StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber23DirectStates 4 12 [mtFiber23StateAt 0] (mtFiber23StateAt 14) h4

theorem mtFiber23State15_in_close :
    mtFiber23StateAt 15 ∈ closeChainFiber mtWord mtFiber23DirectStates mtFiber23DirectStates.length [mtFiber23StateAt 0] := by
  have h0 : mtFiber23StateAt 0 ∈ closeChainFiber mtWord mtFiber23DirectStates 0 [mtFiber23StateAt 0] := by
    simp [closeChainFiber]
  have h1 : mtFiber23StateAt 3 ∈ closeChainFiber mtWord mtFiber23DirectStates 1 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 0 [mtFiber23StateAt 0]
      (mtFiber23StateAt 0) (mtFiber23StateAt 3) (by decide) h0 (by decide)
      mtFiber23ReverseSingleStep3
  have h2 : mtFiber23StateAt 7 ∈ closeChainFiber mtWord mtFiber23DirectStates 2 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 1 [mtFiber23StateAt 0]
      (mtFiber23StateAt 3) (mtFiber23StateAt 7) (by decide) h1 (by decide)
      mtFiber23ReverseSingleStep7
  have h3 : mtFiber23StateAt 15 ∈ closeChainFiber mtWord mtFiber23DirectStates 3 [mtFiber23StateAt 0] := by
    simpa using closeChainFiber_mem_step_of_close mtWord mtFiber23DirectStates 2 [mtFiber23StateAt 0]
      (mtFiber23StateAt 7) (mtFiber23StateAt 15) (by decide) h2 (by decide)
      mtFiber23ReverseSingleStep15
  change mtFiber23StateAt 15 ∈ closeChainFiber mtWord mtFiber23DirectStates (3 + 13) [mtFiber23StateAt 0]
  exact closeChainFiber_mem_mono_add mtWord mtFiber23DirectStates 3 13 [mtFiber23StateAt 0] (mtFiber23StateAt 15) h3

theorem mtFiber23DirectConnected :
    chainFiberConnected mtWord mtFiber23DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [mtFiber23DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact mtFiber23State0_in_close
  · subst state
    exact mtFiber23State1_in_close
  · subst state
    exact mtFiber23State2_in_close
  · subst state
    exact mtFiber23State3_in_close
  · subst state
    exact mtFiber23State4_in_close
  · subst state
    exact mtFiber23State5_in_close
  · subst state
    exact mtFiber23State6_in_close
  · subst state
    exact mtFiber23State7_in_close
  · subst state
    exact mtFiber23State8_in_close
  · subst state
    exact mtFiber23State9_in_close
  · subst state
    exact mtFiber23State10_in_close
  · subst state
    exact mtFiber23State11_in_close
  · subst state
    exact mtFiber23State12_in_close
  · subst state
    exact mtFiber23State13_in_close
  · subst state
    exact mtFiber23State14_in_close
  · subst state
    exact mtFiber23State15_in_close
  · cases h
end GoertzelLemma818LengthTwoMTBridge

end Mettapedia.GraphTheory.FourColor
