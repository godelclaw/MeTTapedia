import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for size-16 `normal,mirror` length-two fibers, group 0

This module proves direct connectedness for four generated `normal,mirror`
size-16 fibers from row-local reverse certificate chunks, keeping Lean on
default recursion limits.
-/

namespace GoertzelLemma818LengthTwoTMShape16Bridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818TauMirrorCertificate
open GoertzelLemma818TauMirrorReverseAudit

def tmFiber3StateAt (i : Nat) : List TauState :=
  directStates (tmFiber3RowAt i).sourceLeft (tmFiber3RowAt i).sourceRight

def tmFiber3DirectStates : List (List TauState) :=
  [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14, tmFiber3StateAt 15]

theorem tmFiber3ReverseRow_1_ok :
    tmRowReverseValid tmFiber3Key tmFiber3Expected (tmFiber3RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber3Chunk0_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber3Chunk0] at h
  exact h.2

theorem tmFiber3ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber3StateAt 0) (tmFiber3StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber3StateAt 0) (tmFiber3StateAt 1)
    (tmFiber3RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber3Key tmFiber3Expected
        (tmFiber3RowAt 1) (by decide) tmFiber3ReverseRow_1_ok
      simpa [tmFiber3StateAt, tmFiber3RowAt, tmFiber3Rows, listGetD, directRow] using h)

theorem tmFiber3ReverseRow_2_ok :
    tmRowReverseValid tmFiber3Key tmFiber3Expected (tmFiber3RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber3Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber3Chunk1] at h
  exact h.1

theorem tmFiber3ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber3StateAt 1) (tmFiber3StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber3StateAt 1) (tmFiber3StateAt 2)
    (tmFiber3RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber3Key tmFiber3Expected
        (tmFiber3RowAt 2) (by decide) tmFiber3ReverseRow_2_ok
      simpa [tmFiber3StateAt, tmFiber3RowAt, tmFiber3Rows, listGetD, directRow] using h)

theorem tmFiber3ReverseRow_3_ok :
    tmRowReverseValid tmFiber3Key tmFiber3Expected (tmFiber3RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber3Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber3Chunk1] at h
  exact h.2

theorem tmFiber3ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber3StateAt 0) (tmFiber3StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber3StateAt 0) (tmFiber3StateAt 3)
    (tmFiber3RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber3Key tmFiber3Expected
        (tmFiber3RowAt 3) (by decide) tmFiber3ReverseRow_3_ok
      simpa [tmFiber3StateAt, tmFiber3RowAt, tmFiber3Rows, listGetD, directRow] using h)

theorem tmFiber3ReverseRow_4_ok :
    tmRowReverseValid tmFiber3Key tmFiber3Expected (tmFiber3RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber3Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber3Chunk2] at h
  exact h.1

theorem tmFiber3ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber3StateAt 0) (tmFiber3StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber3StateAt 0) (tmFiber3StateAt 4)
    (tmFiber3RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber3Key tmFiber3Expected
        (tmFiber3RowAt 4) (by decide) tmFiber3ReverseRow_4_ok
      simpa [tmFiber3StateAt, tmFiber3RowAt, tmFiber3Rows, listGetD, directRow] using h)

theorem tmFiber3ReverseRow_5_ok :
    tmRowReverseValid tmFiber3Key tmFiber3Expected (tmFiber3RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber3Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber3Chunk2] at h
  exact h.2

theorem tmFiber3ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber3StateAt 1) (tmFiber3StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber3StateAt 1) (tmFiber3StateAt 5)
    (tmFiber3RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber3Key tmFiber3Expected
        (tmFiber3RowAt 5) (by decide) tmFiber3ReverseRow_5_ok
      simpa [tmFiber3StateAt, tmFiber3RowAt, tmFiber3Rows, listGetD, directRow] using h)

theorem tmFiber3ReverseRow_6_ok :
    tmRowReverseValid tmFiber3Key tmFiber3Expected (tmFiber3RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber3Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber3Chunk3] at h
  exact h.1

theorem tmFiber3ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber3StateAt 2) (tmFiber3StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber3StateAt 2) (tmFiber3StateAt 6)
    (tmFiber3RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber3Key tmFiber3Expected
        (tmFiber3RowAt 6) (by decide) tmFiber3ReverseRow_6_ok
      simpa [tmFiber3StateAt, tmFiber3RowAt, tmFiber3Rows, listGetD, directRow] using h)

theorem tmFiber3ReverseRow_7_ok :
    tmRowReverseValid tmFiber3Key tmFiber3Expected (tmFiber3RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber3Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber3Chunk3] at h
  exact h.2

theorem tmFiber3ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber3StateAt 3) (tmFiber3StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber3StateAt 3) (tmFiber3StateAt 7)
    (tmFiber3RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber3Key tmFiber3Expected
        (tmFiber3RowAt 7) (by decide) tmFiber3ReverseRow_7_ok
      simpa [tmFiber3StateAt, tmFiber3RowAt, tmFiber3Rows, listGetD, directRow] using h)

theorem tmFiber3ReverseRow_8_ok :
    tmRowReverseValid tmFiber3Key tmFiber3Expected (tmFiber3RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber3Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber3Chunk4] at h
  exact h.1

theorem tmFiber3ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber3StateAt 0) (tmFiber3StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber3StateAt 0) (tmFiber3StateAt 8)
    (tmFiber3RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber3Key tmFiber3Expected
        (tmFiber3RowAt 8) (by decide) tmFiber3ReverseRow_8_ok
      simpa [tmFiber3StateAt, tmFiber3RowAt, tmFiber3Rows, listGetD, directRow] using h)

theorem tmFiber3ReverseRow_9_ok :
    tmRowReverseValid tmFiber3Key tmFiber3Expected (tmFiber3RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber3Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber3Chunk4] at h
  exact h.2

theorem tmFiber3ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber3StateAt 1) (tmFiber3StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber3StateAt 1) (tmFiber3StateAt 9)
    (tmFiber3RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber3Key tmFiber3Expected
        (tmFiber3RowAt 9) (by decide) tmFiber3ReverseRow_9_ok
      simpa [tmFiber3StateAt, tmFiber3RowAt, tmFiber3Rows, listGetD, directRow] using h)

theorem tmFiber3ReverseRow_10_ok :
    tmRowReverseValid tmFiber3Key tmFiber3Expected (tmFiber3RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber3Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber3Chunk5] at h
  exact h.1

theorem tmFiber3ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber3StateAt 2) (tmFiber3StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber3StateAt 2) (tmFiber3StateAt 10)
    (tmFiber3RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber3Key tmFiber3Expected
        (tmFiber3RowAt 10) (by decide) tmFiber3ReverseRow_10_ok
      simpa [tmFiber3StateAt, tmFiber3RowAt, tmFiber3Rows, listGetD, directRow] using h)

theorem tmFiber3ReverseRow_11_ok :
    tmRowReverseValid tmFiber3Key tmFiber3Expected (tmFiber3RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber3Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber3Chunk5] at h
  exact h.2

theorem tmFiber3ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber3StateAt 3) (tmFiber3StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber3StateAt 3) (tmFiber3StateAt 11)
    (tmFiber3RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber3Key tmFiber3Expected
        (tmFiber3RowAt 11) (by decide) tmFiber3ReverseRow_11_ok
      simpa [tmFiber3StateAt, tmFiber3RowAt, tmFiber3Rows, listGetD, directRow] using h)

theorem tmFiber3ReverseRow_12_ok :
    tmRowReverseValid tmFiber3Key tmFiber3Expected (tmFiber3RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber3Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber3Chunk6] at h
  exact h.1

theorem tmFiber3ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber3StateAt 4) (tmFiber3StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber3StateAt 4) (tmFiber3StateAt 12)
    (tmFiber3RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber3Key tmFiber3Expected
        (tmFiber3RowAt 12) (by decide) tmFiber3ReverseRow_12_ok
      simpa [tmFiber3StateAt, tmFiber3RowAt, tmFiber3Rows, listGetD, directRow] using h)

theorem tmFiber3ReverseRow_13_ok :
    tmRowReverseValid tmFiber3Key tmFiber3Expected (tmFiber3RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber3Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber3Chunk6] at h
  exact h.2

theorem tmFiber3ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber3StateAt 5) (tmFiber3StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber3StateAt 5) (tmFiber3StateAt 13)
    (tmFiber3RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber3Key tmFiber3Expected
        (tmFiber3RowAt 13) (by decide) tmFiber3ReverseRow_13_ok
      simpa [tmFiber3StateAt, tmFiber3RowAt, tmFiber3Rows, listGetD, directRow] using h)

theorem tmFiber3ReverseRow_14_ok :
    tmRowReverseValid tmFiber3Key tmFiber3Expected (tmFiber3RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber3Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber3Chunk7] at h
  exact h.1

theorem tmFiber3ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber3StateAt 6) (tmFiber3StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber3StateAt 6) (tmFiber3StateAt 14)
    (tmFiber3RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber3Key tmFiber3Expected
        (tmFiber3RowAt 14) (by decide) tmFiber3ReverseRow_14_ok
      simpa [tmFiber3StateAt, tmFiber3RowAt, tmFiber3Rows, listGetD, directRow] using h)

theorem tmFiber3ReverseRow_15_ok :
    tmRowReverseValid tmFiber3Key tmFiber3Expected (tmFiber3RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber3Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber3Chunk7] at h
  exact h.2

theorem tmFiber3ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber3StateAt 7) (tmFiber3StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber3StateAt 7) (tmFiber3StateAt 15)
    (tmFiber3RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber3Key tmFiber3Expected
        (tmFiber3RowAt 15) (by decide) tmFiber3ReverseRow_15_ok
      simpa [tmFiber3StateAt, tmFiber3RowAt, tmFiber3Rows, listGetD, directRow] using h)

theorem tmFiber3State0_in_pass1_prefix :
    tmFiber3StateAt 0 ∈ chainClosureStep tmWord [tmFiber3StateAt 0] [tmFiber3StateAt 0] := by
  exact chainClosureStep_mem_of_seen tmWord [tmFiber3StateAt 0] [tmFiber3StateAt 0] (tmFiber3StateAt 0) (by simp)

theorem tmFiber3State1_in_pass1_prefix :
    tmFiber3StateAt 1 ∈ chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1] [tmFiber3StateAt 0] := by
  have hparentBefore :
      tmFiber3StateAt 0 ∈ chainClosureStep tmWord [tmFiber3StateAt 0] [tmFiber3StateAt 0] := by
    exact tmFiber3State0_in_pass1_prefix
  rw [show [tmFiber3StateAt 0, tmFiber3StateAt 1] = [tmFiber3StateAt 0] ++ [tmFiber3StateAt 1] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber3StateAt 1) []
    (chainClosureStep tmWord [tmFiber3StateAt 0] [tmFiber3StateAt 0]) (tmFiber3StateAt 0)
    hparentBefore tmFiber3ReverseSingleStep1

theorem tmFiber3State2_in_pass1_prefix :
    tmFiber3StateAt 2 ∈ chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2] [tmFiber3StateAt 0] := by
  have hparentBefore :
      tmFiber3StateAt 1 ∈ chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1] [tmFiber3StateAt 0] := by
    exact tmFiber3State1_in_pass1_prefix
  rw [show [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2] = [tmFiber3StateAt 0, tmFiber3StateAt 1] ++ [tmFiber3StateAt 2] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber3StateAt 2) []
    (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1] [tmFiber3StateAt 0]) (tmFiber3StateAt 1)
    hparentBefore tmFiber3ReverseSingleStep2

theorem tmFiber3State3_in_pass1_prefix :
    tmFiber3StateAt 3 ∈ chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3] [tmFiber3StateAt 0] := by
  have hparentBefore :
      tmFiber3StateAt 0 ∈ chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2] [tmFiber3StateAt 0] := by
    rw [show [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2] = [tmFiber3StateAt 0] ++ [tmFiber3StateAt 1, tmFiber3StateAt 2] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber3StateAt 1, tmFiber3StateAt 2]
      (chainClosureStep tmWord [tmFiber3StateAt 0] [tmFiber3StateAt 0]) (tmFiber3StateAt 0)
      tmFiber3State0_in_pass1_prefix
  rw [show [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3] = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2] ++ [tmFiber3StateAt 3] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber3StateAt 3) []
    (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2] [tmFiber3StateAt 0]) (tmFiber3StateAt 0)
    hparentBefore tmFiber3ReverseSingleStep3

theorem tmFiber3State4_in_pass1_prefix :
    tmFiber3StateAt 4 ∈ chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4] [tmFiber3StateAt 0] := by
  have hparentBefore :
      tmFiber3StateAt 0 ∈ chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3] [tmFiber3StateAt 0] := by
    rw [show [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3] = [tmFiber3StateAt 0] ++ [tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3]
      (chainClosureStep tmWord [tmFiber3StateAt 0] [tmFiber3StateAt 0]) (tmFiber3StateAt 0)
      tmFiber3State0_in_pass1_prefix
  rw [show [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4] = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3] ++ [tmFiber3StateAt 4] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber3StateAt 4) []
    (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3] [tmFiber3StateAt 0]) (tmFiber3StateAt 0)
    hparentBefore tmFiber3ReverseSingleStep4

theorem tmFiber3State5_in_pass1_prefix :
    tmFiber3StateAt 5 ∈ chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5] [tmFiber3StateAt 0] := by
  have hparentBefore :
      tmFiber3StateAt 1 ∈ chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4] [tmFiber3StateAt 0] := by
    rw [show [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4] = [tmFiber3StateAt 0, tmFiber3StateAt 1] ++ [tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4]
      (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1] [tmFiber3StateAt 0]) (tmFiber3StateAt 1)
      tmFiber3State1_in_pass1_prefix
  rw [show [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5] = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4] ++ [tmFiber3StateAt 5] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber3StateAt 5) []
    (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4] [tmFiber3StateAt 0]) (tmFiber3StateAt 1)
    hparentBefore tmFiber3ReverseSingleStep5

theorem tmFiber3State6_in_pass1_prefix :
    tmFiber3StateAt 6 ∈ chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6] [tmFiber3StateAt 0] := by
  have hparentBefore :
      tmFiber3StateAt 2 ∈ chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5] [tmFiber3StateAt 0] := by
    rw [show [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5] = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2] ++ [tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5]
      (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2] [tmFiber3StateAt 0]) (tmFiber3StateAt 2)
      tmFiber3State2_in_pass1_prefix
  rw [show [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6] = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5] ++ [tmFiber3StateAt 6] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber3StateAt 6) []
    (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5] [tmFiber3StateAt 0]) (tmFiber3StateAt 2)
    hparentBefore tmFiber3ReverseSingleStep6

theorem tmFiber3State7_in_pass1_prefix :
    tmFiber3StateAt 7 ∈ chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7] [tmFiber3StateAt 0] := by
  have hparentBefore :
      tmFiber3StateAt 3 ∈ chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6] [tmFiber3StateAt 0] := by
    rw [show [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6] = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3] ++ [tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6]
      (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3] [tmFiber3StateAt 0]) (tmFiber3StateAt 3)
      tmFiber3State3_in_pass1_prefix
  rw [show [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7] = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6] ++ [tmFiber3StateAt 7] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber3StateAt 7) []
    (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6] [tmFiber3StateAt 0]) (tmFiber3StateAt 3)
    hparentBefore tmFiber3ReverseSingleStep7

theorem tmFiber3State8_in_pass1_prefix :
    tmFiber3StateAt 8 ∈ chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8] [tmFiber3StateAt 0] := by
  have hparentBefore :
      tmFiber3StateAt 0 ∈ chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7] [tmFiber3StateAt 0] := by
    rw [show [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7] = [tmFiber3StateAt 0] ++ [tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7]
      (chainClosureStep tmWord [tmFiber3StateAt 0] [tmFiber3StateAt 0]) (tmFiber3StateAt 0)
      tmFiber3State0_in_pass1_prefix
  rw [show [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8] = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7] ++ [tmFiber3StateAt 8] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber3StateAt 8) []
    (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7] [tmFiber3StateAt 0]) (tmFiber3StateAt 0)
    hparentBefore tmFiber3ReverseSingleStep8

theorem tmFiber3State9_in_pass1_prefix :
    tmFiber3StateAt 9 ∈ chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9] [tmFiber3StateAt 0] := by
  have hparentBefore :
      tmFiber3StateAt 1 ∈ chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8] [tmFiber3StateAt 0] := by
    rw [show [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8] = [tmFiber3StateAt 0, tmFiber3StateAt 1] ++ [tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8]
      (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1] [tmFiber3StateAt 0]) (tmFiber3StateAt 1)
      tmFiber3State1_in_pass1_prefix
  rw [show [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9] = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8] ++ [tmFiber3StateAt 9] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber3StateAt 9) []
    (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8] [tmFiber3StateAt 0]) (tmFiber3StateAt 1)
    hparentBefore tmFiber3ReverseSingleStep9

theorem tmFiber3State10_in_pass1_prefix :
    tmFiber3StateAt 10 ∈ chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10] [tmFiber3StateAt 0] := by
  have hparentBefore :
      tmFiber3StateAt 2 ∈ chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9] [tmFiber3StateAt 0] := by
    rw [show [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9] = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2] ++ [tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9]
      (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2] [tmFiber3StateAt 0]) (tmFiber3StateAt 2)
      tmFiber3State2_in_pass1_prefix
  rw [show [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10] = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9] ++ [tmFiber3StateAt 10] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber3StateAt 10) []
    (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9] [tmFiber3StateAt 0]) (tmFiber3StateAt 2)
    hparentBefore tmFiber3ReverseSingleStep10

theorem tmFiber3State11_in_pass1_prefix :
    tmFiber3StateAt 11 ∈ chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11] [tmFiber3StateAt 0] := by
  have hparentBefore :
      tmFiber3StateAt 3 ∈ chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10] [tmFiber3StateAt 0] := by
    rw [show [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10] = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3] ++ [tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10]
      (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3] [tmFiber3StateAt 0]) (tmFiber3StateAt 3)
      tmFiber3State3_in_pass1_prefix
  rw [show [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11] = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10] ++ [tmFiber3StateAt 11] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber3StateAt 11) []
    (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10] [tmFiber3StateAt 0]) (tmFiber3StateAt 3)
    hparentBefore tmFiber3ReverseSingleStep11

theorem tmFiber3State12_in_pass1_prefix :
    tmFiber3StateAt 12 ∈ chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12] [tmFiber3StateAt 0] := by
  have hparentBefore :
      tmFiber3StateAt 4 ∈ chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11] [tmFiber3StateAt 0] := by
    rw [show [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11] = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4] ++ [tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11]
      (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4] [tmFiber3StateAt 0]) (tmFiber3StateAt 4)
      tmFiber3State4_in_pass1_prefix
  rw [show [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12] = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11] ++ [tmFiber3StateAt 12] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber3StateAt 12) []
    (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11] [tmFiber3StateAt 0]) (tmFiber3StateAt 4)
    hparentBefore tmFiber3ReverseSingleStep12

theorem tmFiber3State13_in_pass1_prefix :
    tmFiber3StateAt 13 ∈ chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13] [tmFiber3StateAt 0] := by
  have hparentBefore :
      tmFiber3StateAt 5 ∈ chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12] [tmFiber3StateAt 0] := by
    rw [show [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12] = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5] ++ [tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12]
      (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5] [tmFiber3StateAt 0]) (tmFiber3StateAt 5)
      tmFiber3State5_in_pass1_prefix
  rw [show [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13] = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12] ++ [tmFiber3StateAt 13] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber3StateAt 13) []
    (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12] [tmFiber3StateAt 0]) (tmFiber3StateAt 5)
    hparentBefore tmFiber3ReverseSingleStep13

theorem tmFiber3State14_in_pass1_prefix :
    tmFiber3StateAt 14 ∈ chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14] [tmFiber3StateAt 0] := by
  have hparentBefore :
      tmFiber3StateAt 6 ∈ chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13] [tmFiber3StateAt 0] := by
    rw [show [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13] = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6] ++ [tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13]
      (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6] [tmFiber3StateAt 0]) (tmFiber3StateAt 6)
      tmFiber3State6_in_pass1_prefix
  rw [show [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14] = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13] ++ [tmFiber3StateAt 14] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber3StateAt 14) []
    (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13] [tmFiber3StateAt 0]) (tmFiber3StateAt 6)
    hparentBefore tmFiber3ReverseSingleStep14

theorem tmFiber3State15_in_pass1_prefix :
    tmFiber3StateAt 15 ∈ chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14, tmFiber3StateAt 15] [tmFiber3StateAt 0] := by
  have hparentBefore :
      tmFiber3StateAt 7 ∈ chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14] [tmFiber3StateAt 0] := by
    rw [show [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14] = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7] ++ [tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14]
      (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7] [tmFiber3StateAt 0]) (tmFiber3StateAt 7)
      tmFiber3State7_in_pass1_prefix
  rw [show [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14, tmFiber3StateAt 15] = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14] ++ [tmFiber3StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber3StateAt 15) []
    (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14] [tmFiber3StateAt 0]) (tmFiber3StateAt 7)
    hparentBefore tmFiber3ReverseSingleStep15

theorem tmFiber3State0_in_pass1_full :
    tmFiber3StateAt 0 ∈ chainClosureStep tmWord tmFiber3DirectStates [tmFiber3StateAt 0] := by
  rw [show tmFiber3DirectStates = [tmFiber3StateAt 0] ++ [tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14, tmFiber3StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14, tmFiber3StateAt 15]
    (chainClosureStep tmWord [tmFiber3StateAt 0] [tmFiber3StateAt 0]) (tmFiber3StateAt 0)
    tmFiber3State0_in_pass1_prefix

theorem tmFiber3State1_in_pass1_full :
    tmFiber3StateAt 1 ∈ chainClosureStep tmWord tmFiber3DirectStates [tmFiber3StateAt 0] := by
  rw [show tmFiber3DirectStates = [tmFiber3StateAt 0, tmFiber3StateAt 1] ++ [tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14, tmFiber3StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14, tmFiber3StateAt 15]
    (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1] [tmFiber3StateAt 0]) (tmFiber3StateAt 1)
    tmFiber3State1_in_pass1_prefix

theorem tmFiber3State2_in_pass1_full :
    tmFiber3StateAt 2 ∈ chainClosureStep tmWord tmFiber3DirectStates [tmFiber3StateAt 0] := by
  rw [show tmFiber3DirectStates = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2] ++ [tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14, tmFiber3StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14, tmFiber3StateAt 15]
    (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2] [tmFiber3StateAt 0]) (tmFiber3StateAt 2)
    tmFiber3State2_in_pass1_prefix

theorem tmFiber3State3_in_pass1_full :
    tmFiber3StateAt 3 ∈ chainClosureStep tmWord tmFiber3DirectStates [tmFiber3StateAt 0] := by
  rw [show tmFiber3DirectStates = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3] ++ [tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14, tmFiber3StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14, tmFiber3StateAt 15]
    (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3] [tmFiber3StateAt 0]) (tmFiber3StateAt 3)
    tmFiber3State3_in_pass1_prefix

theorem tmFiber3State4_in_pass1_full :
    tmFiber3StateAt 4 ∈ chainClosureStep tmWord tmFiber3DirectStates [tmFiber3StateAt 0] := by
  rw [show tmFiber3DirectStates = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4] ++ [tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14, tmFiber3StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14, tmFiber3StateAt 15]
    (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4] [tmFiber3StateAt 0]) (tmFiber3StateAt 4)
    tmFiber3State4_in_pass1_prefix

theorem tmFiber3State5_in_pass1_full :
    tmFiber3StateAt 5 ∈ chainClosureStep tmWord tmFiber3DirectStates [tmFiber3StateAt 0] := by
  rw [show tmFiber3DirectStates = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5] ++ [tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14, tmFiber3StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14, tmFiber3StateAt 15]
    (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5] [tmFiber3StateAt 0]) (tmFiber3StateAt 5)
    tmFiber3State5_in_pass1_prefix

theorem tmFiber3State6_in_pass1_full :
    tmFiber3StateAt 6 ∈ chainClosureStep tmWord tmFiber3DirectStates [tmFiber3StateAt 0] := by
  rw [show tmFiber3DirectStates = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6] ++ [tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14, tmFiber3StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14, tmFiber3StateAt 15]
    (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6] [tmFiber3StateAt 0]) (tmFiber3StateAt 6)
    tmFiber3State6_in_pass1_prefix

theorem tmFiber3State7_in_pass1_full :
    tmFiber3StateAt 7 ∈ chainClosureStep tmWord tmFiber3DirectStates [tmFiber3StateAt 0] := by
  rw [show tmFiber3DirectStates = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7] ++ [tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14, tmFiber3StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14, tmFiber3StateAt 15]
    (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7] [tmFiber3StateAt 0]) (tmFiber3StateAt 7)
    tmFiber3State7_in_pass1_prefix

theorem tmFiber3State8_in_pass1_full :
    tmFiber3StateAt 8 ∈ chainClosureStep tmWord tmFiber3DirectStates [tmFiber3StateAt 0] := by
  rw [show tmFiber3DirectStates = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8] ++ [tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14, tmFiber3StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14, tmFiber3StateAt 15]
    (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8] [tmFiber3StateAt 0]) (tmFiber3StateAt 8)
    tmFiber3State8_in_pass1_prefix

theorem tmFiber3State9_in_pass1_full :
    tmFiber3StateAt 9 ∈ chainClosureStep tmWord tmFiber3DirectStates [tmFiber3StateAt 0] := by
  rw [show tmFiber3DirectStates = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9] ++ [tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14, tmFiber3StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14, tmFiber3StateAt 15]
    (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9] [tmFiber3StateAt 0]) (tmFiber3StateAt 9)
    tmFiber3State9_in_pass1_prefix

theorem tmFiber3State10_in_pass1_full :
    tmFiber3StateAt 10 ∈ chainClosureStep tmWord tmFiber3DirectStates [tmFiber3StateAt 0] := by
  rw [show tmFiber3DirectStates = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10] ++ [tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14, tmFiber3StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14, tmFiber3StateAt 15]
    (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10] [tmFiber3StateAt 0]) (tmFiber3StateAt 10)
    tmFiber3State10_in_pass1_prefix

theorem tmFiber3State11_in_pass1_full :
    tmFiber3StateAt 11 ∈ chainClosureStep tmWord tmFiber3DirectStates [tmFiber3StateAt 0] := by
  rw [show tmFiber3DirectStates = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11] ++ [tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14, tmFiber3StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14, tmFiber3StateAt 15]
    (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11] [tmFiber3StateAt 0]) (tmFiber3StateAt 11)
    tmFiber3State11_in_pass1_prefix

theorem tmFiber3State12_in_pass1_full :
    tmFiber3StateAt 12 ∈ chainClosureStep tmWord tmFiber3DirectStates [tmFiber3StateAt 0] := by
  rw [show tmFiber3DirectStates = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12] ++ [tmFiber3StateAt 13, tmFiber3StateAt 14, tmFiber3StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber3StateAt 13, tmFiber3StateAt 14, tmFiber3StateAt 15]
    (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12] [tmFiber3StateAt 0]) (tmFiber3StateAt 12)
    tmFiber3State12_in_pass1_prefix

theorem tmFiber3State13_in_pass1_full :
    tmFiber3StateAt 13 ∈ chainClosureStep tmWord tmFiber3DirectStates [tmFiber3StateAt 0] := by
  rw [show tmFiber3DirectStates = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13] ++ [tmFiber3StateAt 14, tmFiber3StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber3StateAt 14, tmFiber3StateAt 15]
    (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13] [tmFiber3StateAt 0]) (tmFiber3StateAt 13)
    tmFiber3State13_in_pass1_prefix

theorem tmFiber3State14_in_pass1_full :
    tmFiber3StateAt 14 ∈ chainClosureStep tmWord tmFiber3DirectStates [tmFiber3StateAt 0] := by
  rw [show tmFiber3DirectStates = [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14] ++ [tmFiber3StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber3StateAt 15]
    (chainClosureStep tmWord [tmFiber3StateAt 0, tmFiber3StateAt 1, tmFiber3StateAt 2, tmFiber3StateAt 3, tmFiber3StateAt 4, tmFiber3StateAt 5, tmFiber3StateAt 6, tmFiber3StateAt 7, tmFiber3StateAt 8, tmFiber3StateAt 9, tmFiber3StateAt 10, tmFiber3StateAt 11, tmFiber3StateAt 12, tmFiber3StateAt 13, tmFiber3StateAt 14] [tmFiber3StateAt 0]) (tmFiber3StateAt 14)
    tmFiber3State14_in_pass1_prefix

theorem tmFiber3State15_in_pass1_full :
    tmFiber3StateAt 15 ∈ chainClosureStep tmWord tmFiber3DirectStates [tmFiber3StateAt 0] := by
  simpa [tmFiber3DirectStates] using tmFiber3State15_in_pass1_prefix

theorem tmFiber3State0_in_close :
    tmFiber3StateAt 0 ∈ closeChainFiber tmWord tmFiber3DirectStates tmFiber3DirectStates.length [tmFiber3StateAt 0] := by
  change tmFiber3StateAt 0 ∈ closeChainFiber tmWord tmFiber3DirectStates (15 + 1) [tmFiber3StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber3DirectStates 15 [tmFiber3StateAt 0] (tmFiber3StateAt 0) tmFiber3State0_in_pass1_full

theorem tmFiber3State1_in_close :
    tmFiber3StateAt 1 ∈ closeChainFiber tmWord tmFiber3DirectStates tmFiber3DirectStates.length [tmFiber3StateAt 0] := by
  change tmFiber3StateAt 1 ∈ closeChainFiber tmWord tmFiber3DirectStates (15 + 1) [tmFiber3StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber3DirectStates 15 [tmFiber3StateAt 0] (tmFiber3StateAt 1) tmFiber3State1_in_pass1_full

theorem tmFiber3State2_in_close :
    tmFiber3StateAt 2 ∈ closeChainFiber tmWord tmFiber3DirectStates tmFiber3DirectStates.length [tmFiber3StateAt 0] := by
  change tmFiber3StateAt 2 ∈ closeChainFiber tmWord tmFiber3DirectStates (15 + 1) [tmFiber3StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber3DirectStates 15 [tmFiber3StateAt 0] (tmFiber3StateAt 2) tmFiber3State2_in_pass1_full

theorem tmFiber3State3_in_close :
    tmFiber3StateAt 3 ∈ closeChainFiber tmWord tmFiber3DirectStates tmFiber3DirectStates.length [tmFiber3StateAt 0] := by
  change tmFiber3StateAt 3 ∈ closeChainFiber tmWord tmFiber3DirectStates (15 + 1) [tmFiber3StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber3DirectStates 15 [tmFiber3StateAt 0] (tmFiber3StateAt 3) tmFiber3State3_in_pass1_full

theorem tmFiber3State4_in_close :
    tmFiber3StateAt 4 ∈ closeChainFiber tmWord tmFiber3DirectStates tmFiber3DirectStates.length [tmFiber3StateAt 0] := by
  change tmFiber3StateAt 4 ∈ closeChainFiber tmWord tmFiber3DirectStates (15 + 1) [tmFiber3StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber3DirectStates 15 [tmFiber3StateAt 0] (tmFiber3StateAt 4) tmFiber3State4_in_pass1_full

theorem tmFiber3State5_in_close :
    tmFiber3StateAt 5 ∈ closeChainFiber tmWord tmFiber3DirectStates tmFiber3DirectStates.length [tmFiber3StateAt 0] := by
  change tmFiber3StateAt 5 ∈ closeChainFiber tmWord tmFiber3DirectStates (15 + 1) [tmFiber3StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber3DirectStates 15 [tmFiber3StateAt 0] (tmFiber3StateAt 5) tmFiber3State5_in_pass1_full

theorem tmFiber3State6_in_close :
    tmFiber3StateAt 6 ∈ closeChainFiber tmWord tmFiber3DirectStates tmFiber3DirectStates.length [tmFiber3StateAt 0] := by
  change tmFiber3StateAt 6 ∈ closeChainFiber tmWord tmFiber3DirectStates (15 + 1) [tmFiber3StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber3DirectStates 15 [tmFiber3StateAt 0] (tmFiber3StateAt 6) tmFiber3State6_in_pass1_full

theorem tmFiber3State7_in_close :
    tmFiber3StateAt 7 ∈ closeChainFiber tmWord tmFiber3DirectStates tmFiber3DirectStates.length [tmFiber3StateAt 0] := by
  change tmFiber3StateAt 7 ∈ closeChainFiber tmWord tmFiber3DirectStates (15 + 1) [tmFiber3StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber3DirectStates 15 [tmFiber3StateAt 0] (tmFiber3StateAt 7) tmFiber3State7_in_pass1_full

theorem tmFiber3State8_in_close :
    tmFiber3StateAt 8 ∈ closeChainFiber tmWord tmFiber3DirectStates tmFiber3DirectStates.length [tmFiber3StateAt 0] := by
  change tmFiber3StateAt 8 ∈ closeChainFiber tmWord tmFiber3DirectStates (15 + 1) [tmFiber3StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber3DirectStates 15 [tmFiber3StateAt 0] (tmFiber3StateAt 8) tmFiber3State8_in_pass1_full

theorem tmFiber3State9_in_close :
    tmFiber3StateAt 9 ∈ closeChainFiber tmWord tmFiber3DirectStates tmFiber3DirectStates.length [tmFiber3StateAt 0] := by
  change tmFiber3StateAt 9 ∈ closeChainFiber tmWord tmFiber3DirectStates (15 + 1) [tmFiber3StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber3DirectStates 15 [tmFiber3StateAt 0] (tmFiber3StateAt 9) tmFiber3State9_in_pass1_full

theorem tmFiber3State10_in_close :
    tmFiber3StateAt 10 ∈ closeChainFiber tmWord tmFiber3DirectStates tmFiber3DirectStates.length [tmFiber3StateAt 0] := by
  change tmFiber3StateAt 10 ∈ closeChainFiber tmWord tmFiber3DirectStates (15 + 1) [tmFiber3StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber3DirectStates 15 [tmFiber3StateAt 0] (tmFiber3StateAt 10) tmFiber3State10_in_pass1_full

theorem tmFiber3State11_in_close :
    tmFiber3StateAt 11 ∈ closeChainFiber tmWord tmFiber3DirectStates tmFiber3DirectStates.length [tmFiber3StateAt 0] := by
  change tmFiber3StateAt 11 ∈ closeChainFiber tmWord tmFiber3DirectStates (15 + 1) [tmFiber3StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber3DirectStates 15 [tmFiber3StateAt 0] (tmFiber3StateAt 11) tmFiber3State11_in_pass1_full

theorem tmFiber3State12_in_close :
    tmFiber3StateAt 12 ∈ closeChainFiber tmWord tmFiber3DirectStates tmFiber3DirectStates.length [tmFiber3StateAt 0] := by
  change tmFiber3StateAt 12 ∈ closeChainFiber tmWord tmFiber3DirectStates (15 + 1) [tmFiber3StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber3DirectStates 15 [tmFiber3StateAt 0] (tmFiber3StateAt 12) tmFiber3State12_in_pass1_full

theorem tmFiber3State13_in_close :
    tmFiber3StateAt 13 ∈ closeChainFiber tmWord tmFiber3DirectStates tmFiber3DirectStates.length [tmFiber3StateAt 0] := by
  change tmFiber3StateAt 13 ∈ closeChainFiber tmWord tmFiber3DirectStates (15 + 1) [tmFiber3StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber3DirectStates 15 [tmFiber3StateAt 0] (tmFiber3StateAt 13) tmFiber3State13_in_pass1_full

theorem tmFiber3State14_in_close :
    tmFiber3StateAt 14 ∈ closeChainFiber tmWord tmFiber3DirectStates tmFiber3DirectStates.length [tmFiber3StateAt 0] := by
  change tmFiber3StateAt 14 ∈ closeChainFiber tmWord tmFiber3DirectStates (15 + 1) [tmFiber3StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber3DirectStates 15 [tmFiber3StateAt 0] (tmFiber3StateAt 14) tmFiber3State14_in_pass1_full

theorem tmFiber3State15_in_close :
    tmFiber3StateAt 15 ∈ closeChainFiber tmWord tmFiber3DirectStates tmFiber3DirectStates.length [tmFiber3StateAt 0] := by
  change tmFiber3StateAt 15 ∈ closeChainFiber tmWord tmFiber3DirectStates (15 + 1) [tmFiber3StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber3DirectStates 15 [tmFiber3StateAt 0] (tmFiber3StateAt 15) tmFiber3State15_in_pass1_full

theorem tmFiber3DirectConnected :
    chainFiberConnected tmWord tmFiber3DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber3DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber3State0_in_close
  · subst state
    exact tmFiber3State1_in_close
  · subst state
    exact tmFiber3State2_in_close
  · subst state
    exact tmFiber3State3_in_close
  · subst state
    exact tmFiber3State4_in_close
  · subst state
    exact tmFiber3State5_in_close
  · subst state
    exact tmFiber3State6_in_close
  · subst state
    exact tmFiber3State7_in_close
  · subst state
    exact tmFiber3State8_in_close
  · subst state
    exact tmFiber3State9_in_close
  · subst state
    exact tmFiber3State10_in_close
  · subst state
    exact tmFiber3State11_in_close
  · subst state
    exact tmFiber3State12_in_close
  · subst state
    exact tmFiber3State13_in_close
  · subst state
    exact tmFiber3State14_in_close
  · subst state
    exact tmFiber3State15_in_close
  · cases h

def tmFiber5StateAt (i : Nat) : List TauState :=
  directStates (tmFiber5RowAt i).sourceLeft (tmFiber5RowAt i).sourceRight

def tmFiber5DirectStates : List (List TauState) :=
  [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14, tmFiber5StateAt 15]

theorem tmFiber5ReverseRow_1_ok :
    tmRowReverseValid tmFiber5Key tmFiber5Expected (tmFiber5RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber5Chunk0_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber5Chunk0] at h
  exact h.2

theorem tmFiber5ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber5StateAt 0) (tmFiber5StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber5StateAt 0) (tmFiber5StateAt 1)
    (tmFiber5RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber5Key tmFiber5Expected
        (tmFiber5RowAt 1) (by decide) tmFiber5ReverseRow_1_ok
      simpa [tmFiber5StateAt, tmFiber5RowAt, tmFiber5Rows, listGetD, directRow] using h)

theorem tmFiber5ReverseRow_2_ok :
    tmRowReverseValid tmFiber5Key tmFiber5Expected (tmFiber5RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber5Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber5Chunk1] at h
  exact h.1

theorem tmFiber5ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber5StateAt 1) (tmFiber5StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber5StateAt 1) (tmFiber5StateAt 2)
    (tmFiber5RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber5Key tmFiber5Expected
        (tmFiber5RowAt 2) (by decide) tmFiber5ReverseRow_2_ok
      simpa [tmFiber5StateAt, tmFiber5RowAt, tmFiber5Rows, listGetD, directRow] using h)

theorem tmFiber5ReverseRow_3_ok :
    tmRowReverseValid tmFiber5Key tmFiber5Expected (tmFiber5RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber5Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber5Chunk1] at h
  exact h.2

theorem tmFiber5ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber5StateAt 0) (tmFiber5StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber5StateAt 0) (tmFiber5StateAt 3)
    (tmFiber5RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber5Key tmFiber5Expected
        (tmFiber5RowAt 3) (by decide) tmFiber5ReverseRow_3_ok
      simpa [tmFiber5StateAt, tmFiber5RowAt, tmFiber5Rows, listGetD, directRow] using h)

theorem tmFiber5ReverseRow_4_ok :
    tmRowReverseValid tmFiber5Key tmFiber5Expected (tmFiber5RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber5Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber5Chunk2] at h
  exact h.1

theorem tmFiber5ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber5StateAt 0) (tmFiber5StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber5StateAt 0) (tmFiber5StateAt 4)
    (tmFiber5RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber5Key tmFiber5Expected
        (tmFiber5RowAt 4) (by decide) tmFiber5ReverseRow_4_ok
      simpa [tmFiber5StateAt, tmFiber5RowAt, tmFiber5Rows, listGetD, directRow] using h)

theorem tmFiber5ReverseRow_5_ok :
    tmRowReverseValid tmFiber5Key tmFiber5Expected (tmFiber5RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber5Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber5Chunk2] at h
  exact h.2

theorem tmFiber5ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber5StateAt 1) (tmFiber5StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber5StateAt 1) (tmFiber5StateAt 5)
    (tmFiber5RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber5Key tmFiber5Expected
        (tmFiber5RowAt 5) (by decide) tmFiber5ReverseRow_5_ok
      simpa [tmFiber5StateAt, tmFiber5RowAt, tmFiber5Rows, listGetD, directRow] using h)

theorem tmFiber5ReverseRow_6_ok :
    tmRowReverseValid tmFiber5Key tmFiber5Expected (tmFiber5RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber5Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber5Chunk3] at h
  exact h.1

theorem tmFiber5ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber5StateAt 2) (tmFiber5StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber5StateAt 2) (tmFiber5StateAt 6)
    (tmFiber5RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber5Key tmFiber5Expected
        (tmFiber5RowAt 6) (by decide) tmFiber5ReverseRow_6_ok
      simpa [tmFiber5StateAt, tmFiber5RowAt, tmFiber5Rows, listGetD, directRow] using h)

theorem tmFiber5ReverseRow_7_ok :
    tmRowReverseValid tmFiber5Key tmFiber5Expected (tmFiber5RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber5Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber5Chunk3] at h
  exact h.2

theorem tmFiber5ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber5StateAt 3) (tmFiber5StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber5StateAt 3) (tmFiber5StateAt 7)
    (tmFiber5RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber5Key tmFiber5Expected
        (tmFiber5RowAt 7) (by decide) tmFiber5ReverseRow_7_ok
      simpa [tmFiber5StateAt, tmFiber5RowAt, tmFiber5Rows, listGetD, directRow] using h)

theorem tmFiber5ReverseRow_8_ok :
    tmRowReverseValid tmFiber5Key tmFiber5Expected (tmFiber5RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber5Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber5Chunk4] at h
  exact h.1

theorem tmFiber5ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber5StateAt 0) (tmFiber5StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber5StateAt 0) (tmFiber5StateAt 8)
    (tmFiber5RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber5Key tmFiber5Expected
        (tmFiber5RowAt 8) (by decide) tmFiber5ReverseRow_8_ok
      simpa [tmFiber5StateAt, tmFiber5RowAt, tmFiber5Rows, listGetD, directRow] using h)

theorem tmFiber5ReverseRow_9_ok :
    tmRowReverseValid tmFiber5Key tmFiber5Expected (tmFiber5RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber5Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber5Chunk4] at h
  exact h.2

theorem tmFiber5ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber5StateAt 1) (tmFiber5StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber5StateAt 1) (tmFiber5StateAt 9)
    (tmFiber5RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber5Key tmFiber5Expected
        (tmFiber5RowAt 9) (by decide) tmFiber5ReverseRow_9_ok
      simpa [tmFiber5StateAt, tmFiber5RowAt, tmFiber5Rows, listGetD, directRow] using h)

theorem tmFiber5ReverseRow_10_ok :
    tmRowReverseValid tmFiber5Key tmFiber5Expected (tmFiber5RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber5Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber5Chunk5] at h
  exact h.1

theorem tmFiber5ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber5StateAt 2) (tmFiber5StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber5StateAt 2) (tmFiber5StateAt 10)
    (tmFiber5RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber5Key tmFiber5Expected
        (tmFiber5RowAt 10) (by decide) tmFiber5ReverseRow_10_ok
      simpa [tmFiber5StateAt, tmFiber5RowAt, tmFiber5Rows, listGetD, directRow] using h)

theorem tmFiber5ReverseRow_11_ok :
    tmRowReverseValid tmFiber5Key tmFiber5Expected (tmFiber5RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber5Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber5Chunk5] at h
  exact h.2

theorem tmFiber5ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber5StateAt 3) (tmFiber5StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber5StateAt 3) (tmFiber5StateAt 11)
    (tmFiber5RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber5Key tmFiber5Expected
        (tmFiber5RowAt 11) (by decide) tmFiber5ReverseRow_11_ok
      simpa [tmFiber5StateAt, tmFiber5RowAt, tmFiber5Rows, listGetD, directRow] using h)

theorem tmFiber5ReverseRow_12_ok :
    tmRowReverseValid tmFiber5Key tmFiber5Expected (tmFiber5RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber5Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber5Chunk6] at h
  exact h.1

theorem tmFiber5ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber5StateAt 4) (tmFiber5StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber5StateAt 4) (tmFiber5StateAt 12)
    (tmFiber5RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber5Key tmFiber5Expected
        (tmFiber5RowAt 12) (by decide) tmFiber5ReverseRow_12_ok
      simpa [tmFiber5StateAt, tmFiber5RowAt, tmFiber5Rows, listGetD, directRow] using h)

theorem tmFiber5ReverseRow_13_ok :
    tmRowReverseValid tmFiber5Key tmFiber5Expected (tmFiber5RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber5Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber5Chunk6] at h
  exact h.2

theorem tmFiber5ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber5StateAt 5) (tmFiber5StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber5StateAt 5) (tmFiber5StateAt 13)
    (tmFiber5RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber5Key tmFiber5Expected
        (tmFiber5RowAt 13) (by decide) tmFiber5ReverseRow_13_ok
      simpa [tmFiber5StateAt, tmFiber5RowAt, tmFiber5Rows, listGetD, directRow] using h)

theorem tmFiber5ReverseRow_14_ok :
    tmRowReverseValid tmFiber5Key tmFiber5Expected (tmFiber5RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber5Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber5Chunk7] at h
  exact h.1

theorem tmFiber5ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber5StateAt 6) (tmFiber5StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber5StateAt 6) (tmFiber5StateAt 14)
    (tmFiber5RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber5Key tmFiber5Expected
        (tmFiber5RowAt 14) (by decide) tmFiber5ReverseRow_14_ok
      simpa [tmFiber5StateAt, tmFiber5RowAt, tmFiber5Rows, listGetD, directRow] using h)

theorem tmFiber5ReverseRow_15_ok :
    tmRowReverseValid tmFiber5Key tmFiber5Expected (tmFiber5RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber5Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber5Chunk7] at h
  exact h.2

theorem tmFiber5ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber5StateAt 7) (tmFiber5StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber5StateAt 7) (tmFiber5StateAt 15)
    (tmFiber5RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber5Key tmFiber5Expected
        (tmFiber5RowAt 15) (by decide) tmFiber5ReverseRow_15_ok
      simpa [tmFiber5StateAt, tmFiber5RowAt, tmFiber5Rows, listGetD, directRow] using h)

theorem tmFiber5State0_in_pass1_prefix :
    tmFiber5StateAt 0 ∈ chainClosureStep tmWord [tmFiber5StateAt 0] [tmFiber5StateAt 0] := by
  exact chainClosureStep_mem_of_seen tmWord [tmFiber5StateAt 0] [tmFiber5StateAt 0] (tmFiber5StateAt 0) (by simp)

theorem tmFiber5State1_in_pass1_prefix :
    tmFiber5StateAt 1 ∈ chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1] [tmFiber5StateAt 0] := by
  have hparentBefore :
      tmFiber5StateAt 0 ∈ chainClosureStep tmWord [tmFiber5StateAt 0] [tmFiber5StateAt 0] := by
    exact tmFiber5State0_in_pass1_prefix
  rw [show [tmFiber5StateAt 0, tmFiber5StateAt 1] = [tmFiber5StateAt 0] ++ [tmFiber5StateAt 1] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber5StateAt 1) []
    (chainClosureStep tmWord [tmFiber5StateAt 0] [tmFiber5StateAt 0]) (tmFiber5StateAt 0)
    hparentBefore tmFiber5ReverseSingleStep1

theorem tmFiber5State2_in_pass1_prefix :
    tmFiber5StateAt 2 ∈ chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2] [tmFiber5StateAt 0] := by
  have hparentBefore :
      tmFiber5StateAt 1 ∈ chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1] [tmFiber5StateAt 0] := by
    exact tmFiber5State1_in_pass1_prefix
  rw [show [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2] = [tmFiber5StateAt 0, tmFiber5StateAt 1] ++ [tmFiber5StateAt 2] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber5StateAt 2) []
    (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1] [tmFiber5StateAt 0]) (tmFiber5StateAt 1)
    hparentBefore tmFiber5ReverseSingleStep2

theorem tmFiber5State3_in_pass1_prefix :
    tmFiber5StateAt 3 ∈ chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3] [tmFiber5StateAt 0] := by
  have hparentBefore :
      tmFiber5StateAt 0 ∈ chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2] [tmFiber5StateAt 0] := by
    rw [show [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2] = [tmFiber5StateAt 0] ++ [tmFiber5StateAt 1, tmFiber5StateAt 2] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber5StateAt 1, tmFiber5StateAt 2]
      (chainClosureStep tmWord [tmFiber5StateAt 0] [tmFiber5StateAt 0]) (tmFiber5StateAt 0)
      tmFiber5State0_in_pass1_prefix
  rw [show [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3] = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2] ++ [tmFiber5StateAt 3] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber5StateAt 3) []
    (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2] [tmFiber5StateAt 0]) (tmFiber5StateAt 0)
    hparentBefore tmFiber5ReverseSingleStep3

theorem tmFiber5State4_in_pass1_prefix :
    tmFiber5StateAt 4 ∈ chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4] [tmFiber5StateAt 0] := by
  have hparentBefore :
      tmFiber5StateAt 0 ∈ chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3] [tmFiber5StateAt 0] := by
    rw [show [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3] = [tmFiber5StateAt 0] ++ [tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3]
      (chainClosureStep tmWord [tmFiber5StateAt 0] [tmFiber5StateAt 0]) (tmFiber5StateAt 0)
      tmFiber5State0_in_pass1_prefix
  rw [show [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4] = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3] ++ [tmFiber5StateAt 4] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber5StateAt 4) []
    (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3] [tmFiber5StateAt 0]) (tmFiber5StateAt 0)
    hparentBefore tmFiber5ReverseSingleStep4

theorem tmFiber5State5_in_pass1_prefix :
    tmFiber5StateAt 5 ∈ chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5] [tmFiber5StateAt 0] := by
  have hparentBefore :
      tmFiber5StateAt 1 ∈ chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4] [tmFiber5StateAt 0] := by
    rw [show [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4] = [tmFiber5StateAt 0, tmFiber5StateAt 1] ++ [tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4]
      (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1] [tmFiber5StateAt 0]) (tmFiber5StateAt 1)
      tmFiber5State1_in_pass1_prefix
  rw [show [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5] = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4] ++ [tmFiber5StateAt 5] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber5StateAt 5) []
    (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4] [tmFiber5StateAt 0]) (tmFiber5StateAt 1)
    hparentBefore tmFiber5ReverseSingleStep5

theorem tmFiber5State6_in_pass1_prefix :
    tmFiber5StateAt 6 ∈ chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6] [tmFiber5StateAt 0] := by
  have hparentBefore :
      tmFiber5StateAt 2 ∈ chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5] [tmFiber5StateAt 0] := by
    rw [show [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5] = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2] ++ [tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5]
      (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2] [tmFiber5StateAt 0]) (tmFiber5StateAt 2)
      tmFiber5State2_in_pass1_prefix
  rw [show [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6] = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5] ++ [tmFiber5StateAt 6] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber5StateAt 6) []
    (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5] [tmFiber5StateAt 0]) (tmFiber5StateAt 2)
    hparentBefore tmFiber5ReverseSingleStep6

theorem tmFiber5State7_in_pass1_prefix :
    tmFiber5StateAt 7 ∈ chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7] [tmFiber5StateAt 0] := by
  have hparentBefore :
      tmFiber5StateAt 3 ∈ chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6] [tmFiber5StateAt 0] := by
    rw [show [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6] = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3] ++ [tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6]
      (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3] [tmFiber5StateAt 0]) (tmFiber5StateAt 3)
      tmFiber5State3_in_pass1_prefix
  rw [show [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7] = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6] ++ [tmFiber5StateAt 7] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber5StateAt 7) []
    (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6] [tmFiber5StateAt 0]) (tmFiber5StateAt 3)
    hparentBefore tmFiber5ReverseSingleStep7

theorem tmFiber5State8_in_pass1_prefix :
    tmFiber5StateAt 8 ∈ chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8] [tmFiber5StateAt 0] := by
  have hparentBefore :
      tmFiber5StateAt 0 ∈ chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7] [tmFiber5StateAt 0] := by
    rw [show [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7] = [tmFiber5StateAt 0] ++ [tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7]
      (chainClosureStep tmWord [tmFiber5StateAt 0] [tmFiber5StateAt 0]) (tmFiber5StateAt 0)
      tmFiber5State0_in_pass1_prefix
  rw [show [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8] = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7] ++ [tmFiber5StateAt 8] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber5StateAt 8) []
    (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7] [tmFiber5StateAt 0]) (tmFiber5StateAt 0)
    hparentBefore tmFiber5ReverseSingleStep8

theorem tmFiber5State9_in_pass1_prefix :
    tmFiber5StateAt 9 ∈ chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9] [tmFiber5StateAt 0] := by
  have hparentBefore :
      tmFiber5StateAt 1 ∈ chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8] [tmFiber5StateAt 0] := by
    rw [show [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8] = [tmFiber5StateAt 0, tmFiber5StateAt 1] ++ [tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8]
      (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1] [tmFiber5StateAt 0]) (tmFiber5StateAt 1)
      tmFiber5State1_in_pass1_prefix
  rw [show [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9] = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8] ++ [tmFiber5StateAt 9] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber5StateAt 9) []
    (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8] [tmFiber5StateAt 0]) (tmFiber5StateAt 1)
    hparentBefore tmFiber5ReverseSingleStep9

theorem tmFiber5State10_in_pass1_prefix :
    tmFiber5StateAt 10 ∈ chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10] [tmFiber5StateAt 0] := by
  have hparentBefore :
      tmFiber5StateAt 2 ∈ chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9] [tmFiber5StateAt 0] := by
    rw [show [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9] = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2] ++ [tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9]
      (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2] [tmFiber5StateAt 0]) (tmFiber5StateAt 2)
      tmFiber5State2_in_pass1_prefix
  rw [show [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10] = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9] ++ [tmFiber5StateAt 10] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber5StateAt 10) []
    (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9] [tmFiber5StateAt 0]) (tmFiber5StateAt 2)
    hparentBefore tmFiber5ReverseSingleStep10

theorem tmFiber5State11_in_pass1_prefix :
    tmFiber5StateAt 11 ∈ chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11] [tmFiber5StateAt 0] := by
  have hparentBefore :
      tmFiber5StateAt 3 ∈ chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10] [tmFiber5StateAt 0] := by
    rw [show [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10] = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3] ++ [tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10]
      (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3] [tmFiber5StateAt 0]) (tmFiber5StateAt 3)
      tmFiber5State3_in_pass1_prefix
  rw [show [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11] = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10] ++ [tmFiber5StateAt 11] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber5StateAt 11) []
    (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10] [tmFiber5StateAt 0]) (tmFiber5StateAt 3)
    hparentBefore tmFiber5ReverseSingleStep11

theorem tmFiber5State12_in_pass1_prefix :
    tmFiber5StateAt 12 ∈ chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12] [tmFiber5StateAt 0] := by
  have hparentBefore :
      tmFiber5StateAt 4 ∈ chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11] [tmFiber5StateAt 0] := by
    rw [show [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11] = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4] ++ [tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11]
      (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4] [tmFiber5StateAt 0]) (tmFiber5StateAt 4)
      tmFiber5State4_in_pass1_prefix
  rw [show [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12] = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11] ++ [tmFiber5StateAt 12] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber5StateAt 12) []
    (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11] [tmFiber5StateAt 0]) (tmFiber5StateAt 4)
    hparentBefore tmFiber5ReverseSingleStep12

theorem tmFiber5State13_in_pass1_prefix :
    tmFiber5StateAt 13 ∈ chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13] [tmFiber5StateAt 0] := by
  have hparentBefore :
      tmFiber5StateAt 5 ∈ chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12] [tmFiber5StateAt 0] := by
    rw [show [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12] = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5] ++ [tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12]
      (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5] [tmFiber5StateAt 0]) (tmFiber5StateAt 5)
      tmFiber5State5_in_pass1_prefix
  rw [show [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13] = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12] ++ [tmFiber5StateAt 13] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber5StateAt 13) []
    (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12] [tmFiber5StateAt 0]) (tmFiber5StateAt 5)
    hparentBefore tmFiber5ReverseSingleStep13

theorem tmFiber5State14_in_pass1_prefix :
    tmFiber5StateAt 14 ∈ chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14] [tmFiber5StateAt 0] := by
  have hparentBefore :
      tmFiber5StateAt 6 ∈ chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13] [tmFiber5StateAt 0] := by
    rw [show [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13] = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6] ++ [tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13]
      (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6] [tmFiber5StateAt 0]) (tmFiber5StateAt 6)
      tmFiber5State6_in_pass1_prefix
  rw [show [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14] = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13] ++ [tmFiber5StateAt 14] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber5StateAt 14) []
    (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13] [tmFiber5StateAt 0]) (tmFiber5StateAt 6)
    hparentBefore tmFiber5ReverseSingleStep14

theorem tmFiber5State15_in_pass1_prefix :
    tmFiber5StateAt 15 ∈ chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14, tmFiber5StateAt 15] [tmFiber5StateAt 0] := by
  have hparentBefore :
      tmFiber5StateAt 7 ∈ chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14] [tmFiber5StateAt 0] := by
    rw [show [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14] = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7] ++ [tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14]
      (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7] [tmFiber5StateAt 0]) (tmFiber5StateAt 7)
      tmFiber5State7_in_pass1_prefix
  rw [show [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14, tmFiber5StateAt 15] = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14] ++ [tmFiber5StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber5StateAt 15) []
    (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14] [tmFiber5StateAt 0]) (tmFiber5StateAt 7)
    hparentBefore tmFiber5ReverseSingleStep15

theorem tmFiber5State0_in_pass1_full :
    tmFiber5StateAt 0 ∈ chainClosureStep tmWord tmFiber5DirectStates [tmFiber5StateAt 0] := by
  rw [show tmFiber5DirectStates = [tmFiber5StateAt 0] ++ [tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14, tmFiber5StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14, tmFiber5StateAt 15]
    (chainClosureStep tmWord [tmFiber5StateAt 0] [tmFiber5StateAt 0]) (tmFiber5StateAt 0)
    tmFiber5State0_in_pass1_prefix

theorem tmFiber5State1_in_pass1_full :
    tmFiber5StateAt 1 ∈ chainClosureStep tmWord tmFiber5DirectStates [tmFiber5StateAt 0] := by
  rw [show tmFiber5DirectStates = [tmFiber5StateAt 0, tmFiber5StateAt 1] ++ [tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14, tmFiber5StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14, tmFiber5StateAt 15]
    (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1] [tmFiber5StateAt 0]) (tmFiber5StateAt 1)
    tmFiber5State1_in_pass1_prefix

theorem tmFiber5State2_in_pass1_full :
    tmFiber5StateAt 2 ∈ chainClosureStep tmWord tmFiber5DirectStates [tmFiber5StateAt 0] := by
  rw [show tmFiber5DirectStates = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2] ++ [tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14, tmFiber5StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14, tmFiber5StateAt 15]
    (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2] [tmFiber5StateAt 0]) (tmFiber5StateAt 2)
    tmFiber5State2_in_pass1_prefix

theorem tmFiber5State3_in_pass1_full :
    tmFiber5StateAt 3 ∈ chainClosureStep tmWord tmFiber5DirectStates [tmFiber5StateAt 0] := by
  rw [show tmFiber5DirectStates = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3] ++ [tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14, tmFiber5StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14, tmFiber5StateAt 15]
    (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3] [tmFiber5StateAt 0]) (tmFiber5StateAt 3)
    tmFiber5State3_in_pass1_prefix

theorem tmFiber5State4_in_pass1_full :
    tmFiber5StateAt 4 ∈ chainClosureStep tmWord tmFiber5DirectStates [tmFiber5StateAt 0] := by
  rw [show tmFiber5DirectStates = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4] ++ [tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14, tmFiber5StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14, tmFiber5StateAt 15]
    (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4] [tmFiber5StateAt 0]) (tmFiber5StateAt 4)
    tmFiber5State4_in_pass1_prefix

theorem tmFiber5State5_in_pass1_full :
    tmFiber5StateAt 5 ∈ chainClosureStep tmWord tmFiber5DirectStates [tmFiber5StateAt 0] := by
  rw [show tmFiber5DirectStates = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5] ++ [tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14, tmFiber5StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14, tmFiber5StateAt 15]
    (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5] [tmFiber5StateAt 0]) (tmFiber5StateAt 5)
    tmFiber5State5_in_pass1_prefix

theorem tmFiber5State6_in_pass1_full :
    tmFiber5StateAt 6 ∈ chainClosureStep tmWord tmFiber5DirectStates [tmFiber5StateAt 0] := by
  rw [show tmFiber5DirectStates = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6] ++ [tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14, tmFiber5StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14, tmFiber5StateAt 15]
    (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6] [tmFiber5StateAt 0]) (tmFiber5StateAt 6)
    tmFiber5State6_in_pass1_prefix

theorem tmFiber5State7_in_pass1_full :
    tmFiber5StateAt 7 ∈ chainClosureStep tmWord tmFiber5DirectStates [tmFiber5StateAt 0] := by
  rw [show tmFiber5DirectStates = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7] ++ [tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14, tmFiber5StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14, tmFiber5StateAt 15]
    (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7] [tmFiber5StateAt 0]) (tmFiber5StateAt 7)
    tmFiber5State7_in_pass1_prefix

theorem tmFiber5State8_in_pass1_full :
    tmFiber5StateAt 8 ∈ chainClosureStep tmWord tmFiber5DirectStates [tmFiber5StateAt 0] := by
  rw [show tmFiber5DirectStates = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8] ++ [tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14, tmFiber5StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14, tmFiber5StateAt 15]
    (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8] [tmFiber5StateAt 0]) (tmFiber5StateAt 8)
    tmFiber5State8_in_pass1_prefix

theorem tmFiber5State9_in_pass1_full :
    tmFiber5StateAt 9 ∈ chainClosureStep tmWord tmFiber5DirectStates [tmFiber5StateAt 0] := by
  rw [show tmFiber5DirectStates = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9] ++ [tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14, tmFiber5StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14, tmFiber5StateAt 15]
    (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9] [tmFiber5StateAt 0]) (tmFiber5StateAt 9)
    tmFiber5State9_in_pass1_prefix

theorem tmFiber5State10_in_pass1_full :
    tmFiber5StateAt 10 ∈ chainClosureStep tmWord tmFiber5DirectStates [tmFiber5StateAt 0] := by
  rw [show tmFiber5DirectStates = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10] ++ [tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14, tmFiber5StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14, tmFiber5StateAt 15]
    (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10] [tmFiber5StateAt 0]) (tmFiber5StateAt 10)
    tmFiber5State10_in_pass1_prefix

theorem tmFiber5State11_in_pass1_full :
    tmFiber5StateAt 11 ∈ chainClosureStep tmWord tmFiber5DirectStates [tmFiber5StateAt 0] := by
  rw [show tmFiber5DirectStates = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11] ++ [tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14, tmFiber5StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14, tmFiber5StateAt 15]
    (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11] [tmFiber5StateAt 0]) (tmFiber5StateAt 11)
    tmFiber5State11_in_pass1_prefix

theorem tmFiber5State12_in_pass1_full :
    tmFiber5StateAt 12 ∈ chainClosureStep tmWord tmFiber5DirectStates [tmFiber5StateAt 0] := by
  rw [show tmFiber5DirectStates = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12] ++ [tmFiber5StateAt 13, tmFiber5StateAt 14, tmFiber5StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber5StateAt 13, tmFiber5StateAt 14, tmFiber5StateAt 15]
    (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12] [tmFiber5StateAt 0]) (tmFiber5StateAt 12)
    tmFiber5State12_in_pass1_prefix

theorem tmFiber5State13_in_pass1_full :
    tmFiber5StateAt 13 ∈ chainClosureStep tmWord tmFiber5DirectStates [tmFiber5StateAt 0] := by
  rw [show tmFiber5DirectStates = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13] ++ [tmFiber5StateAt 14, tmFiber5StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber5StateAt 14, tmFiber5StateAt 15]
    (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13] [tmFiber5StateAt 0]) (tmFiber5StateAt 13)
    tmFiber5State13_in_pass1_prefix

theorem tmFiber5State14_in_pass1_full :
    tmFiber5StateAt 14 ∈ chainClosureStep tmWord tmFiber5DirectStates [tmFiber5StateAt 0] := by
  rw [show tmFiber5DirectStates = [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14] ++ [tmFiber5StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber5StateAt 15]
    (chainClosureStep tmWord [tmFiber5StateAt 0, tmFiber5StateAt 1, tmFiber5StateAt 2, tmFiber5StateAt 3, tmFiber5StateAt 4, tmFiber5StateAt 5, tmFiber5StateAt 6, tmFiber5StateAt 7, tmFiber5StateAt 8, tmFiber5StateAt 9, tmFiber5StateAt 10, tmFiber5StateAt 11, tmFiber5StateAt 12, tmFiber5StateAt 13, tmFiber5StateAt 14] [tmFiber5StateAt 0]) (tmFiber5StateAt 14)
    tmFiber5State14_in_pass1_prefix

theorem tmFiber5State15_in_pass1_full :
    tmFiber5StateAt 15 ∈ chainClosureStep tmWord tmFiber5DirectStates [tmFiber5StateAt 0] := by
  simpa [tmFiber5DirectStates] using tmFiber5State15_in_pass1_prefix

theorem tmFiber5State0_in_close :
    tmFiber5StateAt 0 ∈ closeChainFiber tmWord tmFiber5DirectStates tmFiber5DirectStates.length [tmFiber5StateAt 0] := by
  change tmFiber5StateAt 0 ∈ closeChainFiber tmWord tmFiber5DirectStates (15 + 1) [tmFiber5StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber5DirectStates 15 [tmFiber5StateAt 0] (tmFiber5StateAt 0) tmFiber5State0_in_pass1_full

theorem tmFiber5State1_in_close :
    tmFiber5StateAt 1 ∈ closeChainFiber tmWord tmFiber5DirectStates tmFiber5DirectStates.length [tmFiber5StateAt 0] := by
  change tmFiber5StateAt 1 ∈ closeChainFiber tmWord tmFiber5DirectStates (15 + 1) [tmFiber5StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber5DirectStates 15 [tmFiber5StateAt 0] (tmFiber5StateAt 1) tmFiber5State1_in_pass1_full

theorem tmFiber5State2_in_close :
    tmFiber5StateAt 2 ∈ closeChainFiber tmWord tmFiber5DirectStates tmFiber5DirectStates.length [tmFiber5StateAt 0] := by
  change tmFiber5StateAt 2 ∈ closeChainFiber tmWord tmFiber5DirectStates (15 + 1) [tmFiber5StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber5DirectStates 15 [tmFiber5StateAt 0] (tmFiber5StateAt 2) tmFiber5State2_in_pass1_full

theorem tmFiber5State3_in_close :
    tmFiber5StateAt 3 ∈ closeChainFiber tmWord tmFiber5DirectStates tmFiber5DirectStates.length [tmFiber5StateAt 0] := by
  change tmFiber5StateAt 3 ∈ closeChainFiber tmWord tmFiber5DirectStates (15 + 1) [tmFiber5StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber5DirectStates 15 [tmFiber5StateAt 0] (tmFiber5StateAt 3) tmFiber5State3_in_pass1_full

theorem tmFiber5State4_in_close :
    tmFiber5StateAt 4 ∈ closeChainFiber tmWord tmFiber5DirectStates tmFiber5DirectStates.length [tmFiber5StateAt 0] := by
  change tmFiber5StateAt 4 ∈ closeChainFiber tmWord tmFiber5DirectStates (15 + 1) [tmFiber5StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber5DirectStates 15 [tmFiber5StateAt 0] (tmFiber5StateAt 4) tmFiber5State4_in_pass1_full

theorem tmFiber5State5_in_close :
    tmFiber5StateAt 5 ∈ closeChainFiber tmWord tmFiber5DirectStates tmFiber5DirectStates.length [tmFiber5StateAt 0] := by
  change tmFiber5StateAt 5 ∈ closeChainFiber tmWord tmFiber5DirectStates (15 + 1) [tmFiber5StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber5DirectStates 15 [tmFiber5StateAt 0] (tmFiber5StateAt 5) tmFiber5State5_in_pass1_full

theorem tmFiber5State6_in_close :
    tmFiber5StateAt 6 ∈ closeChainFiber tmWord tmFiber5DirectStates tmFiber5DirectStates.length [tmFiber5StateAt 0] := by
  change tmFiber5StateAt 6 ∈ closeChainFiber tmWord tmFiber5DirectStates (15 + 1) [tmFiber5StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber5DirectStates 15 [tmFiber5StateAt 0] (tmFiber5StateAt 6) tmFiber5State6_in_pass1_full

theorem tmFiber5State7_in_close :
    tmFiber5StateAt 7 ∈ closeChainFiber tmWord tmFiber5DirectStates tmFiber5DirectStates.length [tmFiber5StateAt 0] := by
  change tmFiber5StateAt 7 ∈ closeChainFiber tmWord tmFiber5DirectStates (15 + 1) [tmFiber5StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber5DirectStates 15 [tmFiber5StateAt 0] (tmFiber5StateAt 7) tmFiber5State7_in_pass1_full

theorem tmFiber5State8_in_close :
    tmFiber5StateAt 8 ∈ closeChainFiber tmWord tmFiber5DirectStates tmFiber5DirectStates.length [tmFiber5StateAt 0] := by
  change tmFiber5StateAt 8 ∈ closeChainFiber tmWord tmFiber5DirectStates (15 + 1) [tmFiber5StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber5DirectStates 15 [tmFiber5StateAt 0] (tmFiber5StateAt 8) tmFiber5State8_in_pass1_full

theorem tmFiber5State9_in_close :
    tmFiber5StateAt 9 ∈ closeChainFiber tmWord tmFiber5DirectStates tmFiber5DirectStates.length [tmFiber5StateAt 0] := by
  change tmFiber5StateAt 9 ∈ closeChainFiber tmWord tmFiber5DirectStates (15 + 1) [tmFiber5StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber5DirectStates 15 [tmFiber5StateAt 0] (tmFiber5StateAt 9) tmFiber5State9_in_pass1_full

theorem tmFiber5State10_in_close :
    tmFiber5StateAt 10 ∈ closeChainFiber tmWord tmFiber5DirectStates tmFiber5DirectStates.length [tmFiber5StateAt 0] := by
  change tmFiber5StateAt 10 ∈ closeChainFiber tmWord tmFiber5DirectStates (15 + 1) [tmFiber5StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber5DirectStates 15 [tmFiber5StateAt 0] (tmFiber5StateAt 10) tmFiber5State10_in_pass1_full

theorem tmFiber5State11_in_close :
    tmFiber5StateAt 11 ∈ closeChainFiber tmWord tmFiber5DirectStates tmFiber5DirectStates.length [tmFiber5StateAt 0] := by
  change tmFiber5StateAt 11 ∈ closeChainFiber tmWord tmFiber5DirectStates (15 + 1) [tmFiber5StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber5DirectStates 15 [tmFiber5StateAt 0] (tmFiber5StateAt 11) tmFiber5State11_in_pass1_full

theorem tmFiber5State12_in_close :
    tmFiber5StateAt 12 ∈ closeChainFiber tmWord tmFiber5DirectStates tmFiber5DirectStates.length [tmFiber5StateAt 0] := by
  change tmFiber5StateAt 12 ∈ closeChainFiber tmWord tmFiber5DirectStates (15 + 1) [tmFiber5StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber5DirectStates 15 [tmFiber5StateAt 0] (tmFiber5StateAt 12) tmFiber5State12_in_pass1_full

theorem tmFiber5State13_in_close :
    tmFiber5StateAt 13 ∈ closeChainFiber tmWord tmFiber5DirectStates tmFiber5DirectStates.length [tmFiber5StateAt 0] := by
  change tmFiber5StateAt 13 ∈ closeChainFiber tmWord tmFiber5DirectStates (15 + 1) [tmFiber5StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber5DirectStates 15 [tmFiber5StateAt 0] (tmFiber5StateAt 13) tmFiber5State13_in_pass1_full

theorem tmFiber5State14_in_close :
    tmFiber5StateAt 14 ∈ closeChainFiber tmWord tmFiber5DirectStates tmFiber5DirectStates.length [tmFiber5StateAt 0] := by
  change tmFiber5StateAt 14 ∈ closeChainFiber tmWord tmFiber5DirectStates (15 + 1) [tmFiber5StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber5DirectStates 15 [tmFiber5StateAt 0] (tmFiber5StateAt 14) tmFiber5State14_in_pass1_full

theorem tmFiber5State15_in_close :
    tmFiber5StateAt 15 ∈ closeChainFiber tmWord tmFiber5DirectStates tmFiber5DirectStates.length [tmFiber5StateAt 0] := by
  change tmFiber5StateAt 15 ∈ closeChainFiber tmWord tmFiber5DirectStates (15 + 1) [tmFiber5StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber5DirectStates 15 [tmFiber5StateAt 0] (tmFiber5StateAt 15) tmFiber5State15_in_pass1_full

theorem tmFiber5DirectConnected :
    chainFiberConnected tmWord tmFiber5DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber5DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber5State0_in_close
  · subst state
    exact tmFiber5State1_in_close
  · subst state
    exact tmFiber5State2_in_close
  · subst state
    exact tmFiber5State3_in_close
  · subst state
    exact tmFiber5State4_in_close
  · subst state
    exact tmFiber5State5_in_close
  · subst state
    exact tmFiber5State6_in_close
  · subst state
    exact tmFiber5State7_in_close
  · subst state
    exact tmFiber5State8_in_close
  · subst state
    exact tmFiber5State9_in_close
  · subst state
    exact tmFiber5State10_in_close
  · subst state
    exact tmFiber5State11_in_close
  · subst state
    exact tmFiber5State12_in_close
  · subst state
    exact tmFiber5State13_in_close
  · subst state
    exact tmFiber5State14_in_close
  · subst state
    exact tmFiber5State15_in_close
  · cases h

def tmFiber6StateAt (i : Nat) : List TauState :=
  directStates (tmFiber6RowAt i).sourceLeft (tmFiber6RowAt i).sourceRight

def tmFiber6DirectStates : List (List TauState) :=
  [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14, tmFiber6StateAt 15]

theorem tmFiber6ReverseRow_1_ok :
    tmRowReverseValid tmFiber6Key tmFiber6Expected (tmFiber6RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber6Chunk0_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber6Chunk0] at h
  exact h.2

theorem tmFiber6ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber6StateAt 0) (tmFiber6StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber6StateAt 0) (tmFiber6StateAt 1)
    (tmFiber6RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber6Key tmFiber6Expected
        (tmFiber6RowAt 1) (by decide) tmFiber6ReverseRow_1_ok
      simpa [tmFiber6StateAt, tmFiber6RowAt, tmFiber6Rows, listGetD, directRow] using h)

theorem tmFiber6ReverseRow_2_ok :
    tmRowReverseValid tmFiber6Key tmFiber6Expected (tmFiber6RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber6Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber6Chunk1] at h
  exact h.1

theorem tmFiber6ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber6StateAt 0) (tmFiber6StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber6StateAt 0) (tmFiber6StateAt 2)
    (tmFiber6RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber6Key tmFiber6Expected
        (tmFiber6RowAt 2) (by decide) tmFiber6ReverseRow_2_ok
      simpa [tmFiber6StateAt, tmFiber6RowAt, tmFiber6Rows, listGetD, directRow] using h)

theorem tmFiber6ReverseRow_3_ok :
    tmRowReverseValid tmFiber6Key tmFiber6Expected (tmFiber6RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber6Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber6Chunk1] at h
  exact h.2

theorem tmFiber6ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber6StateAt 1) (tmFiber6StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber6StateAt 1) (tmFiber6StateAt 3)
    (tmFiber6RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber6Key tmFiber6Expected
        (tmFiber6RowAt 3) (by decide) tmFiber6ReverseRow_3_ok
      simpa [tmFiber6StateAt, tmFiber6RowAt, tmFiber6Rows, listGetD, directRow] using h)

theorem tmFiber6ReverseRow_4_ok :
    tmRowReverseValid tmFiber6Key tmFiber6Expected (tmFiber6RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber6Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber6Chunk2] at h
  exact h.1

theorem tmFiber6ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber6StateAt 0) (tmFiber6StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber6StateAt 0) (tmFiber6StateAt 4)
    (tmFiber6RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber6Key tmFiber6Expected
        (tmFiber6RowAt 4) (by decide) tmFiber6ReverseRow_4_ok
      simpa [tmFiber6StateAt, tmFiber6RowAt, tmFiber6Rows, listGetD, directRow] using h)

theorem tmFiber6ReverseRow_5_ok :
    tmRowReverseValid tmFiber6Key tmFiber6Expected (tmFiber6RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber6Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber6Chunk2] at h
  exact h.2

theorem tmFiber6ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber6StateAt 1) (tmFiber6StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber6StateAt 1) (tmFiber6StateAt 5)
    (tmFiber6RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber6Key tmFiber6Expected
        (tmFiber6RowAt 5) (by decide) tmFiber6ReverseRow_5_ok
      simpa [tmFiber6StateAt, tmFiber6RowAt, tmFiber6Rows, listGetD, directRow] using h)

theorem tmFiber6ReverseRow_6_ok :
    tmRowReverseValid tmFiber6Key tmFiber6Expected (tmFiber6RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber6Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber6Chunk3] at h
  exact h.1

theorem tmFiber6ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber6StateAt 2) (tmFiber6StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber6StateAt 2) (tmFiber6StateAt 6)
    (tmFiber6RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber6Key tmFiber6Expected
        (tmFiber6RowAt 6) (by decide) tmFiber6ReverseRow_6_ok
      simpa [tmFiber6StateAt, tmFiber6RowAt, tmFiber6Rows, listGetD, directRow] using h)

theorem tmFiber6ReverseRow_7_ok :
    tmRowReverseValid tmFiber6Key tmFiber6Expected (tmFiber6RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber6Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber6Chunk3] at h
  exact h.2

theorem tmFiber6ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber6StateAt 3) (tmFiber6StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber6StateAt 3) (tmFiber6StateAt 7)
    (tmFiber6RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber6Key tmFiber6Expected
        (tmFiber6RowAt 7) (by decide) tmFiber6ReverseRow_7_ok
      simpa [tmFiber6StateAt, tmFiber6RowAt, tmFiber6Rows, listGetD, directRow] using h)

theorem tmFiber6ReverseRow_8_ok :
    tmRowReverseValid tmFiber6Key tmFiber6Expected (tmFiber6RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber6Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber6Chunk4] at h
  exact h.1

theorem tmFiber6ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber6StateAt 0) (tmFiber6StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber6StateAt 0) (tmFiber6StateAt 8)
    (tmFiber6RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber6Key tmFiber6Expected
        (tmFiber6RowAt 8) (by decide) tmFiber6ReverseRow_8_ok
      simpa [tmFiber6StateAt, tmFiber6RowAt, tmFiber6Rows, listGetD, directRow] using h)

theorem tmFiber6ReverseRow_9_ok :
    tmRowReverseValid tmFiber6Key tmFiber6Expected (tmFiber6RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber6Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber6Chunk4] at h
  exact h.2

theorem tmFiber6ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber6StateAt 1) (tmFiber6StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber6StateAt 1) (tmFiber6StateAt 9)
    (tmFiber6RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber6Key tmFiber6Expected
        (tmFiber6RowAt 9) (by decide) tmFiber6ReverseRow_9_ok
      simpa [tmFiber6StateAt, tmFiber6RowAt, tmFiber6Rows, listGetD, directRow] using h)

theorem tmFiber6ReverseRow_10_ok :
    tmRowReverseValid tmFiber6Key tmFiber6Expected (tmFiber6RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber6Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber6Chunk5] at h
  exact h.1

theorem tmFiber6ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber6StateAt 2) (tmFiber6StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber6StateAt 2) (tmFiber6StateAt 10)
    (tmFiber6RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber6Key tmFiber6Expected
        (tmFiber6RowAt 10) (by decide) tmFiber6ReverseRow_10_ok
      simpa [tmFiber6StateAt, tmFiber6RowAt, tmFiber6Rows, listGetD, directRow] using h)

theorem tmFiber6ReverseRow_11_ok :
    tmRowReverseValid tmFiber6Key tmFiber6Expected (tmFiber6RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber6Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber6Chunk5] at h
  exact h.2

theorem tmFiber6ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber6StateAt 3) (tmFiber6StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber6StateAt 3) (tmFiber6StateAt 11)
    (tmFiber6RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber6Key tmFiber6Expected
        (tmFiber6RowAt 11) (by decide) tmFiber6ReverseRow_11_ok
      simpa [tmFiber6StateAt, tmFiber6RowAt, tmFiber6Rows, listGetD, directRow] using h)

theorem tmFiber6ReverseRow_12_ok :
    tmRowReverseValid tmFiber6Key tmFiber6Expected (tmFiber6RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber6Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber6Chunk6] at h
  exact h.1

theorem tmFiber6ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber6StateAt 4) (tmFiber6StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber6StateAt 4) (tmFiber6StateAt 12)
    (tmFiber6RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber6Key tmFiber6Expected
        (tmFiber6RowAt 12) (by decide) tmFiber6ReverseRow_12_ok
      simpa [tmFiber6StateAt, tmFiber6RowAt, tmFiber6Rows, listGetD, directRow] using h)

theorem tmFiber6ReverseRow_13_ok :
    tmRowReverseValid tmFiber6Key tmFiber6Expected (tmFiber6RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber6Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber6Chunk6] at h
  exact h.2

theorem tmFiber6ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber6StateAt 5) (tmFiber6StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber6StateAt 5) (tmFiber6StateAt 13)
    (tmFiber6RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber6Key tmFiber6Expected
        (tmFiber6RowAt 13) (by decide) tmFiber6ReverseRow_13_ok
      simpa [tmFiber6StateAt, tmFiber6RowAt, tmFiber6Rows, listGetD, directRow] using h)

theorem tmFiber6ReverseRow_14_ok :
    tmRowReverseValid tmFiber6Key tmFiber6Expected (tmFiber6RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber6Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber6Chunk7] at h
  exact h.1

theorem tmFiber6ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber6StateAt 6) (tmFiber6StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber6StateAt 6) (tmFiber6StateAt 14)
    (tmFiber6RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber6Key tmFiber6Expected
        (tmFiber6RowAt 14) (by decide) tmFiber6ReverseRow_14_ok
      simpa [tmFiber6StateAt, tmFiber6RowAt, tmFiber6Rows, listGetD, directRow] using h)

theorem tmFiber6ReverseRow_15_ok :
    tmRowReverseValid tmFiber6Key tmFiber6Expected (tmFiber6RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber6Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber6Chunk7] at h
  exact h.2

theorem tmFiber6ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber6StateAt 7) (tmFiber6StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber6StateAt 7) (tmFiber6StateAt 15)
    (tmFiber6RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber6Key tmFiber6Expected
        (tmFiber6RowAt 15) (by decide) tmFiber6ReverseRow_15_ok
      simpa [tmFiber6StateAt, tmFiber6RowAt, tmFiber6Rows, listGetD, directRow] using h)

theorem tmFiber6State0_in_pass1_prefix :
    tmFiber6StateAt 0 ∈ chainClosureStep tmWord [tmFiber6StateAt 0] [tmFiber6StateAt 0] := by
  exact chainClosureStep_mem_of_seen tmWord [tmFiber6StateAt 0] [tmFiber6StateAt 0] (tmFiber6StateAt 0) (by simp)

theorem tmFiber6State1_in_pass1_prefix :
    tmFiber6StateAt 1 ∈ chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1] [tmFiber6StateAt 0] := by
  have hparentBefore :
      tmFiber6StateAt 0 ∈ chainClosureStep tmWord [tmFiber6StateAt 0] [tmFiber6StateAt 0] := by
    exact tmFiber6State0_in_pass1_prefix
  rw [show [tmFiber6StateAt 0, tmFiber6StateAt 1] = [tmFiber6StateAt 0] ++ [tmFiber6StateAt 1] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber6StateAt 1) []
    (chainClosureStep tmWord [tmFiber6StateAt 0] [tmFiber6StateAt 0]) (tmFiber6StateAt 0)
    hparentBefore tmFiber6ReverseSingleStep1

theorem tmFiber6State2_in_pass1_prefix :
    tmFiber6StateAt 2 ∈ chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2] [tmFiber6StateAt 0] := by
  have hparentBefore :
      tmFiber6StateAt 0 ∈ chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1] [tmFiber6StateAt 0] := by
    rw [show [tmFiber6StateAt 0, tmFiber6StateAt 1] = [tmFiber6StateAt 0] ++ [tmFiber6StateAt 1] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber6StateAt 1]
      (chainClosureStep tmWord [tmFiber6StateAt 0] [tmFiber6StateAt 0]) (tmFiber6StateAt 0)
      tmFiber6State0_in_pass1_prefix
  rw [show [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2] = [tmFiber6StateAt 0, tmFiber6StateAt 1] ++ [tmFiber6StateAt 2] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber6StateAt 2) []
    (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1] [tmFiber6StateAt 0]) (tmFiber6StateAt 0)
    hparentBefore tmFiber6ReverseSingleStep2

theorem tmFiber6State3_in_pass1_prefix :
    tmFiber6StateAt 3 ∈ chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3] [tmFiber6StateAt 0] := by
  have hparentBefore :
      tmFiber6StateAt 1 ∈ chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2] [tmFiber6StateAt 0] := by
    rw [show [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2] = [tmFiber6StateAt 0, tmFiber6StateAt 1] ++ [tmFiber6StateAt 2] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber6StateAt 2]
      (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1] [tmFiber6StateAt 0]) (tmFiber6StateAt 1)
      tmFiber6State1_in_pass1_prefix
  rw [show [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3] = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2] ++ [tmFiber6StateAt 3] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber6StateAt 3) []
    (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2] [tmFiber6StateAt 0]) (tmFiber6StateAt 1)
    hparentBefore tmFiber6ReverseSingleStep3

theorem tmFiber6State4_in_pass1_prefix :
    tmFiber6StateAt 4 ∈ chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4] [tmFiber6StateAt 0] := by
  have hparentBefore :
      tmFiber6StateAt 0 ∈ chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3] [tmFiber6StateAt 0] := by
    rw [show [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3] = [tmFiber6StateAt 0] ++ [tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3]
      (chainClosureStep tmWord [tmFiber6StateAt 0] [tmFiber6StateAt 0]) (tmFiber6StateAt 0)
      tmFiber6State0_in_pass1_prefix
  rw [show [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4] = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3] ++ [tmFiber6StateAt 4] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber6StateAt 4) []
    (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3] [tmFiber6StateAt 0]) (tmFiber6StateAt 0)
    hparentBefore tmFiber6ReverseSingleStep4

theorem tmFiber6State5_in_pass1_prefix :
    tmFiber6StateAt 5 ∈ chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5] [tmFiber6StateAt 0] := by
  have hparentBefore :
      tmFiber6StateAt 1 ∈ chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4] [tmFiber6StateAt 0] := by
    rw [show [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4] = [tmFiber6StateAt 0, tmFiber6StateAt 1] ++ [tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4]
      (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1] [tmFiber6StateAt 0]) (tmFiber6StateAt 1)
      tmFiber6State1_in_pass1_prefix
  rw [show [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5] = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4] ++ [tmFiber6StateAt 5] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber6StateAt 5) []
    (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4] [tmFiber6StateAt 0]) (tmFiber6StateAt 1)
    hparentBefore tmFiber6ReverseSingleStep5

theorem tmFiber6State6_in_pass1_prefix :
    tmFiber6StateAt 6 ∈ chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6] [tmFiber6StateAt 0] := by
  have hparentBefore :
      tmFiber6StateAt 2 ∈ chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5] [tmFiber6StateAt 0] := by
    rw [show [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5] = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2] ++ [tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5]
      (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2] [tmFiber6StateAt 0]) (tmFiber6StateAt 2)
      tmFiber6State2_in_pass1_prefix
  rw [show [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6] = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5] ++ [tmFiber6StateAt 6] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber6StateAt 6) []
    (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5] [tmFiber6StateAt 0]) (tmFiber6StateAt 2)
    hparentBefore tmFiber6ReverseSingleStep6

theorem tmFiber6State7_in_pass1_prefix :
    tmFiber6StateAt 7 ∈ chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7] [tmFiber6StateAt 0] := by
  have hparentBefore :
      tmFiber6StateAt 3 ∈ chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6] [tmFiber6StateAt 0] := by
    rw [show [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6] = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3] ++ [tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6]
      (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3] [tmFiber6StateAt 0]) (tmFiber6StateAt 3)
      tmFiber6State3_in_pass1_prefix
  rw [show [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7] = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6] ++ [tmFiber6StateAt 7] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber6StateAt 7) []
    (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6] [tmFiber6StateAt 0]) (tmFiber6StateAt 3)
    hparentBefore tmFiber6ReverseSingleStep7

theorem tmFiber6State8_in_pass1_prefix :
    tmFiber6StateAt 8 ∈ chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8] [tmFiber6StateAt 0] := by
  have hparentBefore :
      tmFiber6StateAt 0 ∈ chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7] [tmFiber6StateAt 0] := by
    rw [show [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7] = [tmFiber6StateAt 0] ++ [tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7]
      (chainClosureStep tmWord [tmFiber6StateAt 0] [tmFiber6StateAt 0]) (tmFiber6StateAt 0)
      tmFiber6State0_in_pass1_prefix
  rw [show [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8] = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7] ++ [tmFiber6StateAt 8] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber6StateAt 8) []
    (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7] [tmFiber6StateAt 0]) (tmFiber6StateAt 0)
    hparentBefore tmFiber6ReverseSingleStep8

theorem tmFiber6State9_in_pass1_prefix :
    tmFiber6StateAt 9 ∈ chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9] [tmFiber6StateAt 0] := by
  have hparentBefore :
      tmFiber6StateAt 1 ∈ chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8] [tmFiber6StateAt 0] := by
    rw [show [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8] = [tmFiber6StateAt 0, tmFiber6StateAt 1] ++ [tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8]
      (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1] [tmFiber6StateAt 0]) (tmFiber6StateAt 1)
      tmFiber6State1_in_pass1_prefix
  rw [show [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9] = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8] ++ [tmFiber6StateAt 9] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber6StateAt 9) []
    (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8] [tmFiber6StateAt 0]) (tmFiber6StateAt 1)
    hparentBefore tmFiber6ReverseSingleStep9

theorem tmFiber6State10_in_pass1_prefix :
    tmFiber6StateAt 10 ∈ chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10] [tmFiber6StateAt 0] := by
  have hparentBefore :
      tmFiber6StateAt 2 ∈ chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9] [tmFiber6StateAt 0] := by
    rw [show [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9] = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2] ++ [tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9]
      (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2] [tmFiber6StateAt 0]) (tmFiber6StateAt 2)
      tmFiber6State2_in_pass1_prefix
  rw [show [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10] = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9] ++ [tmFiber6StateAt 10] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber6StateAt 10) []
    (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9] [tmFiber6StateAt 0]) (tmFiber6StateAt 2)
    hparentBefore tmFiber6ReverseSingleStep10

theorem tmFiber6State11_in_pass1_prefix :
    tmFiber6StateAt 11 ∈ chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11] [tmFiber6StateAt 0] := by
  have hparentBefore :
      tmFiber6StateAt 3 ∈ chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10] [tmFiber6StateAt 0] := by
    rw [show [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10] = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3] ++ [tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10]
      (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3] [tmFiber6StateAt 0]) (tmFiber6StateAt 3)
      tmFiber6State3_in_pass1_prefix
  rw [show [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11] = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10] ++ [tmFiber6StateAt 11] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber6StateAt 11) []
    (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10] [tmFiber6StateAt 0]) (tmFiber6StateAt 3)
    hparentBefore tmFiber6ReverseSingleStep11

theorem tmFiber6State12_in_pass1_prefix :
    tmFiber6StateAt 12 ∈ chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12] [tmFiber6StateAt 0] := by
  have hparentBefore :
      tmFiber6StateAt 4 ∈ chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11] [tmFiber6StateAt 0] := by
    rw [show [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11] = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4] ++ [tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11]
      (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4] [tmFiber6StateAt 0]) (tmFiber6StateAt 4)
      tmFiber6State4_in_pass1_prefix
  rw [show [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12] = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11] ++ [tmFiber6StateAt 12] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber6StateAt 12) []
    (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11] [tmFiber6StateAt 0]) (tmFiber6StateAt 4)
    hparentBefore tmFiber6ReverseSingleStep12

theorem tmFiber6State13_in_pass1_prefix :
    tmFiber6StateAt 13 ∈ chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13] [tmFiber6StateAt 0] := by
  have hparentBefore :
      tmFiber6StateAt 5 ∈ chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12] [tmFiber6StateAt 0] := by
    rw [show [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12] = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5] ++ [tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12]
      (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5] [tmFiber6StateAt 0]) (tmFiber6StateAt 5)
      tmFiber6State5_in_pass1_prefix
  rw [show [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13] = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12] ++ [tmFiber6StateAt 13] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber6StateAt 13) []
    (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12] [tmFiber6StateAt 0]) (tmFiber6StateAt 5)
    hparentBefore tmFiber6ReverseSingleStep13

theorem tmFiber6State14_in_pass1_prefix :
    tmFiber6StateAt 14 ∈ chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14] [tmFiber6StateAt 0] := by
  have hparentBefore :
      tmFiber6StateAt 6 ∈ chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13] [tmFiber6StateAt 0] := by
    rw [show [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13] = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6] ++ [tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13]
      (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6] [tmFiber6StateAt 0]) (tmFiber6StateAt 6)
      tmFiber6State6_in_pass1_prefix
  rw [show [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14] = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13] ++ [tmFiber6StateAt 14] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber6StateAt 14) []
    (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13] [tmFiber6StateAt 0]) (tmFiber6StateAt 6)
    hparentBefore tmFiber6ReverseSingleStep14

theorem tmFiber6State15_in_pass1_prefix :
    tmFiber6StateAt 15 ∈ chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14, tmFiber6StateAt 15] [tmFiber6StateAt 0] := by
  have hparentBefore :
      tmFiber6StateAt 7 ∈ chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14] [tmFiber6StateAt 0] := by
    rw [show [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14] = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7] ++ [tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14]
      (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7] [tmFiber6StateAt 0]) (tmFiber6StateAt 7)
      tmFiber6State7_in_pass1_prefix
  rw [show [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14, tmFiber6StateAt 15] = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14] ++ [tmFiber6StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber6StateAt 15) []
    (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14] [tmFiber6StateAt 0]) (tmFiber6StateAt 7)
    hparentBefore tmFiber6ReverseSingleStep15

theorem tmFiber6State0_in_pass1_full :
    tmFiber6StateAt 0 ∈ chainClosureStep tmWord tmFiber6DirectStates [tmFiber6StateAt 0] := by
  rw [show tmFiber6DirectStates = [tmFiber6StateAt 0] ++ [tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14, tmFiber6StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14, tmFiber6StateAt 15]
    (chainClosureStep tmWord [tmFiber6StateAt 0] [tmFiber6StateAt 0]) (tmFiber6StateAt 0)
    tmFiber6State0_in_pass1_prefix

theorem tmFiber6State1_in_pass1_full :
    tmFiber6StateAt 1 ∈ chainClosureStep tmWord tmFiber6DirectStates [tmFiber6StateAt 0] := by
  rw [show tmFiber6DirectStates = [tmFiber6StateAt 0, tmFiber6StateAt 1] ++ [tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14, tmFiber6StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14, tmFiber6StateAt 15]
    (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1] [tmFiber6StateAt 0]) (tmFiber6StateAt 1)
    tmFiber6State1_in_pass1_prefix

theorem tmFiber6State2_in_pass1_full :
    tmFiber6StateAt 2 ∈ chainClosureStep tmWord tmFiber6DirectStates [tmFiber6StateAt 0] := by
  rw [show tmFiber6DirectStates = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2] ++ [tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14, tmFiber6StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14, tmFiber6StateAt 15]
    (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2] [tmFiber6StateAt 0]) (tmFiber6StateAt 2)
    tmFiber6State2_in_pass1_prefix

theorem tmFiber6State3_in_pass1_full :
    tmFiber6StateAt 3 ∈ chainClosureStep tmWord tmFiber6DirectStates [tmFiber6StateAt 0] := by
  rw [show tmFiber6DirectStates = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3] ++ [tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14, tmFiber6StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14, tmFiber6StateAt 15]
    (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3] [tmFiber6StateAt 0]) (tmFiber6StateAt 3)
    tmFiber6State3_in_pass1_prefix

theorem tmFiber6State4_in_pass1_full :
    tmFiber6StateAt 4 ∈ chainClosureStep tmWord tmFiber6DirectStates [tmFiber6StateAt 0] := by
  rw [show tmFiber6DirectStates = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4] ++ [tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14, tmFiber6StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14, tmFiber6StateAt 15]
    (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4] [tmFiber6StateAt 0]) (tmFiber6StateAt 4)
    tmFiber6State4_in_pass1_prefix

theorem tmFiber6State5_in_pass1_full :
    tmFiber6StateAt 5 ∈ chainClosureStep tmWord tmFiber6DirectStates [tmFiber6StateAt 0] := by
  rw [show tmFiber6DirectStates = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5] ++ [tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14, tmFiber6StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14, tmFiber6StateAt 15]
    (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5] [tmFiber6StateAt 0]) (tmFiber6StateAt 5)
    tmFiber6State5_in_pass1_prefix

theorem tmFiber6State6_in_pass1_full :
    tmFiber6StateAt 6 ∈ chainClosureStep tmWord tmFiber6DirectStates [tmFiber6StateAt 0] := by
  rw [show tmFiber6DirectStates = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6] ++ [tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14, tmFiber6StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14, tmFiber6StateAt 15]
    (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6] [tmFiber6StateAt 0]) (tmFiber6StateAt 6)
    tmFiber6State6_in_pass1_prefix

theorem tmFiber6State7_in_pass1_full :
    tmFiber6StateAt 7 ∈ chainClosureStep tmWord tmFiber6DirectStates [tmFiber6StateAt 0] := by
  rw [show tmFiber6DirectStates = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7] ++ [tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14, tmFiber6StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14, tmFiber6StateAt 15]
    (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7] [tmFiber6StateAt 0]) (tmFiber6StateAt 7)
    tmFiber6State7_in_pass1_prefix

theorem tmFiber6State8_in_pass1_full :
    tmFiber6StateAt 8 ∈ chainClosureStep tmWord tmFiber6DirectStates [tmFiber6StateAt 0] := by
  rw [show tmFiber6DirectStates = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8] ++ [tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14, tmFiber6StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14, tmFiber6StateAt 15]
    (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8] [tmFiber6StateAt 0]) (tmFiber6StateAt 8)
    tmFiber6State8_in_pass1_prefix

theorem tmFiber6State9_in_pass1_full :
    tmFiber6StateAt 9 ∈ chainClosureStep tmWord tmFiber6DirectStates [tmFiber6StateAt 0] := by
  rw [show tmFiber6DirectStates = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9] ++ [tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14, tmFiber6StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14, tmFiber6StateAt 15]
    (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9] [tmFiber6StateAt 0]) (tmFiber6StateAt 9)
    tmFiber6State9_in_pass1_prefix

theorem tmFiber6State10_in_pass1_full :
    tmFiber6StateAt 10 ∈ chainClosureStep tmWord tmFiber6DirectStates [tmFiber6StateAt 0] := by
  rw [show tmFiber6DirectStates = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10] ++ [tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14, tmFiber6StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14, tmFiber6StateAt 15]
    (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10] [tmFiber6StateAt 0]) (tmFiber6StateAt 10)
    tmFiber6State10_in_pass1_prefix

theorem tmFiber6State11_in_pass1_full :
    tmFiber6StateAt 11 ∈ chainClosureStep tmWord tmFiber6DirectStates [tmFiber6StateAt 0] := by
  rw [show tmFiber6DirectStates = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11] ++ [tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14, tmFiber6StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14, tmFiber6StateAt 15]
    (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11] [tmFiber6StateAt 0]) (tmFiber6StateAt 11)
    tmFiber6State11_in_pass1_prefix

theorem tmFiber6State12_in_pass1_full :
    tmFiber6StateAt 12 ∈ chainClosureStep tmWord tmFiber6DirectStates [tmFiber6StateAt 0] := by
  rw [show tmFiber6DirectStates = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12] ++ [tmFiber6StateAt 13, tmFiber6StateAt 14, tmFiber6StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber6StateAt 13, tmFiber6StateAt 14, tmFiber6StateAt 15]
    (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12] [tmFiber6StateAt 0]) (tmFiber6StateAt 12)
    tmFiber6State12_in_pass1_prefix

theorem tmFiber6State13_in_pass1_full :
    tmFiber6StateAt 13 ∈ chainClosureStep tmWord tmFiber6DirectStates [tmFiber6StateAt 0] := by
  rw [show tmFiber6DirectStates = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13] ++ [tmFiber6StateAt 14, tmFiber6StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber6StateAt 14, tmFiber6StateAt 15]
    (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13] [tmFiber6StateAt 0]) (tmFiber6StateAt 13)
    tmFiber6State13_in_pass1_prefix

theorem tmFiber6State14_in_pass1_full :
    tmFiber6StateAt 14 ∈ chainClosureStep tmWord tmFiber6DirectStates [tmFiber6StateAt 0] := by
  rw [show tmFiber6DirectStates = [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14] ++ [tmFiber6StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber6StateAt 15]
    (chainClosureStep tmWord [tmFiber6StateAt 0, tmFiber6StateAt 1, tmFiber6StateAt 2, tmFiber6StateAt 3, tmFiber6StateAt 4, tmFiber6StateAt 5, tmFiber6StateAt 6, tmFiber6StateAt 7, tmFiber6StateAt 8, tmFiber6StateAt 9, tmFiber6StateAt 10, tmFiber6StateAt 11, tmFiber6StateAt 12, tmFiber6StateAt 13, tmFiber6StateAt 14] [tmFiber6StateAt 0]) (tmFiber6StateAt 14)
    tmFiber6State14_in_pass1_prefix

theorem tmFiber6State15_in_pass1_full :
    tmFiber6StateAt 15 ∈ chainClosureStep tmWord tmFiber6DirectStates [tmFiber6StateAt 0] := by
  simpa [tmFiber6DirectStates] using tmFiber6State15_in_pass1_prefix

theorem tmFiber6State0_in_close :
    tmFiber6StateAt 0 ∈ closeChainFiber tmWord tmFiber6DirectStates tmFiber6DirectStates.length [tmFiber6StateAt 0] := by
  change tmFiber6StateAt 0 ∈ closeChainFiber tmWord tmFiber6DirectStates (15 + 1) [tmFiber6StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber6DirectStates 15 [tmFiber6StateAt 0] (tmFiber6StateAt 0) tmFiber6State0_in_pass1_full

theorem tmFiber6State1_in_close :
    tmFiber6StateAt 1 ∈ closeChainFiber tmWord tmFiber6DirectStates tmFiber6DirectStates.length [tmFiber6StateAt 0] := by
  change tmFiber6StateAt 1 ∈ closeChainFiber tmWord tmFiber6DirectStates (15 + 1) [tmFiber6StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber6DirectStates 15 [tmFiber6StateAt 0] (tmFiber6StateAt 1) tmFiber6State1_in_pass1_full

theorem tmFiber6State2_in_close :
    tmFiber6StateAt 2 ∈ closeChainFiber tmWord tmFiber6DirectStates tmFiber6DirectStates.length [tmFiber6StateAt 0] := by
  change tmFiber6StateAt 2 ∈ closeChainFiber tmWord tmFiber6DirectStates (15 + 1) [tmFiber6StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber6DirectStates 15 [tmFiber6StateAt 0] (tmFiber6StateAt 2) tmFiber6State2_in_pass1_full

theorem tmFiber6State3_in_close :
    tmFiber6StateAt 3 ∈ closeChainFiber tmWord tmFiber6DirectStates tmFiber6DirectStates.length [tmFiber6StateAt 0] := by
  change tmFiber6StateAt 3 ∈ closeChainFiber tmWord tmFiber6DirectStates (15 + 1) [tmFiber6StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber6DirectStates 15 [tmFiber6StateAt 0] (tmFiber6StateAt 3) tmFiber6State3_in_pass1_full

theorem tmFiber6State4_in_close :
    tmFiber6StateAt 4 ∈ closeChainFiber tmWord tmFiber6DirectStates tmFiber6DirectStates.length [tmFiber6StateAt 0] := by
  change tmFiber6StateAt 4 ∈ closeChainFiber tmWord tmFiber6DirectStates (15 + 1) [tmFiber6StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber6DirectStates 15 [tmFiber6StateAt 0] (tmFiber6StateAt 4) tmFiber6State4_in_pass1_full

theorem tmFiber6State5_in_close :
    tmFiber6StateAt 5 ∈ closeChainFiber tmWord tmFiber6DirectStates tmFiber6DirectStates.length [tmFiber6StateAt 0] := by
  change tmFiber6StateAt 5 ∈ closeChainFiber tmWord tmFiber6DirectStates (15 + 1) [tmFiber6StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber6DirectStates 15 [tmFiber6StateAt 0] (tmFiber6StateAt 5) tmFiber6State5_in_pass1_full

theorem tmFiber6State6_in_close :
    tmFiber6StateAt 6 ∈ closeChainFiber tmWord tmFiber6DirectStates tmFiber6DirectStates.length [tmFiber6StateAt 0] := by
  change tmFiber6StateAt 6 ∈ closeChainFiber tmWord tmFiber6DirectStates (15 + 1) [tmFiber6StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber6DirectStates 15 [tmFiber6StateAt 0] (tmFiber6StateAt 6) tmFiber6State6_in_pass1_full

theorem tmFiber6State7_in_close :
    tmFiber6StateAt 7 ∈ closeChainFiber tmWord tmFiber6DirectStates tmFiber6DirectStates.length [tmFiber6StateAt 0] := by
  change tmFiber6StateAt 7 ∈ closeChainFiber tmWord tmFiber6DirectStates (15 + 1) [tmFiber6StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber6DirectStates 15 [tmFiber6StateAt 0] (tmFiber6StateAt 7) tmFiber6State7_in_pass1_full

theorem tmFiber6State8_in_close :
    tmFiber6StateAt 8 ∈ closeChainFiber tmWord tmFiber6DirectStates tmFiber6DirectStates.length [tmFiber6StateAt 0] := by
  change tmFiber6StateAt 8 ∈ closeChainFiber tmWord tmFiber6DirectStates (15 + 1) [tmFiber6StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber6DirectStates 15 [tmFiber6StateAt 0] (tmFiber6StateAt 8) tmFiber6State8_in_pass1_full

theorem tmFiber6State9_in_close :
    tmFiber6StateAt 9 ∈ closeChainFiber tmWord tmFiber6DirectStates tmFiber6DirectStates.length [tmFiber6StateAt 0] := by
  change tmFiber6StateAt 9 ∈ closeChainFiber tmWord tmFiber6DirectStates (15 + 1) [tmFiber6StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber6DirectStates 15 [tmFiber6StateAt 0] (tmFiber6StateAt 9) tmFiber6State9_in_pass1_full

theorem tmFiber6State10_in_close :
    tmFiber6StateAt 10 ∈ closeChainFiber tmWord tmFiber6DirectStates tmFiber6DirectStates.length [tmFiber6StateAt 0] := by
  change tmFiber6StateAt 10 ∈ closeChainFiber tmWord tmFiber6DirectStates (15 + 1) [tmFiber6StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber6DirectStates 15 [tmFiber6StateAt 0] (tmFiber6StateAt 10) tmFiber6State10_in_pass1_full

theorem tmFiber6State11_in_close :
    tmFiber6StateAt 11 ∈ closeChainFiber tmWord tmFiber6DirectStates tmFiber6DirectStates.length [tmFiber6StateAt 0] := by
  change tmFiber6StateAt 11 ∈ closeChainFiber tmWord tmFiber6DirectStates (15 + 1) [tmFiber6StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber6DirectStates 15 [tmFiber6StateAt 0] (tmFiber6StateAt 11) tmFiber6State11_in_pass1_full

theorem tmFiber6State12_in_close :
    tmFiber6StateAt 12 ∈ closeChainFiber tmWord tmFiber6DirectStates tmFiber6DirectStates.length [tmFiber6StateAt 0] := by
  change tmFiber6StateAt 12 ∈ closeChainFiber tmWord tmFiber6DirectStates (15 + 1) [tmFiber6StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber6DirectStates 15 [tmFiber6StateAt 0] (tmFiber6StateAt 12) tmFiber6State12_in_pass1_full

theorem tmFiber6State13_in_close :
    tmFiber6StateAt 13 ∈ closeChainFiber tmWord tmFiber6DirectStates tmFiber6DirectStates.length [tmFiber6StateAt 0] := by
  change tmFiber6StateAt 13 ∈ closeChainFiber tmWord tmFiber6DirectStates (15 + 1) [tmFiber6StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber6DirectStates 15 [tmFiber6StateAt 0] (tmFiber6StateAt 13) tmFiber6State13_in_pass1_full

theorem tmFiber6State14_in_close :
    tmFiber6StateAt 14 ∈ closeChainFiber tmWord tmFiber6DirectStates tmFiber6DirectStates.length [tmFiber6StateAt 0] := by
  change tmFiber6StateAt 14 ∈ closeChainFiber tmWord tmFiber6DirectStates (15 + 1) [tmFiber6StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber6DirectStates 15 [tmFiber6StateAt 0] (tmFiber6StateAt 14) tmFiber6State14_in_pass1_full

theorem tmFiber6State15_in_close :
    tmFiber6StateAt 15 ∈ closeChainFiber tmWord tmFiber6DirectStates tmFiber6DirectStates.length [tmFiber6StateAt 0] := by
  change tmFiber6StateAt 15 ∈ closeChainFiber tmWord tmFiber6DirectStates (15 + 1) [tmFiber6StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber6DirectStates 15 [tmFiber6StateAt 0] (tmFiber6StateAt 15) tmFiber6State15_in_pass1_full

theorem tmFiber6DirectConnected :
    chainFiberConnected tmWord tmFiber6DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber6DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber6State0_in_close
  · subst state
    exact tmFiber6State1_in_close
  · subst state
    exact tmFiber6State2_in_close
  · subst state
    exact tmFiber6State3_in_close
  · subst state
    exact tmFiber6State4_in_close
  · subst state
    exact tmFiber6State5_in_close
  · subst state
    exact tmFiber6State6_in_close
  · subst state
    exact tmFiber6State7_in_close
  · subst state
    exact tmFiber6State8_in_close
  · subst state
    exact tmFiber6State9_in_close
  · subst state
    exact tmFiber6State10_in_close
  · subst state
    exact tmFiber6State11_in_close
  · subst state
    exact tmFiber6State12_in_close
  · subst state
    exact tmFiber6State13_in_close
  · subst state
    exact tmFiber6State14_in_close
  · subst state
    exact tmFiber6State15_in_close
  · cases h

def tmFiber7StateAt (i : Nat) : List TauState :=
  directStates (tmFiber7RowAt i).sourceLeft (tmFiber7RowAt i).sourceRight

def tmFiber7DirectStates : List (List TauState) :=
  [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14, tmFiber7StateAt 15]

theorem tmFiber7ReverseRow_1_ok :
    tmRowReverseValid tmFiber7Key tmFiber7Expected (tmFiber7RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber7Chunk0_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber7Chunk0] at h
  exact h.2

theorem tmFiber7ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber7StateAt 0) (tmFiber7StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber7StateAt 0) (tmFiber7StateAt 1)
    (tmFiber7RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber7Key tmFiber7Expected
        (tmFiber7RowAt 1) (by decide) tmFiber7ReverseRow_1_ok
      simpa [tmFiber7StateAt, tmFiber7RowAt, tmFiber7Rows, listGetD, directRow] using h)

theorem tmFiber7ReverseRow_2_ok :
    tmRowReverseValid tmFiber7Key tmFiber7Expected (tmFiber7RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber7Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber7Chunk1] at h
  exact h.1

theorem tmFiber7ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber7StateAt 0) (tmFiber7StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber7StateAt 0) (tmFiber7StateAt 2)
    (tmFiber7RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber7Key tmFiber7Expected
        (tmFiber7RowAt 2) (by decide) tmFiber7ReverseRow_2_ok
      simpa [tmFiber7StateAt, tmFiber7RowAt, tmFiber7Rows, listGetD, directRow] using h)

theorem tmFiber7ReverseRow_3_ok :
    tmRowReverseValid tmFiber7Key tmFiber7Expected (tmFiber7RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber7Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber7Chunk1] at h
  exact h.2

theorem tmFiber7ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber7StateAt 1) (tmFiber7StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber7StateAt 1) (tmFiber7StateAt 3)
    (tmFiber7RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber7Key tmFiber7Expected
        (tmFiber7RowAt 3) (by decide) tmFiber7ReverseRow_3_ok
      simpa [tmFiber7StateAt, tmFiber7RowAt, tmFiber7Rows, listGetD, directRow] using h)

theorem tmFiber7ReverseRow_4_ok :
    tmRowReverseValid tmFiber7Key tmFiber7Expected (tmFiber7RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber7Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber7Chunk2] at h
  exact h.1

theorem tmFiber7ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber7StateAt 0) (tmFiber7StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber7StateAt 0) (tmFiber7StateAt 4)
    (tmFiber7RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber7Key tmFiber7Expected
        (tmFiber7RowAt 4) (by decide) tmFiber7ReverseRow_4_ok
      simpa [tmFiber7StateAt, tmFiber7RowAt, tmFiber7Rows, listGetD, directRow] using h)

theorem tmFiber7ReverseRow_5_ok :
    tmRowReverseValid tmFiber7Key tmFiber7Expected (tmFiber7RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber7Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber7Chunk2] at h
  exact h.2

theorem tmFiber7ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber7StateAt 1) (tmFiber7StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber7StateAt 1) (tmFiber7StateAt 5)
    (tmFiber7RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber7Key tmFiber7Expected
        (tmFiber7RowAt 5) (by decide) tmFiber7ReverseRow_5_ok
      simpa [tmFiber7StateAt, tmFiber7RowAt, tmFiber7Rows, listGetD, directRow] using h)

theorem tmFiber7ReverseRow_6_ok :
    tmRowReverseValid tmFiber7Key tmFiber7Expected (tmFiber7RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber7Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber7Chunk3] at h
  exact h.1

theorem tmFiber7ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber7StateAt 2) (tmFiber7StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber7StateAt 2) (tmFiber7StateAt 6)
    (tmFiber7RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber7Key tmFiber7Expected
        (tmFiber7RowAt 6) (by decide) tmFiber7ReverseRow_6_ok
      simpa [tmFiber7StateAt, tmFiber7RowAt, tmFiber7Rows, listGetD, directRow] using h)

theorem tmFiber7ReverseRow_7_ok :
    tmRowReverseValid tmFiber7Key tmFiber7Expected (tmFiber7RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber7Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber7Chunk3] at h
  exact h.2

theorem tmFiber7ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber7StateAt 3) (tmFiber7StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber7StateAt 3) (tmFiber7StateAt 7)
    (tmFiber7RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber7Key tmFiber7Expected
        (tmFiber7RowAt 7) (by decide) tmFiber7ReverseRow_7_ok
      simpa [tmFiber7StateAt, tmFiber7RowAt, tmFiber7Rows, listGetD, directRow] using h)

theorem tmFiber7ReverseRow_8_ok :
    tmRowReverseValid tmFiber7Key tmFiber7Expected (tmFiber7RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber7Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber7Chunk4] at h
  exact h.1

theorem tmFiber7ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber7StateAt 4) (tmFiber7StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber7StateAt 4) (tmFiber7StateAt 8)
    (tmFiber7RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber7Key tmFiber7Expected
        (tmFiber7RowAt 8) (by decide) tmFiber7ReverseRow_8_ok
      simpa [tmFiber7StateAt, tmFiber7RowAt, tmFiber7Rows, listGetD, directRow] using h)

theorem tmFiber7ReverseRow_9_ok :
    tmRowReverseValid tmFiber7Key tmFiber7Expected (tmFiber7RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber7Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber7Chunk4] at h
  exact h.2

theorem tmFiber7ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber7StateAt 5) (tmFiber7StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber7StateAt 5) (tmFiber7StateAt 9)
    (tmFiber7RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber7Key tmFiber7Expected
        (tmFiber7RowAt 9) (by decide) tmFiber7ReverseRow_9_ok
      simpa [tmFiber7StateAt, tmFiber7RowAt, tmFiber7Rows, listGetD, directRow] using h)

theorem tmFiber7ReverseRow_10_ok :
    tmRowReverseValid tmFiber7Key tmFiber7Expected (tmFiber7RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber7Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber7Chunk5] at h
  exact h.1

theorem tmFiber7ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber7StateAt 6) (tmFiber7StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber7StateAt 6) (tmFiber7StateAt 10)
    (tmFiber7RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber7Key tmFiber7Expected
        (tmFiber7RowAt 10) (by decide) tmFiber7ReverseRow_10_ok
      simpa [tmFiber7StateAt, tmFiber7RowAt, tmFiber7Rows, listGetD, directRow] using h)

theorem tmFiber7ReverseRow_11_ok :
    tmRowReverseValid tmFiber7Key tmFiber7Expected (tmFiber7RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber7Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber7Chunk5] at h
  exact h.2

theorem tmFiber7ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber7StateAt 7) (tmFiber7StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber7StateAt 7) (tmFiber7StateAt 11)
    (tmFiber7RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber7Key tmFiber7Expected
        (tmFiber7RowAt 11) (by decide) tmFiber7ReverseRow_11_ok
      simpa [tmFiber7StateAt, tmFiber7RowAt, tmFiber7Rows, listGetD, directRow] using h)

theorem tmFiber7ReverseRow_12_ok :
    tmRowReverseValid tmFiber7Key tmFiber7Expected (tmFiber7RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber7Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber7Chunk6] at h
  exact h.1

theorem tmFiber7ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber7StateAt 0) (tmFiber7StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber7StateAt 0) (tmFiber7StateAt 12)
    (tmFiber7RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber7Key tmFiber7Expected
        (tmFiber7RowAt 12) (by decide) tmFiber7ReverseRow_12_ok
      simpa [tmFiber7StateAt, tmFiber7RowAt, tmFiber7Rows, listGetD, directRow] using h)

theorem tmFiber7ReverseRow_13_ok :
    tmRowReverseValid tmFiber7Key tmFiber7Expected (tmFiber7RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber7Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber7Chunk6] at h
  exact h.2

theorem tmFiber7ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber7StateAt 1) (tmFiber7StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber7StateAt 1) (tmFiber7StateAt 13)
    (tmFiber7RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber7Key tmFiber7Expected
        (tmFiber7RowAt 13) (by decide) tmFiber7ReverseRow_13_ok
      simpa [tmFiber7StateAt, tmFiber7RowAt, tmFiber7Rows, listGetD, directRow] using h)

theorem tmFiber7ReverseRow_14_ok :
    tmRowReverseValid tmFiber7Key tmFiber7Expected (tmFiber7RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber7Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber7Chunk7] at h
  exact h.1

theorem tmFiber7ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber7StateAt 2) (tmFiber7StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber7StateAt 2) (tmFiber7StateAt 14)
    (tmFiber7RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber7Key tmFiber7Expected
        (tmFiber7RowAt 14) (by decide) tmFiber7ReverseRow_14_ok
      simpa [tmFiber7StateAt, tmFiber7RowAt, tmFiber7Rows, listGetD, directRow] using h)

theorem tmFiber7ReverseRow_15_ok :
    tmRowReverseValid tmFiber7Key tmFiber7Expected (tmFiber7RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber7Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber7Chunk7] at h
  exact h.2

theorem tmFiber7ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber7StateAt 3) (tmFiber7StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber7StateAt 3) (tmFiber7StateAt 15)
    (tmFiber7RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber7Key tmFiber7Expected
        (tmFiber7RowAt 15) (by decide) tmFiber7ReverseRow_15_ok
      simpa [tmFiber7StateAt, tmFiber7RowAt, tmFiber7Rows, listGetD, directRow] using h)

theorem tmFiber7State0_in_pass1_prefix :
    tmFiber7StateAt 0 ∈ chainClosureStep tmWord [tmFiber7StateAt 0] [tmFiber7StateAt 0] := by
  exact chainClosureStep_mem_of_seen tmWord [tmFiber7StateAt 0] [tmFiber7StateAt 0] (tmFiber7StateAt 0) (by simp)

theorem tmFiber7State1_in_pass1_prefix :
    tmFiber7StateAt 1 ∈ chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1] [tmFiber7StateAt 0] := by
  have hparentBefore :
      tmFiber7StateAt 0 ∈ chainClosureStep tmWord [tmFiber7StateAt 0] [tmFiber7StateAt 0] := by
    exact tmFiber7State0_in_pass1_prefix
  rw [show [tmFiber7StateAt 0, tmFiber7StateAt 1] = [tmFiber7StateAt 0] ++ [tmFiber7StateAt 1] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber7StateAt 1) []
    (chainClosureStep tmWord [tmFiber7StateAt 0] [tmFiber7StateAt 0]) (tmFiber7StateAt 0)
    hparentBefore tmFiber7ReverseSingleStep1

theorem tmFiber7State2_in_pass1_prefix :
    tmFiber7StateAt 2 ∈ chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2] [tmFiber7StateAt 0] := by
  have hparentBefore :
      tmFiber7StateAt 0 ∈ chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1] [tmFiber7StateAt 0] := by
    rw [show [tmFiber7StateAt 0, tmFiber7StateAt 1] = [tmFiber7StateAt 0] ++ [tmFiber7StateAt 1] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber7StateAt 1]
      (chainClosureStep tmWord [tmFiber7StateAt 0] [tmFiber7StateAt 0]) (tmFiber7StateAt 0)
      tmFiber7State0_in_pass1_prefix
  rw [show [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2] = [tmFiber7StateAt 0, tmFiber7StateAt 1] ++ [tmFiber7StateAt 2] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber7StateAt 2) []
    (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1] [tmFiber7StateAt 0]) (tmFiber7StateAt 0)
    hparentBefore tmFiber7ReverseSingleStep2

theorem tmFiber7State3_in_pass1_prefix :
    tmFiber7StateAt 3 ∈ chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3] [tmFiber7StateAt 0] := by
  have hparentBefore :
      tmFiber7StateAt 1 ∈ chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2] [tmFiber7StateAt 0] := by
    rw [show [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2] = [tmFiber7StateAt 0, tmFiber7StateAt 1] ++ [tmFiber7StateAt 2] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber7StateAt 2]
      (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1] [tmFiber7StateAt 0]) (tmFiber7StateAt 1)
      tmFiber7State1_in_pass1_prefix
  rw [show [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3] = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2] ++ [tmFiber7StateAt 3] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber7StateAt 3) []
    (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2] [tmFiber7StateAt 0]) (tmFiber7StateAt 1)
    hparentBefore tmFiber7ReverseSingleStep3

theorem tmFiber7State4_in_pass1_prefix :
    tmFiber7StateAt 4 ∈ chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4] [tmFiber7StateAt 0] := by
  have hparentBefore :
      tmFiber7StateAt 0 ∈ chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3] [tmFiber7StateAt 0] := by
    rw [show [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3] = [tmFiber7StateAt 0] ++ [tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3]
      (chainClosureStep tmWord [tmFiber7StateAt 0] [tmFiber7StateAt 0]) (tmFiber7StateAt 0)
      tmFiber7State0_in_pass1_prefix
  rw [show [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4] = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3] ++ [tmFiber7StateAt 4] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber7StateAt 4) []
    (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3] [tmFiber7StateAt 0]) (tmFiber7StateAt 0)
    hparentBefore tmFiber7ReverseSingleStep4

theorem tmFiber7State5_in_pass1_prefix :
    tmFiber7StateAt 5 ∈ chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5] [tmFiber7StateAt 0] := by
  have hparentBefore :
      tmFiber7StateAt 1 ∈ chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4] [tmFiber7StateAt 0] := by
    rw [show [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4] = [tmFiber7StateAt 0, tmFiber7StateAt 1] ++ [tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4]
      (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1] [tmFiber7StateAt 0]) (tmFiber7StateAt 1)
      tmFiber7State1_in_pass1_prefix
  rw [show [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5] = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4] ++ [tmFiber7StateAt 5] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber7StateAt 5) []
    (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4] [tmFiber7StateAt 0]) (tmFiber7StateAt 1)
    hparentBefore tmFiber7ReverseSingleStep5

theorem tmFiber7State6_in_pass1_prefix :
    tmFiber7StateAt 6 ∈ chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6] [tmFiber7StateAt 0] := by
  have hparentBefore :
      tmFiber7StateAt 2 ∈ chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5] [tmFiber7StateAt 0] := by
    rw [show [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5] = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2] ++ [tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5]
      (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2] [tmFiber7StateAt 0]) (tmFiber7StateAt 2)
      tmFiber7State2_in_pass1_prefix
  rw [show [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6] = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5] ++ [tmFiber7StateAt 6] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber7StateAt 6) []
    (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5] [tmFiber7StateAt 0]) (tmFiber7StateAt 2)
    hparentBefore tmFiber7ReverseSingleStep6

theorem tmFiber7State7_in_pass1_prefix :
    tmFiber7StateAt 7 ∈ chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7] [tmFiber7StateAt 0] := by
  have hparentBefore :
      tmFiber7StateAt 3 ∈ chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6] [tmFiber7StateAt 0] := by
    rw [show [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6] = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3] ++ [tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6]
      (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3] [tmFiber7StateAt 0]) (tmFiber7StateAt 3)
      tmFiber7State3_in_pass1_prefix
  rw [show [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7] = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6] ++ [tmFiber7StateAt 7] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber7StateAt 7) []
    (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6] [tmFiber7StateAt 0]) (tmFiber7StateAt 3)
    hparentBefore tmFiber7ReverseSingleStep7

theorem tmFiber7State8_in_pass1_prefix :
    tmFiber7StateAt 8 ∈ chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8] [tmFiber7StateAt 0] := by
  have hparentBefore :
      tmFiber7StateAt 4 ∈ chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7] [tmFiber7StateAt 0] := by
    rw [show [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7] = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4] ++ [tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7]
      (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4] [tmFiber7StateAt 0]) (tmFiber7StateAt 4)
      tmFiber7State4_in_pass1_prefix
  rw [show [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8] = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7] ++ [tmFiber7StateAt 8] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber7StateAt 8) []
    (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7] [tmFiber7StateAt 0]) (tmFiber7StateAt 4)
    hparentBefore tmFiber7ReverseSingleStep8

theorem tmFiber7State9_in_pass1_prefix :
    tmFiber7StateAt 9 ∈ chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9] [tmFiber7StateAt 0] := by
  have hparentBefore :
      tmFiber7StateAt 5 ∈ chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8] [tmFiber7StateAt 0] := by
    rw [show [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8] = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5] ++ [tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8]
      (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5] [tmFiber7StateAt 0]) (tmFiber7StateAt 5)
      tmFiber7State5_in_pass1_prefix
  rw [show [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9] = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8] ++ [tmFiber7StateAt 9] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber7StateAt 9) []
    (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8] [tmFiber7StateAt 0]) (tmFiber7StateAt 5)
    hparentBefore tmFiber7ReverseSingleStep9

theorem tmFiber7State10_in_pass1_prefix :
    tmFiber7StateAt 10 ∈ chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10] [tmFiber7StateAt 0] := by
  have hparentBefore :
      tmFiber7StateAt 6 ∈ chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9] [tmFiber7StateAt 0] := by
    rw [show [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9] = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6] ++ [tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9]
      (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6] [tmFiber7StateAt 0]) (tmFiber7StateAt 6)
      tmFiber7State6_in_pass1_prefix
  rw [show [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10] = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9] ++ [tmFiber7StateAt 10] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber7StateAt 10) []
    (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9] [tmFiber7StateAt 0]) (tmFiber7StateAt 6)
    hparentBefore tmFiber7ReverseSingleStep10

theorem tmFiber7State11_in_pass1_prefix :
    tmFiber7StateAt 11 ∈ chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11] [tmFiber7StateAt 0] := by
  have hparentBefore :
      tmFiber7StateAt 7 ∈ chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10] [tmFiber7StateAt 0] := by
    rw [show [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10] = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7] ++ [tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10]
      (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7] [tmFiber7StateAt 0]) (tmFiber7StateAt 7)
      tmFiber7State7_in_pass1_prefix
  rw [show [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11] = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10] ++ [tmFiber7StateAt 11] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber7StateAt 11) []
    (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10] [tmFiber7StateAt 0]) (tmFiber7StateAt 7)
    hparentBefore tmFiber7ReverseSingleStep11

theorem tmFiber7State12_in_pass1_prefix :
    tmFiber7StateAt 12 ∈ chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12] [tmFiber7StateAt 0] := by
  have hparentBefore :
      tmFiber7StateAt 0 ∈ chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11] [tmFiber7StateAt 0] := by
    rw [show [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11] = [tmFiber7StateAt 0] ++ [tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11]
      (chainClosureStep tmWord [tmFiber7StateAt 0] [tmFiber7StateAt 0]) (tmFiber7StateAt 0)
      tmFiber7State0_in_pass1_prefix
  rw [show [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12] = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11] ++ [tmFiber7StateAt 12] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber7StateAt 12) []
    (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11] [tmFiber7StateAt 0]) (tmFiber7StateAt 0)
    hparentBefore tmFiber7ReverseSingleStep12

theorem tmFiber7State13_in_pass1_prefix :
    tmFiber7StateAt 13 ∈ chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13] [tmFiber7StateAt 0] := by
  have hparentBefore :
      tmFiber7StateAt 1 ∈ chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12] [tmFiber7StateAt 0] := by
    rw [show [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12] = [tmFiber7StateAt 0, tmFiber7StateAt 1] ++ [tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12]
      (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1] [tmFiber7StateAt 0]) (tmFiber7StateAt 1)
      tmFiber7State1_in_pass1_prefix
  rw [show [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13] = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12] ++ [tmFiber7StateAt 13] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber7StateAt 13) []
    (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12] [tmFiber7StateAt 0]) (tmFiber7StateAt 1)
    hparentBefore tmFiber7ReverseSingleStep13

theorem tmFiber7State14_in_pass1_prefix :
    tmFiber7StateAt 14 ∈ chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14] [tmFiber7StateAt 0] := by
  have hparentBefore :
      tmFiber7StateAt 2 ∈ chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13] [tmFiber7StateAt 0] := by
    rw [show [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13] = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2] ++ [tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13]
      (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2] [tmFiber7StateAt 0]) (tmFiber7StateAt 2)
      tmFiber7State2_in_pass1_prefix
  rw [show [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14] = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13] ++ [tmFiber7StateAt 14] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber7StateAt 14) []
    (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13] [tmFiber7StateAt 0]) (tmFiber7StateAt 2)
    hparentBefore tmFiber7ReverseSingleStep14

theorem tmFiber7State15_in_pass1_prefix :
    tmFiber7StateAt 15 ∈ chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14, tmFiber7StateAt 15] [tmFiber7StateAt 0] := by
  have hparentBefore :
      tmFiber7StateAt 3 ∈ chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14] [tmFiber7StateAt 0] := by
    rw [show [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14] = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3] ++ [tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14]
      (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3] [tmFiber7StateAt 0]) (tmFiber7StateAt 3)
      tmFiber7State3_in_pass1_prefix
  rw [show [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14, tmFiber7StateAt 15] = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14] ++ [tmFiber7StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber7StateAt 15) []
    (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14] [tmFiber7StateAt 0]) (tmFiber7StateAt 3)
    hparentBefore tmFiber7ReverseSingleStep15

theorem tmFiber7State0_in_pass1_full :
    tmFiber7StateAt 0 ∈ chainClosureStep tmWord tmFiber7DirectStates [tmFiber7StateAt 0] := by
  rw [show tmFiber7DirectStates = [tmFiber7StateAt 0] ++ [tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14, tmFiber7StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14, tmFiber7StateAt 15]
    (chainClosureStep tmWord [tmFiber7StateAt 0] [tmFiber7StateAt 0]) (tmFiber7StateAt 0)
    tmFiber7State0_in_pass1_prefix

theorem tmFiber7State1_in_pass1_full :
    tmFiber7StateAt 1 ∈ chainClosureStep tmWord tmFiber7DirectStates [tmFiber7StateAt 0] := by
  rw [show tmFiber7DirectStates = [tmFiber7StateAt 0, tmFiber7StateAt 1] ++ [tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14, tmFiber7StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14, tmFiber7StateAt 15]
    (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1] [tmFiber7StateAt 0]) (tmFiber7StateAt 1)
    tmFiber7State1_in_pass1_prefix

theorem tmFiber7State2_in_pass1_full :
    tmFiber7StateAt 2 ∈ chainClosureStep tmWord tmFiber7DirectStates [tmFiber7StateAt 0] := by
  rw [show tmFiber7DirectStates = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2] ++ [tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14, tmFiber7StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14, tmFiber7StateAt 15]
    (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2] [tmFiber7StateAt 0]) (tmFiber7StateAt 2)
    tmFiber7State2_in_pass1_prefix

theorem tmFiber7State3_in_pass1_full :
    tmFiber7StateAt 3 ∈ chainClosureStep tmWord tmFiber7DirectStates [tmFiber7StateAt 0] := by
  rw [show tmFiber7DirectStates = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3] ++ [tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14, tmFiber7StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14, tmFiber7StateAt 15]
    (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3] [tmFiber7StateAt 0]) (tmFiber7StateAt 3)
    tmFiber7State3_in_pass1_prefix

theorem tmFiber7State4_in_pass1_full :
    tmFiber7StateAt 4 ∈ chainClosureStep tmWord tmFiber7DirectStates [tmFiber7StateAt 0] := by
  rw [show tmFiber7DirectStates = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4] ++ [tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14, tmFiber7StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14, tmFiber7StateAt 15]
    (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4] [tmFiber7StateAt 0]) (tmFiber7StateAt 4)
    tmFiber7State4_in_pass1_prefix

theorem tmFiber7State5_in_pass1_full :
    tmFiber7StateAt 5 ∈ chainClosureStep tmWord tmFiber7DirectStates [tmFiber7StateAt 0] := by
  rw [show tmFiber7DirectStates = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5] ++ [tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14, tmFiber7StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14, tmFiber7StateAt 15]
    (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5] [tmFiber7StateAt 0]) (tmFiber7StateAt 5)
    tmFiber7State5_in_pass1_prefix

theorem tmFiber7State6_in_pass1_full :
    tmFiber7StateAt 6 ∈ chainClosureStep tmWord tmFiber7DirectStates [tmFiber7StateAt 0] := by
  rw [show tmFiber7DirectStates = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6] ++ [tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14, tmFiber7StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14, tmFiber7StateAt 15]
    (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6] [tmFiber7StateAt 0]) (tmFiber7StateAt 6)
    tmFiber7State6_in_pass1_prefix

theorem tmFiber7State7_in_pass1_full :
    tmFiber7StateAt 7 ∈ chainClosureStep tmWord tmFiber7DirectStates [tmFiber7StateAt 0] := by
  rw [show tmFiber7DirectStates = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7] ++ [tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14, tmFiber7StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14, tmFiber7StateAt 15]
    (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7] [tmFiber7StateAt 0]) (tmFiber7StateAt 7)
    tmFiber7State7_in_pass1_prefix

theorem tmFiber7State8_in_pass1_full :
    tmFiber7StateAt 8 ∈ chainClosureStep tmWord tmFiber7DirectStates [tmFiber7StateAt 0] := by
  rw [show tmFiber7DirectStates = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8] ++ [tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14, tmFiber7StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14, tmFiber7StateAt 15]
    (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8] [tmFiber7StateAt 0]) (tmFiber7StateAt 8)
    tmFiber7State8_in_pass1_prefix

theorem tmFiber7State9_in_pass1_full :
    tmFiber7StateAt 9 ∈ chainClosureStep tmWord tmFiber7DirectStates [tmFiber7StateAt 0] := by
  rw [show tmFiber7DirectStates = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9] ++ [tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14, tmFiber7StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14, tmFiber7StateAt 15]
    (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9] [tmFiber7StateAt 0]) (tmFiber7StateAt 9)
    tmFiber7State9_in_pass1_prefix

theorem tmFiber7State10_in_pass1_full :
    tmFiber7StateAt 10 ∈ chainClosureStep tmWord tmFiber7DirectStates [tmFiber7StateAt 0] := by
  rw [show tmFiber7DirectStates = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10] ++ [tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14, tmFiber7StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14, tmFiber7StateAt 15]
    (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10] [tmFiber7StateAt 0]) (tmFiber7StateAt 10)
    tmFiber7State10_in_pass1_prefix

theorem tmFiber7State11_in_pass1_full :
    tmFiber7StateAt 11 ∈ chainClosureStep tmWord tmFiber7DirectStates [tmFiber7StateAt 0] := by
  rw [show tmFiber7DirectStates = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11] ++ [tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14, tmFiber7StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14, tmFiber7StateAt 15]
    (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11] [tmFiber7StateAt 0]) (tmFiber7StateAt 11)
    tmFiber7State11_in_pass1_prefix

theorem tmFiber7State12_in_pass1_full :
    tmFiber7StateAt 12 ∈ chainClosureStep tmWord tmFiber7DirectStates [tmFiber7StateAt 0] := by
  rw [show tmFiber7DirectStates = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12] ++ [tmFiber7StateAt 13, tmFiber7StateAt 14, tmFiber7StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber7StateAt 13, tmFiber7StateAt 14, tmFiber7StateAt 15]
    (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12] [tmFiber7StateAt 0]) (tmFiber7StateAt 12)
    tmFiber7State12_in_pass1_prefix

theorem tmFiber7State13_in_pass1_full :
    tmFiber7StateAt 13 ∈ chainClosureStep tmWord tmFiber7DirectStates [tmFiber7StateAt 0] := by
  rw [show tmFiber7DirectStates = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13] ++ [tmFiber7StateAt 14, tmFiber7StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber7StateAt 14, tmFiber7StateAt 15]
    (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13] [tmFiber7StateAt 0]) (tmFiber7StateAt 13)
    tmFiber7State13_in_pass1_prefix

theorem tmFiber7State14_in_pass1_full :
    tmFiber7StateAt 14 ∈ chainClosureStep tmWord tmFiber7DirectStates [tmFiber7StateAt 0] := by
  rw [show tmFiber7DirectStates = [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14] ++ [tmFiber7StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber7StateAt 15]
    (chainClosureStep tmWord [tmFiber7StateAt 0, tmFiber7StateAt 1, tmFiber7StateAt 2, tmFiber7StateAt 3, tmFiber7StateAt 4, tmFiber7StateAt 5, tmFiber7StateAt 6, tmFiber7StateAt 7, tmFiber7StateAt 8, tmFiber7StateAt 9, tmFiber7StateAt 10, tmFiber7StateAt 11, tmFiber7StateAt 12, tmFiber7StateAt 13, tmFiber7StateAt 14] [tmFiber7StateAt 0]) (tmFiber7StateAt 14)
    tmFiber7State14_in_pass1_prefix

theorem tmFiber7State15_in_pass1_full :
    tmFiber7StateAt 15 ∈ chainClosureStep tmWord tmFiber7DirectStates [tmFiber7StateAt 0] := by
  simpa [tmFiber7DirectStates] using tmFiber7State15_in_pass1_prefix

theorem tmFiber7State0_in_close :
    tmFiber7StateAt 0 ∈ closeChainFiber tmWord tmFiber7DirectStates tmFiber7DirectStates.length [tmFiber7StateAt 0] := by
  change tmFiber7StateAt 0 ∈ closeChainFiber tmWord tmFiber7DirectStates (15 + 1) [tmFiber7StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber7DirectStates 15 [tmFiber7StateAt 0] (tmFiber7StateAt 0) tmFiber7State0_in_pass1_full

theorem tmFiber7State1_in_close :
    tmFiber7StateAt 1 ∈ closeChainFiber tmWord tmFiber7DirectStates tmFiber7DirectStates.length [tmFiber7StateAt 0] := by
  change tmFiber7StateAt 1 ∈ closeChainFiber tmWord tmFiber7DirectStates (15 + 1) [tmFiber7StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber7DirectStates 15 [tmFiber7StateAt 0] (tmFiber7StateAt 1) tmFiber7State1_in_pass1_full

theorem tmFiber7State2_in_close :
    tmFiber7StateAt 2 ∈ closeChainFiber tmWord tmFiber7DirectStates tmFiber7DirectStates.length [tmFiber7StateAt 0] := by
  change tmFiber7StateAt 2 ∈ closeChainFiber tmWord tmFiber7DirectStates (15 + 1) [tmFiber7StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber7DirectStates 15 [tmFiber7StateAt 0] (tmFiber7StateAt 2) tmFiber7State2_in_pass1_full

theorem tmFiber7State3_in_close :
    tmFiber7StateAt 3 ∈ closeChainFiber tmWord tmFiber7DirectStates tmFiber7DirectStates.length [tmFiber7StateAt 0] := by
  change tmFiber7StateAt 3 ∈ closeChainFiber tmWord tmFiber7DirectStates (15 + 1) [tmFiber7StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber7DirectStates 15 [tmFiber7StateAt 0] (tmFiber7StateAt 3) tmFiber7State3_in_pass1_full

theorem tmFiber7State4_in_close :
    tmFiber7StateAt 4 ∈ closeChainFiber tmWord tmFiber7DirectStates tmFiber7DirectStates.length [tmFiber7StateAt 0] := by
  change tmFiber7StateAt 4 ∈ closeChainFiber tmWord tmFiber7DirectStates (15 + 1) [tmFiber7StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber7DirectStates 15 [tmFiber7StateAt 0] (tmFiber7StateAt 4) tmFiber7State4_in_pass1_full

theorem tmFiber7State5_in_close :
    tmFiber7StateAt 5 ∈ closeChainFiber tmWord tmFiber7DirectStates tmFiber7DirectStates.length [tmFiber7StateAt 0] := by
  change tmFiber7StateAt 5 ∈ closeChainFiber tmWord tmFiber7DirectStates (15 + 1) [tmFiber7StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber7DirectStates 15 [tmFiber7StateAt 0] (tmFiber7StateAt 5) tmFiber7State5_in_pass1_full

theorem tmFiber7State6_in_close :
    tmFiber7StateAt 6 ∈ closeChainFiber tmWord tmFiber7DirectStates tmFiber7DirectStates.length [tmFiber7StateAt 0] := by
  change tmFiber7StateAt 6 ∈ closeChainFiber tmWord tmFiber7DirectStates (15 + 1) [tmFiber7StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber7DirectStates 15 [tmFiber7StateAt 0] (tmFiber7StateAt 6) tmFiber7State6_in_pass1_full

theorem tmFiber7State7_in_close :
    tmFiber7StateAt 7 ∈ closeChainFiber tmWord tmFiber7DirectStates tmFiber7DirectStates.length [tmFiber7StateAt 0] := by
  change tmFiber7StateAt 7 ∈ closeChainFiber tmWord tmFiber7DirectStates (15 + 1) [tmFiber7StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber7DirectStates 15 [tmFiber7StateAt 0] (tmFiber7StateAt 7) tmFiber7State7_in_pass1_full

theorem tmFiber7State8_in_close :
    tmFiber7StateAt 8 ∈ closeChainFiber tmWord tmFiber7DirectStates tmFiber7DirectStates.length [tmFiber7StateAt 0] := by
  change tmFiber7StateAt 8 ∈ closeChainFiber tmWord tmFiber7DirectStates (15 + 1) [tmFiber7StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber7DirectStates 15 [tmFiber7StateAt 0] (tmFiber7StateAt 8) tmFiber7State8_in_pass1_full

theorem tmFiber7State9_in_close :
    tmFiber7StateAt 9 ∈ closeChainFiber tmWord tmFiber7DirectStates tmFiber7DirectStates.length [tmFiber7StateAt 0] := by
  change tmFiber7StateAt 9 ∈ closeChainFiber tmWord tmFiber7DirectStates (15 + 1) [tmFiber7StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber7DirectStates 15 [tmFiber7StateAt 0] (tmFiber7StateAt 9) tmFiber7State9_in_pass1_full

theorem tmFiber7State10_in_close :
    tmFiber7StateAt 10 ∈ closeChainFiber tmWord tmFiber7DirectStates tmFiber7DirectStates.length [tmFiber7StateAt 0] := by
  change tmFiber7StateAt 10 ∈ closeChainFiber tmWord tmFiber7DirectStates (15 + 1) [tmFiber7StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber7DirectStates 15 [tmFiber7StateAt 0] (tmFiber7StateAt 10) tmFiber7State10_in_pass1_full

theorem tmFiber7State11_in_close :
    tmFiber7StateAt 11 ∈ closeChainFiber tmWord tmFiber7DirectStates tmFiber7DirectStates.length [tmFiber7StateAt 0] := by
  change tmFiber7StateAt 11 ∈ closeChainFiber tmWord tmFiber7DirectStates (15 + 1) [tmFiber7StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber7DirectStates 15 [tmFiber7StateAt 0] (tmFiber7StateAt 11) tmFiber7State11_in_pass1_full

theorem tmFiber7State12_in_close :
    tmFiber7StateAt 12 ∈ closeChainFiber tmWord tmFiber7DirectStates tmFiber7DirectStates.length [tmFiber7StateAt 0] := by
  change tmFiber7StateAt 12 ∈ closeChainFiber tmWord tmFiber7DirectStates (15 + 1) [tmFiber7StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber7DirectStates 15 [tmFiber7StateAt 0] (tmFiber7StateAt 12) tmFiber7State12_in_pass1_full

theorem tmFiber7State13_in_close :
    tmFiber7StateAt 13 ∈ closeChainFiber tmWord tmFiber7DirectStates tmFiber7DirectStates.length [tmFiber7StateAt 0] := by
  change tmFiber7StateAt 13 ∈ closeChainFiber tmWord tmFiber7DirectStates (15 + 1) [tmFiber7StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber7DirectStates 15 [tmFiber7StateAt 0] (tmFiber7StateAt 13) tmFiber7State13_in_pass1_full

theorem tmFiber7State14_in_close :
    tmFiber7StateAt 14 ∈ closeChainFiber tmWord tmFiber7DirectStates tmFiber7DirectStates.length [tmFiber7StateAt 0] := by
  change tmFiber7StateAt 14 ∈ closeChainFiber tmWord tmFiber7DirectStates (15 + 1) [tmFiber7StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber7DirectStates 15 [tmFiber7StateAt 0] (tmFiber7StateAt 14) tmFiber7State14_in_pass1_full

theorem tmFiber7State15_in_close :
    tmFiber7StateAt 15 ∈ closeChainFiber tmWord tmFiber7DirectStates tmFiber7DirectStates.length [tmFiber7StateAt 0] := by
  change tmFiber7StateAt 15 ∈ closeChainFiber tmWord tmFiber7DirectStates (15 + 1) [tmFiber7StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber7DirectStates 15 [tmFiber7StateAt 0] (tmFiber7StateAt 15) tmFiber7State15_in_pass1_full

theorem tmFiber7DirectConnected :
    chainFiberConnected tmWord tmFiber7DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber7DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber7State0_in_close
  · subst state
    exact tmFiber7State1_in_close
  · subst state
    exact tmFiber7State2_in_close
  · subst state
    exact tmFiber7State3_in_close
  · subst state
    exact tmFiber7State4_in_close
  · subst state
    exact tmFiber7State5_in_close
  · subst state
    exact tmFiber7State6_in_close
  · subst state
    exact tmFiber7State7_in_close
  · subst state
    exact tmFiber7State8_in_close
  · subst state
    exact tmFiber7State9_in_close
  · subst state
    exact tmFiber7State10_in_close
  · subst state
    exact tmFiber7State11_in_close
  · subst state
    exact tmFiber7State12_in_close
  · subst state
    exact tmFiber7State13_in_close
  · subst state
    exact tmFiber7State14_in_close
  · subst state
    exact tmFiber7State15_in_close
  · cases h

end GoertzelLemma818LengthTwoTMShape16Bridge

end Mettapedia.GraphTheory.FourColor
