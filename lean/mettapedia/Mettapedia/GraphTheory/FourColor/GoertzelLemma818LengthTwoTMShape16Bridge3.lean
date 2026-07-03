import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for size-16 `normal,mirror` length-two fibers, group 3

This module proves direct connectedness for four generated `normal,mirror`
size-16 fibers from row-local reverse certificate chunks, keeping Lean on
default recursion limits.
-/

namespace GoertzelLemma818LengthTwoTMShape16Bridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818TauMirrorCertificate
open GoertzelLemma818TauMirrorReverseAudit

def tmFiber42StateAt (i : Nat) : List TauState :=
  directStates (tmFiber42RowAt i).sourceLeft (tmFiber42RowAt i).sourceRight

def tmFiber42DirectStates : List (List TauState) :=
  [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14, tmFiber42StateAt 15]

theorem tmFiber42ReverseRow_1_ok :
    tmRowReverseValid tmFiber42Key tmFiber42Expected (tmFiber42RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber42Chunk0_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber42Chunk0] at h
  exact h.2

theorem tmFiber42ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber42StateAt 0) (tmFiber42StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber42StateAt 0) (tmFiber42StateAt 1)
    (tmFiber42RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber42Key tmFiber42Expected
        (tmFiber42RowAt 1) (by decide) tmFiber42ReverseRow_1_ok
      simpa [tmFiber42StateAt, tmFiber42RowAt, tmFiber42Rows, listGetD, directRow] using h)

theorem tmFiber42ReverseRow_2_ok :
    tmRowReverseValid tmFiber42Key tmFiber42Expected (tmFiber42RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber42Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber42Chunk1] at h
  exact h.1

theorem tmFiber42ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber42StateAt 0) (tmFiber42StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber42StateAt 0) (tmFiber42StateAt 2)
    (tmFiber42RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber42Key tmFiber42Expected
        (tmFiber42RowAt 2) (by decide) tmFiber42ReverseRow_2_ok
      simpa [tmFiber42StateAt, tmFiber42RowAt, tmFiber42Rows, listGetD, directRow] using h)

theorem tmFiber42ReverseRow_3_ok :
    tmRowReverseValid tmFiber42Key tmFiber42Expected (tmFiber42RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber42Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber42Chunk1] at h
  exact h.2

theorem tmFiber42ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber42StateAt 1) (tmFiber42StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber42StateAt 1) (tmFiber42StateAt 3)
    (tmFiber42RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber42Key tmFiber42Expected
        (tmFiber42RowAt 3) (by decide) tmFiber42ReverseRow_3_ok
      simpa [tmFiber42StateAt, tmFiber42RowAt, tmFiber42Rows, listGetD, directRow] using h)

theorem tmFiber42ReverseRow_4_ok :
    tmRowReverseValid tmFiber42Key tmFiber42Expected (tmFiber42RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber42Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber42Chunk2] at h
  exact h.1

theorem tmFiber42ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber42StateAt 0) (tmFiber42StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber42StateAt 0) (tmFiber42StateAt 4)
    (tmFiber42RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber42Key tmFiber42Expected
        (tmFiber42RowAt 4) (by decide) tmFiber42ReverseRow_4_ok
      simpa [tmFiber42StateAt, tmFiber42RowAt, tmFiber42Rows, listGetD, directRow] using h)

theorem tmFiber42ReverseRow_5_ok :
    tmRowReverseValid tmFiber42Key tmFiber42Expected (tmFiber42RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber42Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber42Chunk2] at h
  exact h.2

theorem tmFiber42ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber42StateAt 1) (tmFiber42StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber42StateAt 1) (tmFiber42StateAt 5)
    (tmFiber42RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber42Key tmFiber42Expected
        (tmFiber42RowAt 5) (by decide) tmFiber42ReverseRow_5_ok
      simpa [tmFiber42StateAt, tmFiber42RowAt, tmFiber42Rows, listGetD, directRow] using h)

theorem tmFiber42ReverseRow_6_ok :
    tmRowReverseValid tmFiber42Key tmFiber42Expected (tmFiber42RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber42Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber42Chunk3] at h
  exact h.1

theorem tmFiber42ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber42StateAt 2) (tmFiber42StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber42StateAt 2) (tmFiber42StateAt 6)
    (tmFiber42RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber42Key tmFiber42Expected
        (tmFiber42RowAt 6) (by decide) tmFiber42ReverseRow_6_ok
      simpa [tmFiber42StateAt, tmFiber42RowAt, tmFiber42Rows, listGetD, directRow] using h)

theorem tmFiber42ReverseRow_7_ok :
    tmRowReverseValid tmFiber42Key tmFiber42Expected (tmFiber42RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber42Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber42Chunk3] at h
  exact h.2

theorem tmFiber42ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber42StateAt 3) (tmFiber42StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber42StateAt 3) (tmFiber42StateAt 7)
    (tmFiber42RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber42Key tmFiber42Expected
        (tmFiber42RowAt 7) (by decide) tmFiber42ReverseRow_7_ok
      simpa [tmFiber42StateAt, tmFiber42RowAt, tmFiber42Rows, listGetD, directRow] using h)

theorem tmFiber42ReverseRow_8_ok :
    tmRowReverseValid tmFiber42Key tmFiber42Expected (tmFiber42RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber42Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber42Chunk4] at h
  exact h.1

theorem tmFiber42ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber42StateAt 0) (tmFiber42StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber42StateAt 0) (tmFiber42StateAt 8)
    (tmFiber42RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber42Key tmFiber42Expected
        (tmFiber42RowAt 8) (by decide) tmFiber42ReverseRow_8_ok
      simpa [tmFiber42StateAt, tmFiber42RowAt, tmFiber42Rows, listGetD, directRow] using h)

theorem tmFiber42ReverseRow_9_ok :
    tmRowReverseValid tmFiber42Key tmFiber42Expected (tmFiber42RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber42Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber42Chunk4] at h
  exact h.2

theorem tmFiber42ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber42StateAt 1) (tmFiber42StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber42StateAt 1) (tmFiber42StateAt 9)
    (tmFiber42RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber42Key tmFiber42Expected
        (tmFiber42RowAt 9) (by decide) tmFiber42ReverseRow_9_ok
      simpa [tmFiber42StateAt, tmFiber42RowAt, tmFiber42Rows, listGetD, directRow] using h)

theorem tmFiber42ReverseRow_10_ok :
    tmRowReverseValid tmFiber42Key tmFiber42Expected (tmFiber42RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber42Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber42Chunk5] at h
  exact h.1

theorem tmFiber42ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber42StateAt 2) (tmFiber42StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber42StateAt 2) (tmFiber42StateAt 10)
    (tmFiber42RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber42Key tmFiber42Expected
        (tmFiber42RowAt 10) (by decide) tmFiber42ReverseRow_10_ok
      simpa [tmFiber42StateAt, tmFiber42RowAt, tmFiber42Rows, listGetD, directRow] using h)

theorem tmFiber42ReverseRow_11_ok :
    tmRowReverseValid tmFiber42Key tmFiber42Expected (tmFiber42RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber42Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber42Chunk5] at h
  exact h.2

theorem tmFiber42ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber42StateAt 3) (tmFiber42StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber42StateAt 3) (tmFiber42StateAt 11)
    (tmFiber42RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber42Key tmFiber42Expected
        (tmFiber42RowAt 11) (by decide) tmFiber42ReverseRow_11_ok
      simpa [tmFiber42StateAt, tmFiber42RowAt, tmFiber42Rows, listGetD, directRow] using h)

theorem tmFiber42ReverseRow_12_ok :
    tmRowReverseValid tmFiber42Key tmFiber42Expected (tmFiber42RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber42Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber42Chunk6] at h
  exact h.1

theorem tmFiber42ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber42StateAt 4) (tmFiber42StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber42StateAt 4) (tmFiber42StateAt 12)
    (tmFiber42RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber42Key tmFiber42Expected
        (tmFiber42RowAt 12) (by decide) tmFiber42ReverseRow_12_ok
      simpa [tmFiber42StateAt, tmFiber42RowAt, tmFiber42Rows, listGetD, directRow] using h)

theorem tmFiber42ReverseRow_13_ok :
    tmRowReverseValid tmFiber42Key tmFiber42Expected (tmFiber42RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber42Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber42Chunk6] at h
  exact h.2

theorem tmFiber42ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber42StateAt 5) (tmFiber42StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber42StateAt 5) (tmFiber42StateAt 13)
    (tmFiber42RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber42Key tmFiber42Expected
        (tmFiber42RowAt 13) (by decide) tmFiber42ReverseRow_13_ok
      simpa [tmFiber42StateAt, tmFiber42RowAt, tmFiber42Rows, listGetD, directRow] using h)

theorem tmFiber42ReverseRow_14_ok :
    tmRowReverseValid tmFiber42Key tmFiber42Expected (tmFiber42RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber42Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber42Chunk7] at h
  exact h.1

theorem tmFiber42ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber42StateAt 6) (tmFiber42StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber42StateAt 6) (tmFiber42StateAt 14)
    (tmFiber42RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber42Key tmFiber42Expected
        (tmFiber42RowAt 14) (by decide) tmFiber42ReverseRow_14_ok
      simpa [tmFiber42StateAt, tmFiber42RowAt, tmFiber42Rows, listGetD, directRow] using h)

theorem tmFiber42ReverseRow_15_ok :
    tmRowReverseValid tmFiber42Key tmFiber42Expected (tmFiber42RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber42Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber42Chunk7] at h
  exact h.2

theorem tmFiber42ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber42StateAt 7) (tmFiber42StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber42StateAt 7) (tmFiber42StateAt 15)
    (tmFiber42RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber42Key tmFiber42Expected
        (tmFiber42RowAt 15) (by decide) tmFiber42ReverseRow_15_ok
      simpa [tmFiber42StateAt, tmFiber42RowAt, tmFiber42Rows, listGetD, directRow] using h)

theorem tmFiber42State0_in_pass1_prefix :
    tmFiber42StateAt 0 ∈ chainClosureStep tmWord [tmFiber42StateAt 0] [tmFiber42StateAt 0] := by
  exact chainClosureStep_mem_of_seen tmWord [tmFiber42StateAt 0] [tmFiber42StateAt 0] (tmFiber42StateAt 0) (by simp)

theorem tmFiber42State1_in_pass1_prefix :
    tmFiber42StateAt 1 ∈ chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1] [tmFiber42StateAt 0] := by
  have hparentBefore :
      tmFiber42StateAt 0 ∈ chainClosureStep tmWord [tmFiber42StateAt 0] [tmFiber42StateAt 0] := by
    exact tmFiber42State0_in_pass1_prefix
  rw [show [tmFiber42StateAt 0, tmFiber42StateAt 1] = [tmFiber42StateAt 0] ++ [tmFiber42StateAt 1] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber42StateAt 1) []
    (chainClosureStep tmWord [tmFiber42StateAt 0] [tmFiber42StateAt 0]) (tmFiber42StateAt 0)
    hparentBefore tmFiber42ReverseSingleStep1

theorem tmFiber42State2_in_pass1_prefix :
    tmFiber42StateAt 2 ∈ chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2] [tmFiber42StateAt 0] := by
  have hparentBefore :
      tmFiber42StateAt 0 ∈ chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1] [tmFiber42StateAt 0] := by
    rw [show [tmFiber42StateAt 0, tmFiber42StateAt 1] = [tmFiber42StateAt 0] ++ [tmFiber42StateAt 1] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber42StateAt 1]
      (chainClosureStep tmWord [tmFiber42StateAt 0] [tmFiber42StateAt 0]) (tmFiber42StateAt 0)
      tmFiber42State0_in_pass1_prefix
  rw [show [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2] = [tmFiber42StateAt 0, tmFiber42StateAt 1] ++ [tmFiber42StateAt 2] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber42StateAt 2) []
    (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1] [tmFiber42StateAt 0]) (tmFiber42StateAt 0)
    hparentBefore tmFiber42ReverseSingleStep2

theorem tmFiber42State3_in_pass1_prefix :
    tmFiber42StateAt 3 ∈ chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3] [tmFiber42StateAt 0] := by
  have hparentBefore :
      tmFiber42StateAt 1 ∈ chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2] [tmFiber42StateAt 0] := by
    rw [show [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2] = [tmFiber42StateAt 0, tmFiber42StateAt 1] ++ [tmFiber42StateAt 2] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber42StateAt 2]
      (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1] [tmFiber42StateAt 0]) (tmFiber42StateAt 1)
      tmFiber42State1_in_pass1_prefix
  rw [show [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3] = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2] ++ [tmFiber42StateAt 3] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber42StateAt 3) []
    (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2] [tmFiber42StateAt 0]) (tmFiber42StateAt 1)
    hparentBefore tmFiber42ReverseSingleStep3

theorem tmFiber42State4_in_pass1_prefix :
    tmFiber42StateAt 4 ∈ chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4] [tmFiber42StateAt 0] := by
  have hparentBefore :
      tmFiber42StateAt 0 ∈ chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3] [tmFiber42StateAt 0] := by
    rw [show [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3] = [tmFiber42StateAt 0] ++ [tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3]
      (chainClosureStep tmWord [tmFiber42StateAt 0] [tmFiber42StateAt 0]) (tmFiber42StateAt 0)
      tmFiber42State0_in_pass1_prefix
  rw [show [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4] = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3] ++ [tmFiber42StateAt 4] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber42StateAt 4) []
    (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3] [tmFiber42StateAt 0]) (tmFiber42StateAt 0)
    hparentBefore tmFiber42ReverseSingleStep4

theorem tmFiber42State5_in_pass1_prefix :
    tmFiber42StateAt 5 ∈ chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5] [tmFiber42StateAt 0] := by
  have hparentBefore :
      tmFiber42StateAt 1 ∈ chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4] [tmFiber42StateAt 0] := by
    rw [show [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4] = [tmFiber42StateAt 0, tmFiber42StateAt 1] ++ [tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4]
      (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1] [tmFiber42StateAt 0]) (tmFiber42StateAt 1)
      tmFiber42State1_in_pass1_prefix
  rw [show [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5] = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4] ++ [tmFiber42StateAt 5] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber42StateAt 5) []
    (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4] [tmFiber42StateAt 0]) (tmFiber42StateAt 1)
    hparentBefore tmFiber42ReverseSingleStep5

theorem tmFiber42State6_in_pass1_prefix :
    tmFiber42StateAt 6 ∈ chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6] [tmFiber42StateAt 0] := by
  have hparentBefore :
      tmFiber42StateAt 2 ∈ chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5] [tmFiber42StateAt 0] := by
    rw [show [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5] = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2] ++ [tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5]
      (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2] [tmFiber42StateAt 0]) (tmFiber42StateAt 2)
      tmFiber42State2_in_pass1_prefix
  rw [show [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6] = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5] ++ [tmFiber42StateAt 6] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber42StateAt 6) []
    (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5] [tmFiber42StateAt 0]) (tmFiber42StateAt 2)
    hparentBefore tmFiber42ReverseSingleStep6

theorem tmFiber42State7_in_pass1_prefix :
    tmFiber42StateAt 7 ∈ chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7] [tmFiber42StateAt 0] := by
  have hparentBefore :
      tmFiber42StateAt 3 ∈ chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6] [tmFiber42StateAt 0] := by
    rw [show [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6] = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3] ++ [tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6]
      (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3] [tmFiber42StateAt 0]) (tmFiber42StateAt 3)
      tmFiber42State3_in_pass1_prefix
  rw [show [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7] = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6] ++ [tmFiber42StateAt 7] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber42StateAt 7) []
    (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6] [tmFiber42StateAt 0]) (tmFiber42StateAt 3)
    hparentBefore tmFiber42ReverseSingleStep7

theorem tmFiber42State8_in_pass1_prefix :
    tmFiber42StateAt 8 ∈ chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8] [tmFiber42StateAt 0] := by
  have hparentBefore :
      tmFiber42StateAt 0 ∈ chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7] [tmFiber42StateAt 0] := by
    rw [show [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7] = [tmFiber42StateAt 0] ++ [tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7]
      (chainClosureStep tmWord [tmFiber42StateAt 0] [tmFiber42StateAt 0]) (tmFiber42StateAt 0)
      tmFiber42State0_in_pass1_prefix
  rw [show [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8] = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7] ++ [tmFiber42StateAt 8] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber42StateAt 8) []
    (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7] [tmFiber42StateAt 0]) (tmFiber42StateAt 0)
    hparentBefore tmFiber42ReverseSingleStep8

theorem tmFiber42State9_in_pass1_prefix :
    tmFiber42StateAt 9 ∈ chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9] [tmFiber42StateAt 0] := by
  have hparentBefore :
      tmFiber42StateAt 1 ∈ chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8] [tmFiber42StateAt 0] := by
    rw [show [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8] = [tmFiber42StateAt 0, tmFiber42StateAt 1] ++ [tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8]
      (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1] [tmFiber42StateAt 0]) (tmFiber42StateAt 1)
      tmFiber42State1_in_pass1_prefix
  rw [show [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9] = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8] ++ [tmFiber42StateAt 9] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber42StateAt 9) []
    (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8] [tmFiber42StateAt 0]) (tmFiber42StateAt 1)
    hparentBefore tmFiber42ReverseSingleStep9

theorem tmFiber42State10_in_pass1_prefix :
    tmFiber42StateAt 10 ∈ chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10] [tmFiber42StateAt 0] := by
  have hparentBefore :
      tmFiber42StateAt 2 ∈ chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9] [tmFiber42StateAt 0] := by
    rw [show [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9] = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2] ++ [tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9]
      (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2] [tmFiber42StateAt 0]) (tmFiber42StateAt 2)
      tmFiber42State2_in_pass1_prefix
  rw [show [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10] = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9] ++ [tmFiber42StateAt 10] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber42StateAt 10) []
    (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9] [tmFiber42StateAt 0]) (tmFiber42StateAt 2)
    hparentBefore tmFiber42ReverseSingleStep10

theorem tmFiber42State11_in_pass1_prefix :
    tmFiber42StateAt 11 ∈ chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11] [tmFiber42StateAt 0] := by
  have hparentBefore :
      tmFiber42StateAt 3 ∈ chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10] [tmFiber42StateAt 0] := by
    rw [show [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10] = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3] ++ [tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10]
      (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3] [tmFiber42StateAt 0]) (tmFiber42StateAt 3)
      tmFiber42State3_in_pass1_prefix
  rw [show [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11] = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10] ++ [tmFiber42StateAt 11] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber42StateAt 11) []
    (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10] [tmFiber42StateAt 0]) (tmFiber42StateAt 3)
    hparentBefore tmFiber42ReverseSingleStep11

theorem tmFiber42State12_in_pass1_prefix :
    tmFiber42StateAt 12 ∈ chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12] [tmFiber42StateAt 0] := by
  have hparentBefore :
      tmFiber42StateAt 4 ∈ chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11] [tmFiber42StateAt 0] := by
    rw [show [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11] = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4] ++ [tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11]
      (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4] [tmFiber42StateAt 0]) (tmFiber42StateAt 4)
      tmFiber42State4_in_pass1_prefix
  rw [show [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12] = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11] ++ [tmFiber42StateAt 12] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber42StateAt 12) []
    (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11] [tmFiber42StateAt 0]) (tmFiber42StateAt 4)
    hparentBefore tmFiber42ReverseSingleStep12

theorem tmFiber42State13_in_pass1_prefix :
    tmFiber42StateAt 13 ∈ chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13] [tmFiber42StateAt 0] := by
  have hparentBefore :
      tmFiber42StateAt 5 ∈ chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12] [tmFiber42StateAt 0] := by
    rw [show [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12] = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5] ++ [tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12]
      (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5] [tmFiber42StateAt 0]) (tmFiber42StateAt 5)
      tmFiber42State5_in_pass1_prefix
  rw [show [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13] = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12] ++ [tmFiber42StateAt 13] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber42StateAt 13) []
    (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12] [tmFiber42StateAt 0]) (tmFiber42StateAt 5)
    hparentBefore tmFiber42ReverseSingleStep13

theorem tmFiber42State14_in_pass1_prefix :
    tmFiber42StateAt 14 ∈ chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14] [tmFiber42StateAt 0] := by
  have hparentBefore :
      tmFiber42StateAt 6 ∈ chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13] [tmFiber42StateAt 0] := by
    rw [show [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13] = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6] ++ [tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13]
      (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6] [tmFiber42StateAt 0]) (tmFiber42StateAt 6)
      tmFiber42State6_in_pass1_prefix
  rw [show [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14] = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13] ++ [tmFiber42StateAt 14] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber42StateAt 14) []
    (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13] [tmFiber42StateAt 0]) (tmFiber42StateAt 6)
    hparentBefore tmFiber42ReverseSingleStep14

theorem tmFiber42State15_in_pass1_prefix :
    tmFiber42StateAt 15 ∈ chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14, tmFiber42StateAt 15] [tmFiber42StateAt 0] := by
  have hparentBefore :
      tmFiber42StateAt 7 ∈ chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14] [tmFiber42StateAt 0] := by
    rw [show [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14] = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7] ++ [tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14]
      (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7] [tmFiber42StateAt 0]) (tmFiber42StateAt 7)
      tmFiber42State7_in_pass1_prefix
  rw [show [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14, tmFiber42StateAt 15] = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14] ++ [tmFiber42StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber42StateAt 15) []
    (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14] [tmFiber42StateAt 0]) (tmFiber42StateAt 7)
    hparentBefore tmFiber42ReverseSingleStep15

theorem tmFiber42State0_in_pass1_full :
    tmFiber42StateAt 0 ∈ chainClosureStep tmWord tmFiber42DirectStates [tmFiber42StateAt 0] := by
  rw [show tmFiber42DirectStates = [tmFiber42StateAt 0] ++ [tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14, tmFiber42StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14, tmFiber42StateAt 15]
    (chainClosureStep tmWord [tmFiber42StateAt 0] [tmFiber42StateAt 0]) (tmFiber42StateAt 0)
    tmFiber42State0_in_pass1_prefix

theorem tmFiber42State1_in_pass1_full :
    tmFiber42StateAt 1 ∈ chainClosureStep tmWord tmFiber42DirectStates [tmFiber42StateAt 0] := by
  rw [show tmFiber42DirectStates = [tmFiber42StateAt 0, tmFiber42StateAt 1] ++ [tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14, tmFiber42StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14, tmFiber42StateAt 15]
    (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1] [tmFiber42StateAt 0]) (tmFiber42StateAt 1)
    tmFiber42State1_in_pass1_prefix

theorem tmFiber42State2_in_pass1_full :
    tmFiber42StateAt 2 ∈ chainClosureStep tmWord tmFiber42DirectStates [tmFiber42StateAt 0] := by
  rw [show tmFiber42DirectStates = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2] ++ [tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14, tmFiber42StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14, tmFiber42StateAt 15]
    (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2] [tmFiber42StateAt 0]) (tmFiber42StateAt 2)
    tmFiber42State2_in_pass1_prefix

theorem tmFiber42State3_in_pass1_full :
    tmFiber42StateAt 3 ∈ chainClosureStep tmWord tmFiber42DirectStates [tmFiber42StateAt 0] := by
  rw [show tmFiber42DirectStates = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3] ++ [tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14, tmFiber42StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14, tmFiber42StateAt 15]
    (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3] [tmFiber42StateAt 0]) (tmFiber42StateAt 3)
    tmFiber42State3_in_pass1_prefix

theorem tmFiber42State4_in_pass1_full :
    tmFiber42StateAt 4 ∈ chainClosureStep tmWord tmFiber42DirectStates [tmFiber42StateAt 0] := by
  rw [show tmFiber42DirectStates = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4] ++ [tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14, tmFiber42StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14, tmFiber42StateAt 15]
    (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4] [tmFiber42StateAt 0]) (tmFiber42StateAt 4)
    tmFiber42State4_in_pass1_prefix

theorem tmFiber42State5_in_pass1_full :
    tmFiber42StateAt 5 ∈ chainClosureStep tmWord tmFiber42DirectStates [tmFiber42StateAt 0] := by
  rw [show tmFiber42DirectStates = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5] ++ [tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14, tmFiber42StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14, tmFiber42StateAt 15]
    (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5] [tmFiber42StateAt 0]) (tmFiber42StateAt 5)
    tmFiber42State5_in_pass1_prefix

theorem tmFiber42State6_in_pass1_full :
    tmFiber42StateAt 6 ∈ chainClosureStep tmWord tmFiber42DirectStates [tmFiber42StateAt 0] := by
  rw [show tmFiber42DirectStates = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6] ++ [tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14, tmFiber42StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14, tmFiber42StateAt 15]
    (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6] [tmFiber42StateAt 0]) (tmFiber42StateAt 6)
    tmFiber42State6_in_pass1_prefix

theorem tmFiber42State7_in_pass1_full :
    tmFiber42StateAt 7 ∈ chainClosureStep tmWord tmFiber42DirectStates [tmFiber42StateAt 0] := by
  rw [show tmFiber42DirectStates = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7] ++ [tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14, tmFiber42StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14, tmFiber42StateAt 15]
    (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7] [tmFiber42StateAt 0]) (tmFiber42StateAt 7)
    tmFiber42State7_in_pass1_prefix

theorem tmFiber42State8_in_pass1_full :
    tmFiber42StateAt 8 ∈ chainClosureStep tmWord tmFiber42DirectStates [tmFiber42StateAt 0] := by
  rw [show tmFiber42DirectStates = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8] ++ [tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14, tmFiber42StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14, tmFiber42StateAt 15]
    (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8] [tmFiber42StateAt 0]) (tmFiber42StateAt 8)
    tmFiber42State8_in_pass1_prefix

theorem tmFiber42State9_in_pass1_full :
    tmFiber42StateAt 9 ∈ chainClosureStep tmWord tmFiber42DirectStates [tmFiber42StateAt 0] := by
  rw [show tmFiber42DirectStates = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9] ++ [tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14, tmFiber42StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14, tmFiber42StateAt 15]
    (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9] [tmFiber42StateAt 0]) (tmFiber42StateAt 9)
    tmFiber42State9_in_pass1_prefix

theorem tmFiber42State10_in_pass1_full :
    tmFiber42StateAt 10 ∈ chainClosureStep tmWord tmFiber42DirectStates [tmFiber42StateAt 0] := by
  rw [show tmFiber42DirectStates = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10] ++ [tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14, tmFiber42StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14, tmFiber42StateAt 15]
    (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10] [tmFiber42StateAt 0]) (tmFiber42StateAt 10)
    tmFiber42State10_in_pass1_prefix

theorem tmFiber42State11_in_pass1_full :
    tmFiber42StateAt 11 ∈ chainClosureStep tmWord tmFiber42DirectStates [tmFiber42StateAt 0] := by
  rw [show tmFiber42DirectStates = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11] ++ [tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14, tmFiber42StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14, tmFiber42StateAt 15]
    (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11] [tmFiber42StateAt 0]) (tmFiber42StateAt 11)
    tmFiber42State11_in_pass1_prefix

theorem tmFiber42State12_in_pass1_full :
    tmFiber42StateAt 12 ∈ chainClosureStep tmWord tmFiber42DirectStates [tmFiber42StateAt 0] := by
  rw [show tmFiber42DirectStates = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12] ++ [tmFiber42StateAt 13, tmFiber42StateAt 14, tmFiber42StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber42StateAt 13, tmFiber42StateAt 14, tmFiber42StateAt 15]
    (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12] [tmFiber42StateAt 0]) (tmFiber42StateAt 12)
    tmFiber42State12_in_pass1_prefix

theorem tmFiber42State13_in_pass1_full :
    tmFiber42StateAt 13 ∈ chainClosureStep tmWord tmFiber42DirectStates [tmFiber42StateAt 0] := by
  rw [show tmFiber42DirectStates = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13] ++ [tmFiber42StateAt 14, tmFiber42StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber42StateAt 14, tmFiber42StateAt 15]
    (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13] [tmFiber42StateAt 0]) (tmFiber42StateAt 13)
    tmFiber42State13_in_pass1_prefix

theorem tmFiber42State14_in_pass1_full :
    tmFiber42StateAt 14 ∈ chainClosureStep tmWord tmFiber42DirectStates [tmFiber42StateAt 0] := by
  rw [show tmFiber42DirectStates = [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14] ++ [tmFiber42StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber42StateAt 15]
    (chainClosureStep tmWord [tmFiber42StateAt 0, tmFiber42StateAt 1, tmFiber42StateAt 2, tmFiber42StateAt 3, tmFiber42StateAt 4, tmFiber42StateAt 5, tmFiber42StateAt 6, tmFiber42StateAt 7, tmFiber42StateAt 8, tmFiber42StateAt 9, tmFiber42StateAt 10, tmFiber42StateAt 11, tmFiber42StateAt 12, tmFiber42StateAt 13, tmFiber42StateAt 14] [tmFiber42StateAt 0]) (tmFiber42StateAt 14)
    tmFiber42State14_in_pass1_prefix

theorem tmFiber42State15_in_pass1_full :
    tmFiber42StateAt 15 ∈ chainClosureStep tmWord tmFiber42DirectStates [tmFiber42StateAt 0] := by
  simpa [tmFiber42DirectStates] using tmFiber42State15_in_pass1_prefix

theorem tmFiber42State0_in_close :
    tmFiber42StateAt 0 ∈ closeChainFiber tmWord tmFiber42DirectStates tmFiber42DirectStates.length [tmFiber42StateAt 0] := by
  change tmFiber42StateAt 0 ∈ closeChainFiber tmWord tmFiber42DirectStates (15 + 1) [tmFiber42StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber42DirectStates 15 [tmFiber42StateAt 0] (tmFiber42StateAt 0) tmFiber42State0_in_pass1_full

theorem tmFiber42State1_in_close :
    tmFiber42StateAt 1 ∈ closeChainFiber tmWord tmFiber42DirectStates tmFiber42DirectStates.length [tmFiber42StateAt 0] := by
  change tmFiber42StateAt 1 ∈ closeChainFiber tmWord tmFiber42DirectStates (15 + 1) [tmFiber42StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber42DirectStates 15 [tmFiber42StateAt 0] (tmFiber42StateAt 1) tmFiber42State1_in_pass1_full

theorem tmFiber42State2_in_close :
    tmFiber42StateAt 2 ∈ closeChainFiber tmWord tmFiber42DirectStates tmFiber42DirectStates.length [tmFiber42StateAt 0] := by
  change tmFiber42StateAt 2 ∈ closeChainFiber tmWord tmFiber42DirectStates (15 + 1) [tmFiber42StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber42DirectStates 15 [tmFiber42StateAt 0] (tmFiber42StateAt 2) tmFiber42State2_in_pass1_full

theorem tmFiber42State3_in_close :
    tmFiber42StateAt 3 ∈ closeChainFiber tmWord tmFiber42DirectStates tmFiber42DirectStates.length [tmFiber42StateAt 0] := by
  change tmFiber42StateAt 3 ∈ closeChainFiber tmWord tmFiber42DirectStates (15 + 1) [tmFiber42StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber42DirectStates 15 [tmFiber42StateAt 0] (tmFiber42StateAt 3) tmFiber42State3_in_pass1_full

theorem tmFiber42State4_in_close :
    tmFiber42StateAt 4 ∈ closeChainFiber tmWord tmFiber42DirectStates tmFiber42DirectStates.length [tmFiber42StateAt 0] := by
  change tmFiber42StateAt 4 ∈ closeChainFiber tmWord tmFiber42DirectStates (15 + 1) [tmFiber42StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber42DirectStates 15 [tmFiber42StateAt 0] (tmFiber42StateAt 4) tmFiber42State4_in_pass1_full

theorem tmFiber42State5_in_close :
    tmFiber42StateAt 5 ∈ closeChainFiber tmWord tmFiber42DirectStates tmFiber42DirectStates.length [tmFiber42StateAt 0] := by
  change tmFiber42StateAt 5 ∈ closeChainFiber tmWord tmFiber42DirectStates (15 + 1) [tmFiber42StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber42DirectStates 15 [tmFiber42StateAt 0] (tmFiber42StateAt 5) tmFiber42State5_in_pass1_full

theorem tmFiber42State6_in_close :
    tmFiber42StateAt 6 ∈ closeChainFiber tmWord tmFiber42DirectStates tmFiber42DirectStates.length [tmFiber42StateAt 0] := by
  change tmFiber42StateAt 6 ∈ closeChainFiber tmWord tmFiber42DirectStates (15 + 1) [tmFiber42StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber42DirectStates 15 [tmFiber42StateAt 0] (tmFiber42StateAt 6) tmFiber42State6_in_pass1_full

theorem tmFiber42State7_in_close :
    tmFiber42StateAt 7 ∈ closeChainFiber tmWord tmFiber42DirectStates tmFiber42DirectStates.length [tmFiber42StateAt 0] := by
  change tmFiber42StateAt 7 ∈ closeChainFiber tmWord tmFiber42DirectStates (15 + 1) [tmFiber42StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber42DirectStates 15 [tmFiber42StateAt 0] (tmFiber42StateAt 7) tmFiber42State7_in_pass1_full

theorem tmFiber42State8_in_close :
    tmFiber42StateAt 8 ∈ closeChainFiber tmWord tmFiber42DirectStates tmFiber42DirectStates.length [tmFiber42StateAt 0] := by
  change tmFiber42StateAt 8 ∈ closeChainFiber tmWord tmFiber42DirectStates (15 + 1) [tmFiber42StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber42DirectStates 15 [tmFiber42StateAt 0] (tmFiber42StateAt 8) tmFiber42State8_in_pass1_full

theorem tmFiber42State9_in_close :
    tmFiber42StateAt 9 ∈ closeChainFiber tmWord tmFiber42DirectStates tmFiber42DirectStates.length [tmFiber42StateAt 0] := by
  change tmFiber42StateAt 9 ∈ closeChainFiber tmWord tmFiber42DirectStates (15 + 1) [tmFiber42StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber42DirectStates 15 [tmFiber42StateAt 0] (tmFiber42StateAt 9) tmFiber42State9_in_pass1_full

theorem tmFiber42State10_in_close :
    tmFiber42StateAt 10 ∈ closeChainFiber tmWord tmFiber42DirectStates tmFiber42DirectStates.length [tmFiber42StateAt 0] := by
  change tmFiber42StateAt 10 ∈ closeChainFiber tmWord tmFiber42DirectStates (15 + 1) [tmFiber42StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber42DirectStates 15 [tmFiber42StateAt 0] (tmFiber42StateAt 10) tmFiber42State10_in_pass1_full

theorem tmFiber42State11_in_close :
    tmFiber42StateAt 11 ∈ closeChainFiber tmWord tmFiber42DirectStates tmFiber42DirectStates.length [tmFiber42StateAt 0] := by
  change tmFiber42StateAt 11 ∈ closeChainFiber tmWord tmFiber42DirectStates (15 + 1) [tmFiber42StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber42DirectStates 15 [tmFiber42StateAt 0] (tmFiber42StateAt 11) tmFiber42State11_in_pass1_full

theorem tmFiber42State12_in_close :
    tmFiber42StateAt 12 ∈ closeChainFiber tmWord tmFiber42DirectStates tmFiber42DirectStates.length [tmFiber42StateAt 0] := by
  change tmFiber42StateAt 12 ∈ closeChainFiber tmWord tmFiber42DirectStates (15 + 1) [tmFiber42StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber42DirectStates 15 [tmFiber42StateAt 0] (tmFiber42StateAt 12) tmFiber42State12_in_pass1_full

theorem tmFiber42State13_in_close :
    tmFiber42StateAt 13 ∈ closeChainFiber tmWord tmFiber42DirectStates tmFiber42DirectStates.length [tmFiber42StateAt 0] := by
  change tmFiber42StateAt 13 ∈ closeChainFiber tmWord tmFiber42DirectStates (15 + 1) [tmFiber42StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber42DirectStates 15 [tmFiber42StateAt 0] (tmFiber42StateAt 13) tmFiber42State13_in_pass1_full

theorem tmFiber42State14_in_close :
    tmFiber42StateAt 14 ∈ closeChainFiber tmWord tmFiber42DirectStates tmFiber42DirectStates.length [tmFiber42StateAt 0] := by
  change tmFiber42StateAt 14 ∈ closeChainFiber tmWord tmFiber42DirectStates (15 + 1) [tmFiber42StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber42DirectStates 15 [tmFiber42StateAt 0] (tmFiber42StateAt 14) tmFiber42State14_in_pass1_full

theorem tmFiber42State15_in_close :
    tmFiber42StateAt 15 ∈ closeChainFiber tmWord tmFiber42DirectStates tmFiber42DirectStates.length [tmFiber42StateAt 0] := by
  change tmFiber42StateAt 15 ∈ closeChainFiber tmWord tmFiber42DirectStates (15 + 1) [tmFiber42StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber42DirectStates 15 [tmFiber42StateAt 0] (tmFiber42StateAt 15) tmFiber42State15_in_pass1_full

theorem tmFiber42DirectConnected :
    chainFiberConnected tmWord tmFiber42DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber42DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber42State0_in_close
  · subst state
    exact tmFiber42State1_in_close
  · subst state
    exact tmFiber42State2_in_close
  · subst state
    exact tmFiber42State3_in_close
  · subst state
    exact tmFiber42State4_in_close
  · subst state
    exact tmFiber42State5_in_close
  · subst state
    exact tmFiber42State6_in_close
  · subst state
    exact tmFiber42State7_in_close
  · subst state
    exact tmFiber42State8_in_close
  · subst state
    exact tmFiber42State9_in_close
  · subst state
    exact tmFiber42State10_in_close
  · subst state
    exact tmFiber42State11_in_close
  · subst state
    exact tmFiber42State12_in_close
  · subst state
    exact tmFiber42State13_in_close
  · subst state
    exact tmFiber42State14_in_close
  · subst state
    exact tmFiber42State15_in_close
  · cases h

def tmFiber43StateAt (i : Nat) : List TauState :=
  directStates (tmFiber43RowAt i).sourceLeft (tmFiber43RowAt i).sourceRight

def tmFiber43DirectStates : List (List TauState) :=
  [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14, tmFiber43StateAt 15]

theorem tmFiber43ReverseRow_1_ok :
    tmRowReverseValid tmFiber43Key tmFiber43Expected (tmFiber43RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber43Chunk0_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber43Chunk0] at h
  exact h.2

theorem tmFiber43ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber43StateAt 0) (tmFiber43StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber43StateAt 0) (tmFiber43StateAt 1)
    (tmFiber43RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber43Key tmFiber43Expected
        (tmFiber43RowAt 1) (by decide) tmFiber43ReverseRow_1_ok
      simpa [tmFiber43StateAt, tmFiber43RowAt, tmFiber43Rows, listGetD, directRow] using h)

theorem tmFiber43ReverseRow_2_ok :
    tmRowReverseValid tmFiber43Key tmFiber43Expected (tmFiber43RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber43Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber43Chunk1] at h
  exact h.1

theorem tmFiber43ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber43StateAt 0) (tmFiber43StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber43StateAt 0) (tmFiber43StateAt 2)
    (tmFiber43RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber43Key tmFiber43Expected
        (tmFiber43RowAt 2) (by decide) tmFiber43ReverseRow_2_ok
      simpa [tmFiber43StateAt, tmFiber43RowAt, tmFiber43Rows, listGetD, directRow] using h)

theorem tmFiber43ReverseRow_3_ok :
    tmRowReverseValid tmFiber43Key tmFiber43Expected (tmFiber43RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber43Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber43Chunk1] at h
  exact h.2

theorem tmFiber43ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber43StateAt 1) (tmFiber43StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber43StateAt 1) (tmFiber43StateAt 3)
    (tmFiber43RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber43Key tmFiber43Expected
        (tmFiber43RowAt 3) (by decide) tmFiber43ReverseRow_3_ok
      simpa [tmFiber43StateAt, tmFiber43RowAt, tmFiber43Rows, listGetD, directRow] using h)

theorem tmFiber43ReverseRow_4_ok :
    tmRowReverseValid tmFiber43Key tmFiber43Expected (tmFiber43RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber43Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber43Chunk2] at h
  exact h.1

theorem tmFiber43ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber43StateAt 0) (tmFiber43StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber43StateAt 0) (tmFiber43StateAt 4)
    (tmFiber43RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber43Key tmFiber43Expected
        (tmFiber43RowAt 4) (by decide) tmFiber43ReverseRow_4_ok
      simpa [tmFiber43StateAt, tmFiber43RowAt, tmFiber43Rows, listGetD, directRow] using h)

theorem tmFiber43ReverseRow_5_ok :
    tmRowReverseValid tmFiber43Key tmFiber43Expected (tmFiber43RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber43Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber43Chunk2] at h
  exact h.2

theorem tmFiber43ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber43StateAt 1) (tmFiber43StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber43StateAt 1) (tmFiber43StateAt 5)
    (tmFiber43RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber43Key tmFiber43Expected
        (tmFiber43RowAt 5) (by decide) tmFiber43ReverseRow_5_ok
      simpa [tmFiber43StateAt, tmFiber43RowAt, tmFiber43Rows, listGetD, directRow] using h)

theorem tmFiber43ReverseRow_6_ok :
    tmRowReverseValid tmFiber43Key tmFiber43Expected (tmFiber43RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber43Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber43Chunk3] at h
  exact h.1

theorem tmFiber43ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber43StateAt 2) (tmFiber43StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber43StateAt 2) (tmFiber43StateAt 6)
    (tmFiber43RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber43Key tmFiber43Expected
        (tmFiber43RowAt 6) (by decide) tmFiber43ReverseRow_6_ok
      simpa [tmFiber43StateAt, tmFiber43RowAt, tmFiber43Rows, listGetD, directRow] using h)

theorem tmFiber43ReverseRow_7_ok :
    tmRowReverseValid tmFiber43Key tmFiber43Expected (tmFiber43RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber43Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber43Chunk3] at h
  exact h.2

theorem tmFiber43ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber43StateAt 3) (tmFiber43StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber43StateAt 3) (tmFiber43StateAt 7)
    (tmFiber43RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber43Key tmFiber43Expected
        (tmFiber43RowAt 7) (by decide) tmFiber43ReverseRow_7_ok
      simpa [tmFiber43StateAt, tmFiber43RowAt, tmFiber43Rows, listGetD, directRow] using h)

theorem tmFiber43ReverseRow_8_ok :
    tmRowReverseValid tmFiber43Key tmFiber43Expected (tmFiber43RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber43Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber43Chunk4] at h
  exact h.1

theorem tmFiber43ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber43StateAt 4) (tmFiber43StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber43StateAt 4) (tmFiber43StateAt 8)
    (tmFiber43RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber43Key tmFiber43Expected
        (tmFiber43RowAt 8) (by decide) tmFiber43ReverseRow_8_ok
      simpa [tmFiber43StateAt, tmFiber43RowAt, tmFiber43Rows, listGetD, directRow] using h)

theorem tmFiber43ReverseRow_9_ok :
    tmRowReverseValid tmFiber43Key tmFiber43Expected (tmFiber43RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber43Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber43Chunk4] at h
  exact h.2

theorem tmFiber43ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber43StateAt 5) (tmFiber43StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber43StateAt 5) (tmFiber43StateAt 9)
    (tmFiber43RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber43Key tmFiber43Expected
        (tmFiber43RowAt 9) (by decide) tmFiber43ReverseRow_9_ok
      simpa [tmFiber43StateAt, tmFiber43RowAt, tmFiber43Rows, listGetD, directRow] using h)

theorem tmFiber43ReverseRow_10_ok :
    tmRowReverseValid tmFiber43Key tmFiber43Expected (tmFiber43RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber43Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber43Chunk5] at h
  exact h.1

theorem tmFiber43ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber43StateAt 6) (tmFiber43StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber43StateAt 6) (tmFiber43StateAt 10)
    (tmFiber43RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber43Key tmFiber43Expected
        (tmFiber43RowAt 10) (by decide) tmFiber43ReverseRow_10_ok
      simpa [tmFiber43StateAt, tmFiber43RowAt, tmFiber43Rows, listGetD, directRow] using h)

theorem tmFiber43ReverseRow_11_ok :
    tmRowReverseValid tmFiber43Key tmFiber43Expected (tmFiber43RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber43Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber43Chunk5] at h
  exact h.2

theorem tmFiber43ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber43StateAt 7) (tmFiber43StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber43StateAt 7) (tmFiber43StateAt 11)
    (tmFiber43RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber43Key tmFiber43Expected
        (tmFiber43RowAt 11) (by decide) tmFiber43ReverseRow_11_ok
      simpa [tmFiber43StateAt, tmFiber43RowAt, tmFiber43Rows, listGetD, directRow] using h)

theorem tmFiber43ReverseRow_12_ok :
    tmRowReverseValid tmFiber43Key tmFiber43Expected (tmFiber43RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber43Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber43Chunk6] at h
  exact h.1

theorem tmFiber43ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber43StateAt 0) (tmFiber43StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber43StateAt 0) (tmFiber43StateAt 12)
    (tmFiber43RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber43Key tmFiber43Expected
        (tmFiber43RowAt 12) (by decide) tmFiber43ReverseRow_12_ok
      simpa [tmFiber43StateAt, tmFiber43RowAt, tmFiber43Rows, listGetD, directRow] using h)

theorem tmFiber43ReverseRow_13_ok :
    tmRowReverseValid tmFiber43Key tmFiber43Expected (tmFiber43RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber43Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber43Chunk6] at h
  exact h.2

theorem tmFiber43ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber43StateAt 1) (tmFiber43StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber43StateAt 1) (tmFiber43StateAt 13)
    (tmFiber43RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber43Key tmFiber43Expected
        (tmFiber43RowAt 13) (by decide) tmFiber43ReverseRow_13_ok
      simpa [tmFiber43StateAt, tmFiber43RowAt, tmFiber43Rows, listGetD, directRow] using h)

theorem tmFiber43ReverseRow_14_ok :
    tmRowReverseValid tmFiber43Key tmFiber43Expected (tmFiber43RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber43Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber43Chunk7] at h
  exact h.1

theorem tmFiber43ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber43StateAt 2) (tmFiber43StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber43StateAt 2) (tmFiber43StateAt 14)
    (tmFiber43RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber43Key tmFiber43Expected
        (tmFiber43RowAt 14) (by decide) tmFiber43ReverseRow_14_ok
      simpa [tmFiber43StateAt, tmFiber43RowAt, tmFiber43Rows, listGetD, directRow] using h)

theorem tmFiber43ReverseRow_15_ok :
    tmRowReverseValid tmFiber43Key tmFiber43Expected (tmFiber43RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber43Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber43Chunk7] at h
  exact h.2

theorem tmFiber43ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber43StateAt 3) (tmFiber43StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber43StateAt 3) (tmFiber43StateAt 15)
    (tmFiber43RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber43Key tmFiber43Expected
        (tmFiber43RowAt 15) (by decide) tmFiber43ReverseRow_15_ok
      simpa [tmFiber43StateAt, tmFiber43RowAt, tmFiber43Rows, listGetD, directRow] using h)

theorem tmFiber43State0_in_pass1_prefix :
    tmFiber43StateAt 0 ∈ chainClosureStep tmWord [tmFiber43StateAt 0] [tmFiber43StateAt 0] := by
  exact chainClosureStep_mem_of_seen tmWord [tmFiber43StateAt 0] [tmFiber43StateAt 0] (tmFiber43StateAt 0) (by simp)

theorem tmFiber43State1_in_pass1_prefix :
    tmFiber43StateAt 1 ∈ chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1] [tmFiber43StateAt 0] := by
  have hparentBefore :
      tmFiber43StateAt 0 ∈ chainClosureStep tmWord [tmFiber43StateAt 0] [tmFiber43StateAt 0] := by
    exact tmFiber43State0_in_pass1_prefix
  rw [show [tmFiber43StateAt 0, tmFiber43StateAt 1] = [tmFiber43StateAt 0] ++ [tmFiber43StateAt 1] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber43StateAt 1) []
    (chainClosureStep tmWord [tmFiber43StateAt 0] [tmFiber43StateAt 0]) (tmFiber43StateAt 0)
    hparentBefore tmFiber43ReverseSingleStep1

theorem tmFiber43State2_in_pass1_prefix :
    tmFiber43StateAt 2 ∈ chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2] [tmFiber43StateAt 0] := by
  have hparentBefore :
      tmFiber43StateAt 0 ∈ chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1] [tmFiber43StateAt 0] := by
    rw [show [tmFiber43StateAt 0, tmFiber43StateAt 1] = [tmFiber43StateAt 0] ++ [tmFiber43StateAt 1] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber43StateAt 1]
      (chainClosureStep tmWord [tmFiber43StateAt 0] [tmFiber43StateAt 0]) (tmFiber43StateAt 0)
      tmFiber43State0_in_pass1_prefix
  rw [show [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2] = [tmFiber43StateAt 0, tmFiber43StateAt 1] ++ [tmFiber43StateAt 2] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber43StateAt 2) []
    (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1] [tmFiber43StateAt 0]) (tmFiber43StateAt 0)
    hparentBefore tmFiber43ReverseSingleStep2

theorem tmFiber43State3_in_pass1_prefix :
    tmFiber43StateAt 3 ∈ chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3] [tmFiber43StateAt 0] := by
  have hparentBefore :
      tmFiber43StateAt 1 ∈ chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2] [tmFiber43StateAt 0] := by
    rw [show [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2] = [tmFiber43StateAt 0, tmFiber43StateAt 1] ++ [tmFiber43StateAt 2] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber43StateAt 2]
      (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1] [tmFiber43StateAt 0]) (tmFiber43StateAt 1)
      tmFiber43State1_in_pass1_prefix
  rw [show [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3] = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2] ++ [tmFiber43StateAt 3] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber43StateAt 3) []
    (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2] [tmFiber43StateAt 0]) (tmFiber43StateAt 1)
    hparentBefore tmFiber43ReverseSingleStep3

theorem tmFiber43State4_in_pass1_prefix :
    tmFiber43StateAt 4 ∈ chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4] [tmFiber43StateAt 0] := by
  have hparentBefore :
      tmFiber43StateAt 0 ∈ chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3] [tmFiber43StateAt 0] := by
    rw [show [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3] = [tmFiber43StateAt 0] ++ [tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3]
      (chainClosureStep tmWord [tmFiber43StateAt 0] [tmFiber43StateAt 0]) (tmFiber43StateAt 0)
      tmFiber43State0_in_pass1_prefix
  rw [show [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4] = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3] ++ [tmFiber43StateAt 4] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber43StateAt 4) []
    (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3] [tmFiber43StateAt 0]) (tmFiber43StateAt 0)
    hparentBefore tmFiber43ReverseSingleStep4

theorem tmFiber43State5_in_pass1_prefix :
    tmFiber43StateAt 5 ∈ chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5] [tmFiber43StateAt 0] := by
  have hparentBefore :
      tmFiber43StateAt 1 ∈ chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4] [tmFiber43StateAt 0] := by
    rw [show [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4] = [tmFiber43StateAt 0, tmFiber43StateAt 1] ++ [tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4]
      (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1] [tmFiber43StateAt 0]) (tmFiber43StateAt 1)
      tmFiber43State1_in_pass1_prefix
  rw [show [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5] = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4] ++ [tmFiber43StateAt 5] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber43StateAt 5) []
    (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4] [tmFiber43StateAt 0]) (tmFiber43StateAt 1)
    hparentBefore tmFiber43ReverseSingleStep5

theorem tmFiber43State6_in_pass1_prefix :
    tmFiber43StateAt 6 ∈ chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6] [tmFiber43StateAt 0] := by
  have hparentBefore :
      tmFiber43StateAt 2 ∈ chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5] [tmFiber43StateAt 0] := by
    rw [show [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5] = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2] ++ [tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5]
      (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2] [tmFiber43StateAt 0]) (tmFiber43StateAt 2)
      tmFiber43State2_in_pass1_prefix
  rw [show [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6] = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5] ++ [tmFiber43StateAt 6] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber43StateAt 6) []
    (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5] [tmFiber43StateAt 0]) (tmFiber43StateAt 2)
    hparentBefore tmFiber43ReverseSingleStep6

theorem tmFiber43State7_in_pass1_prefix :
    tmFiber43StateAt 7 ∈ chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7] [tmFiber43StateAt 0] := by
  have hparentBefore :
      tmFiber43StateAt 3 ∈ chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6] [tmFiber43StateAt 0] := by
    rw [show [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6] = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3] ++ [tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6]
      (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3] [tmFiber43StateAt 0]) (tmFiber43StateAt 3)
      tmFiber43State3_in_pass1_prefix
  rw [show [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7] = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6] ++ [tmFiber43StateAt 7] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber43StateAt 7) []
    (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6] [tmFiber43StateAt 0]) (tmFiber43StateAt 3)
    hparentBefore tmFiber43ReverseSingleStep7

theorem tmFiber43State8_in_pass1_prefix :
    tmFiber43StateAt 8 ∈ chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8] [tmFiber43StateAt 0] := by
  have hparentBefore :
      tmFiber43StateAt 4 ∈ chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7] [tmFiber43StateAt 0] := by
    rw [show [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7] = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4] ++ [tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7]
      (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4] [tmFiber43StateAt 0]) (tmFiber43StateAt 4)
      tmFiber43State4_in_pass1_prefix
  rw [show [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8] = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7] ++ [tmFiber43StateAt 8] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber43StateAt 8) []
    (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7] [tmFiber43StateAt 0]) (tmFiber43StateAt 4)
    hparentBefore tmFiber43ReverseSingleStep8

theorem tmFiber43State9_in_pass1_prefix :
    tmFiber43StateAt 9 ∈ chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9] [tmFiber43StateAt 0] := by
  have hparentBefore :
      tmFiber43StateAt 5 ∈ chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8] [tmFiber43StateAt 0] := by
    rw [show [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8] = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5] ++ [tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8]
      (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5] [tmFiber43StateAt 0]) (tmFiber43StateAt 5)
      tmFiber43State5_in_pass1_prefix
  rw [show [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9] = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8] ++ [tmFiber43StateAt 9] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber43StateAt 9) []
    (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8] [tmFiber43StateAt 0]) (tmFiber43StateAt 5)
    hparentBefore tmFiber43ReverseSingleStep9

theorem tmFiber43State10_in_pass1_prefix :
    tmFiber43StateAt 10 ∈ chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10] [tmFiber43StateAt 0] := by
  have hparentBefore :
      tmFiber43StateAt 6 ∈ chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9] [tmFiber43StateAt 0] := by
    rw [show [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9] = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6] ++ [tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9]
      (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6] [tmFiber43StateAt 0]) (tmFiber43StateAt 6)
      tmFiber43State6_in_pass1_prefix
  rw [show [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10] = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9] ++ [tmFiber43StateAt 10] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber43StateAt 10) []
    (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9] [tmFiber43StateAt 0]) (tmFiber43StateAt 6)
    hparentBefore tmFiber43ReverseSingleStep10

theorem tmFiber43State11_in_pass1_prefix :
    tmFiber43StateAt 11 ∈ chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11] [tmFiber43StateAt 0] := by
  have hparentBefore :
      tmFiber43StateAt 7 ∈ chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10] [tmFiber43StateAt 0] := by
    rw [show [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10] = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7] ++ [tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10]
      (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7] [tmFiber43StateAt 0]) (tmFiber43StateAt 7)
      tmFiber43State7_in_pass1_prefix
  rw [show [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11] = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10] ++ [tmFiber43StateAt 11] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber43StateAt 11) []
    (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10] [tmFiber43StateAt 0]) (tmFiber43StateAt 7)
    hparentBefore tmFiber43ReverseSingleStep11

theorem tmFiber43State12_in_pass1_prefix :
    tmFiber43StateAt 12 ∈ chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12] [tmFiber43StateAt 0] := by
  have hparentBefore :
      tmFiber43StateAt 0 ∈ chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11] [tmFiber43StateAt 0] := by
    rw [show [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11] = [tmFiber43StateAt 0] ++ [tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11]
      (chainClosureStep tmWord [tmFiber43StateAt 0] [tmFiber43StateAt 0]) (tmFiber43StateAt 0)
      tmFiber43State0_in_pass1_prefix
  rw [show [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12] = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11] ++ [tmFiber43StateAt 12] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber43StateAt 12) []
    (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11] [tmFiber43StateAt 0]) (tmFiber43StateAt 0)
    hparentBefore tmFiber43ReverseSingleStep12

theorem tmFiber43State13_in_pass1_prefix :
    tmFiber43StateAt 13 ∈ chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13] [tmFiber43StateAt 0] := by
  have hparentBefore :
      tmFiber43StateAt 1 ∈ chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12] [tmFiber43StateAt 0] := by
    rw [show [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12] = [tmFiber43StateAt 0, tmFiber43StateAt 1] ++ [tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12]
      (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1] [tmFiber43StateAt 0]) (tmFiber43StateAt 1)
      tmFiber43State1_in_pass1_prefix
  rw [show [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13] = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12] ++ [tmFiber43StateAt 13] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber43StateAt 13) []
    (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12] [tmFiber43StateAt 0]) (tmFiber43StateAt 1)
    hparentBefore tmFiber43ReverseSingleStep13

theorem tmFiber43State14_in_pass1_prefix :
    tmFiber43StateAt 14 ∈ chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14] [tmFiber43StateAt 0] := by
  have hparentBefore :
      tmFiber43StateAt 2 ∈ chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13] [tmFiber43StateAt 0] := by
    rw [show [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13] = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2] ++ [tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13]
      (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2] [tmFiber43StateAt 0]) (tmFiber43StateAt 2)
      tmFiber43State2_in_pass1_prefix
  rw [show [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14] = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13] ++ [tmFiber43StateAt 14] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber43StateAt 14) []
    (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13] [tmFiber43StateAt 0]) (tmFiber43StateAt 2)
    hparentBefore tmFiber43ReverseSingleStep14

theorem tmFiber43State15_in_pass1_prefix :
    tmFiber43StateAt 15 ∈ chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14, tmFiber43StateAt 15] [tmFiber43StateAt 0] := by
  have hparentBefore :
      tmFiber43StateAt 3 ∈ chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14] [tmFiber43StateAt 0] := by
    rw [show [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14] = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3] ++ [tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14]
      (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3] [tmFiber43StateAt 0]) (tmFiber43StateAt 3)
      tmFiber43State3_in_pass1_prefix
  rw [show [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14, tmFiber43StateAt 15] = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14] ++ [tmFiber43StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber43StateAt 15) []
    (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14] [tmFiber43StateAt 0]) (tmFiber43StateAt 3)
    hparentBefore tmFiber43ReverseSingleStep15

theorem tmFiber43State0_in_pass1_full :
    tmFiber43StateAt 0 ∈ chainClosureStep tmWord tmFiber43DirectStates [tmFiber43StateAt 0] := by
  rw [show tmFiber43DirectStates = [tmFiber43StateAt 0] ++ [tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14, tmFiber43StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14, tmFiber43StateAt 15]
    (chainClosureStep tmWord [tmFiber43StateAt 0] [tmFiber43StateAt 0]) (tmFiber43StateAt 0)
    tmFiber43State0_in_pass1_prefix

theorem tmFiber43State1_in_pass1_full :
    tmFiber43StateAt 1 ∈ chainClosureStep tmWord tmFiber43DirectStates [tmFiber43StateAt 0] := by
  rw [show tmFiber43DirectStates = [tmFiber43StateAt 0, tmFiber43StateAt 1] ++ [tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14, tmFiber43StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14, tmFiber43StateAt 15]
    (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1] [tmFiber43StateAt 0]) (tmFiber43StateAt 1)
    tmFiber43State1_in_pass1_prefix

theorem tmFiber43State2_in_pass1_full :
    tmFiber43StateAt 2 ∈ chainClosureStep tmWord tmFiber43DirectStates [tmFiber43StateAt 0] := by
  rw [show tmFiber43DirectStates = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2] ++ [tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14, tmFiber43StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14, tmFiber43StateAt 15]
    (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2] [tmFiber43StateAt 0]) (tmFiber43StateAt 2)
    tmFiber43State2_in_pass1_prefix

theorem tmFiber43State3_in_pass1_full :
    tmFiber43StateAt 3 ∈ chainClosureStep tmWord tmFiber43DirectStates [tmFiber43StateAt 0] := by
  rw [show tmFiber43DirectStates = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3] ++ [tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14, tmFiber43StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14, tmFiber43StateAt 15]
    (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3] [tmFiber43StateAt 0]) (tmFiber43StateAt 3)
    tmFiber43State3_in_pass1_prefix

theorem tmFiber43State4_in_pass1_full :
    tmFiber43StateAt 4 ∈ chainClosureStep tmWord tmFiber43DirectStates [tmFiber43StateAt 0] := by
  rw [show tmFiber43DirectStates = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4] ++ [tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14, tmFiber43StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14, tmFiber43StateAt 15]
    (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4] [tmFiber43StateAt 0]) (tmFiber43StateAt 4)
    tmFiber43State4_in_pass1_prefix

theorem tmFiber43State5_in_pass1_full :
    tmFiber43StateAt 5 ∈ chainClosureStep tmWord tmFiber43DirectStates [tmFiber43StateAt 0] := by
  rw [show tmFiber43DirectStates = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5] ++ [tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14, tmFiber43StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14, tmFiber43StateAt 15]
    (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5] [tmFiber43StateAt 0]) (tmFiber43StateAt 5)
    tmFiber43State5_in_pass1_prefix

theorem tmFiber43State6_in_pass1_full :
    tmFiber43StateAt 6 ∈ chainClosureStep tmWord tmFiber43DirectStates [tmFiber43StateAt 0] := by
  rw [show tmFiber43DirectStates = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6] ++ [tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14, tmFiber43StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14, tmFiber43StateAt 15]
    (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6] [tmFiber43StateAt 0]) (tmFiber43StateAt 6)
    tmFiber43State6_in_pass1_prefix

theorem tmFiber43State7_in_pass1_full :
    tmFiber43StateAt 7 ∈ chainClosureStep tmWord tmFiber43DirectStates [tmFiber43StateAt 0] := by
  rw [show tmFiber43DirectStates = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7] ++ [tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14, tmFiber43StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14, tmFiber43StateAt 15]
    (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7] [tmFiber43StateAt 0]) (tmFiber43StateAt 7)
    tmFiber43State7_in_pass1_prefix

theorem tmFiber43State8_in_pass1_full :
    tmFiber43StateAt 8 ∈ chainClosureStep tmWord tmFiber43DirectStates [tmFiber43StateAt 0] := by
  rw [show tmFiber43DirectStates = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8] ++ [tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14, tmFiber43StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14, tmFiber43StateAt 15]
    (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8] [tmFiber43StateAt 0]) (tmFiber43StateAt 8)
    tmFiber43State8_in_pass1_prefix

theorem tmFiber43State9_in_pass1_full :
    tmFiber43StateAt 9 ∈ chainClosureStep tmWord tmFiber43DirectStates [tmFiber43StateAt 0] := by
  rw [show tmFiber43DirectStates = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9] ++ [tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14, tmFiber43StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14, tmFiber43StateAt 15]
    (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9] [tmFiber43StateAt 0]) (tmFiber43StateAt 9)
    tmFiber43State9_in_pass1_prefix

theorem tmFiber43State10_in_pass1_full :
    tmFiber43StateAt 10 ∈ chainClosureStep tmWord tmFiber43DirectStates [tmFiber43StateAt 0] := by
  rw [show tmFiber43DirectStates = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10] ++ [tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14, tmFiber43StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14, tmFiber43StateAt 15]
    (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10] [tmFiber43StateAt 0]) (tmFiber43StateAt 10)
    tmFiber43State10_in_pass1_prefix

theorem tmFiber43State11_in_pass1_full :
    tmFiber43StateAt 11 ∈ chainClosureStep tmWord tmFiber43DirectStates [tmFiber43StateAt 0] := by
  rw [show tmFiber43DirectStates = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11] ++ [tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14, tmFiber43StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14, tmFiber43StateAt 15]
    (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11] [tmFiber43StateAt 0]) (tmFiber43StateAt 11)
    tmFiber43State11_in_pass1_prefix

theorem tmFiber43State12_in_pass1_full :
    tmFiber43StateAt 12 ∈ chainClosureStep tmWord tmFiber43DirectStates [tmFiber43StateAt 0] := by
  rw [show tmFiber43DirectStates = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12] ++ [tmFiber43StateAt 13, tmFiber43StateAt 14, tmFiber43StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber43StateAt 13, tmFiber43StateAt 14, tmFiber43StateAt 15]
    (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12] [tmFiber43StateAt 0]) (tmFiber43StateAt 12)
    tmFiber43State12_in_pass1_prefix

theorem tmFiber43State13_in_pass1_full :
    tmFiber43StateAt 13 ∈ chainClosureStep tmWord tmFiber43DirectStates [tmFiber43StateAt 0] := by
  rw [show tmFiber43DirectStates = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13] ++ [tmFiber43StateAt 14, tmFiber43StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber43StateAt 14, tmFiber43StateAt 15]
    (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13] [tmFiber43StateAt 0]) (tmFiber43StateAt 13)
    tmFiber43State13_in_pass1_prefix

theorem tmFiber43State14_in_pass1_full :
    tmFiber43StateAt 14 ∈ chainClosureStep tmWord tmFiber43DirectStates [tmFiber43StateAt 0] := by
  rw [show tmFiber43DirectStates = [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14] ++ [tmFiber43StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber43StateAt 15]
    (chainClosureStep tmWord [tmFiber43StateAt 0, tmFiber43StateAt 1, tmFiber43StateAt 2, tmFiber43StateAt 3, tmFiber43StateAt 4, tmFiber43StateAt 5, tmFiber43StateAt 6, tmFiber43StateAt 7, tmFiber43StateAt 8, tmFiber43StateAt 9, tmFiber43StateAt 10, tmFiber43StateAt 11, tmFiber43StateAt 12, tmFiber43StateAt 13, tmFiber43StateAt 14] [tmFiber43StateAt 0]) (tmFiber43StateAt 14)
    tmFiber43State14_in_pass1_prefix

theorem tmFiber43State15_in_pass1_full :
    tmFiber43StateAt 15 ∈ chainClosureStep tmWord tmFiber43DirectStates [tmFiber43StateAt 0] := by
  simpa [tmFiber43DirectStates] using tmFiber43State15_in_pass1_prefix

theorem tmFiber43State0_in_close :
    tmFiber43StateAt 0 ∈ closeChainFiber tmWord tmFiber43DirectStates tmFiber43DirectStates.length [tmFiber43StateAt 0] := by
  change tmFiber43StateAt 0 ∈ closeChainFiber tmWord tmFiber43DirectStates (15 + 1) [tmFiber43StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber43DirectStates 15 [tmFiber43StateAt 0] (tmFiber43StateAt 0) tmFiber43State0_in_pass1_full

theorem tmFiber43State1_in_close :
    tmFiber43StateAt 1 ∈ closeChainFiber tmWord tmFiber43DirectStates tmFiber43DirectStates.length [tmFiber43StateAt 0] := by
  change tmFiber43StateAt 1 ∈ closeChainFiber tmWord tmFiber43DirectStates (15 + 1) [tmFiber43StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber43DirectStates 15 [tmFiber43StateAt 0] (tmFiber43StateAt 1) tmFiber43State1_in_pass1_full

theorem tmFiber43State2_in_close :
    tmFiber43StateAt 2 ∈ closeChainFiber tmWord tmFiber43DirectStates tmFiber43DirectStates.length [tmFiber43StateAt 0] := by
  change tmFiber43StateAt 2 ∈ closeChainFiber tmWord tmFiber43DirectStates (15 + 1) [tmFiber43StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber43DirectStates 15 [tmFiber43StateAt 0] (tmFiber43StateAt 2) tmFiber43State2_in_pass1_full

theorem tmFiber43State3_in_close :
    tmFiber43StateAt 3 ∈ closeChainFiber tmWord tmFiber43DirectStates tmFiber43DirectStates.length [tmFiber43StateAt 0] := by
  change tmFiber43StateAt 3 ∈ closeChainFiber tmWord tmFiber43DirectStates (15 + 1) [tmFiber43StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber43DirectStates 15 [tmFiber43StateAt 0] (tmFiber43StateAt 3) tmFiber43State3_in_pass1_full

theorem tmFiber43State4_in_close :
    tmFiber43StateAt 4 ∈ closeChainFiber tmWord tmFiber43DirectStates tmFiber43DirectStates.length [tmFiber43StateAt 0] := by
  change tmFiber43StateAt 4 ∈ closeChainFiber tmWord tmFiber43DirectStates (15 + 1) [tmFiber43StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber43DirectStates 15 [tmFiber43StateAt 0] (tmFiber43StateAt 4) tmFiber43State4_in_pass1_full

theorem tmFiber43State5_in_close :
    tmFiber43StateAt 5 ∈ closeChainFiber tmWord tmFiber43DirectStates tmFiber43DirectStates.length [tmFiber43StateAt 0] := by
  change tmFiber43StateAt 5 ∈ closeChainFiber tmWord tmFiber43DirectStates (15 + 1) [tmFiber43StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber43DirectStates 15 [tmFiber43StateAt 0] (tmFiber43StateAt 5) tmFiber43State5_in_pass1_full

theorem tmFiber43State6_in_close :
    tmFiber43StateAt 6 ∈ closeChainFiber tmWord tmFiber43DirectStates tmFiber43DirectStates.length [tmFiber43StateAt 0] := by
  change tmFiber43StateAt 6 ∈ closeChainFiber tmWord tmFiber43DirectStates (15 + 1) [tmFiber43StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber43DirectStates 15 [tmFiber43StateAt 0] (tmFiber43StateAt 6) tmFiber43State6_in_pass1_full

theorem tmFiber43State7_in_close :
    tmFiber43StateAt 7 ∈ closeChainFiber tmWord tmFiber43DirectStates tmFiber43DirectStates.length [tmFiber43StateAt 0] := by
  change tmFiber43StateAt 7 ∈ closeChainFiber tmWord tmFiber43DirectStates (15 + 1) [tmFiber43StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber43DirectStates 15 [tmFiber43StateAt 0] (tmFiber43StateAt 7) tmFiber43State7_in_pass1_full

theorem tmFiber43State8_in_close :
    tmFiber43StateAt 8 ∈ closeChainFiber tmWord tmFiber43DirectStates tmFiber43DirectStates.length [tmFiber43StateAt 0] := by
  change tmFiber43StateAt 8 ∈ closeChainFiber tmWord tmFiber43DirectStates (15 + 1) [tmFiber43StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber43DirectStates 15 [tmFiber43StateAt 0] (tmFiber43StateAt 8) tmFiber43State8_in_pass1_full

theorem tmFiber43State9_in_close :
    tmFiber43StateAt 9 ∈ closeChainFiber tmWord tmFiber43DirectStates tmFiber43DirectStates.length [tmFiber43StateAt 0] := by
  change tmFiber43StateAt 9 ∈ closeChainFiber tmWord tmFiber43DirectStates (15 + 1) [tmFiber43StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber43DirectStates 15 [tmFiber43StateAt 0] (tmFiber43StateAt 9) tmFiber43State9_in_pass1_full

theorem tmFiber43State10_in_close :
    tmFiber43StateAt 10 ∈ closeChainFiber tmWord tmFiber43DirectStates tmFiber43DirectStates.length [tmFiber43StateAt 0] := by
  change tmFiber43StateAt 10 ∈ closeChainFiber tmWord tmFiber43DirectStates (15 + 1) [tmFiber43StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber43DirectStates 15 [tmFiber43StateAt 0] (tmFiber43StateAt 10) tmFiber43State10_in_pass1_full

theorem tmFiber43State11_in_close :
    tmFiber43StateAt 11 ∈ closeChainFiber tmWord tmFiber43DirectStates tmFiber43DirectStates.length [tmFiber43StateAt 0] := by
  change tmFiber43StateAt 11 ∈ closeChainFiber tmWord tmFiber43DirectStates (15 + 1) [tmFiber43StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber43DirectStates 15 [tmFiber43StateAt 0] (tmFiber43StateAt 11) tmFiber43State11_in_pass1_full

theorem tmFiber43State12_in_close :
    tmFiber43StateAt 12 ∈ closeChainFiber tmWord tmFiber43DirectStates tmFiber43DirectStates.length [tmFiber43StateAt 0] := by
  change tmFiber43StateAt 12 ∈ closeChainFiber tmWord tmFiber43DirectStates (15 + 1) [tmFiber43StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber43DirectStates 15 [tmFiber43StateAt 0] (tmFiber43StateAt 12) tmFiber43State12_in_pass1_full

theorem tmFiber43State13_in_close :
    tmFiber43StateAt 13 ∈ closeChainFiber tmWord tmFiber43DirectStates tmFiber43DirectStates.length [tmFiber43StateAt 0] := by
  change tmFiber43StateAt 13 ∈ closeChainFiber tmWord tmFiber43DirectStates (15 + 1) [tmFiber43StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber43DirectStates 15 [tmFiber43StateAt 0] (tmFiber43StateAt 13) tmFiber43State13_in_pass1_full

theorem tmFiber43State14_in_close :
    tmFiber43StateAt 14 ∈ closeChainFiber tmWord tmFiber43DirectStates tmFiber43DirectStates.length [tmFiber43StateAt 0] := by
  change tmFiber43StateAt 14 ∈ closeChainFiber tmWord tmFiber43DirectStates (15 + 1) [tmFiber43StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber43DirectStates 15 [tmFiber43StateAt 0] (tmFiber43StateAt 14) tmFiber43State14_in_pass1_full

theorem tmFiber43State15_in_close :
    tmFiber43StateAt 15 ∈ closeChainFiber tmWord tmFiber43DirectStates tmFiber43DirectStates.length [tmFiber43StateAt 0] := by
  change tmFiber43StateAt 15 ∈ closeChainFiber tmWord tmFiber43DirectStates (15 + 1) [tmFiber43StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber43DirectStates 15 [tmFiber43StateAt 0] (tmFiber43StateAt 15) tmFiber43State15_in_pass1_full

theorem tmFiber43DirectConnected :
    chainFiberConnected tmWord tmFiber43DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber43DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber43State0_in_close
  · subst state
    exact tmFiber43State1_in_close
  · subst state
    exact tmFiber43State2_in_close
  · subst state
    exact tmFiber43State3_in_close
  · subst state
    exact tmFiber43State4_in_close
  · subst state
    exact tmFiber43State5_in_close
  · subst state
    exact tmFiber43State6_in_close
  · subst state
    exact tmFiber43State7_in_close
  · subst state
    exact tmFiber43State8_in_close
  · subst state
    exact tmFiber43State9_in_close
  · subst state
    exact tmFiber43State10_in_close
  · subst state
    exact tmFiber43State11_in_close
  · subst state
    exact tmFiber43State12_in_close
  · subst state
    exact tmFiber43State13_in_close
  · subst state
    exact tmFiber43State14_in_close
  · subst state
    exact tmFiber43State15_in_close
  · cases h

def tmFiber48StateAt (i : Nat) : List TauState :=
  directStates (tmFiber48RowAt i).sourceLeft (tmFiber48RowAt i).sourceRight

def tmFiber48DirectStates : List (List TauState) :=
  [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14, tmFiber48StateAt 15]

theorem tmFiber48ReverseRow_1_ok :
    tmRowReverseValid tmFiber48Key tmFiber48Expected (tmFiber48RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber48Chunk0_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber48Chunk0] at h
  exact h.2

theorem tmFiber48ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber48StateAt 0) (tmFiber48StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber48StateAt 0) (tmFiber48StateAt 1)
    (tmFiber48RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber48Key tmFiber48Expected
        (tmFiber48RowAt 1) (by decide) tmFiber48ReverseRow_1_ok
      simpa [tmFiber48StateAt, tmFiber48RowAt, tmFiber48Rows, listGetD, directRow] using h)

theorem tmFiber48ReverseRow_2_ok :
    tmRowReverseValid tmFiber48Key tmFiber48Expected (tmFiber48RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber48Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber48Chunk1] at h
  exact h.1

theorem tmFiber48ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber48StateAt 0) (tmFiber48StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber48StateAt 0) (tmFiber48StateAt 2)
    (tmFiber48RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber48Key tmFiber48Expected
        (tmFiber48RowAt 2) (by decide) tmFiber48ReverseRow_2_ok
      simpa [tmFiber48StateAt, tmFiber48RowAt, tmFiber48Rows, listGetD, directRow] using h)

theorem tmFiber48ReverseRow_3_ok :
    tmRowReverseValid tmFiber48Key tmFiber48Expected (tmFiber48RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber48Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber48Chunk1] at h
  exact h.2

theorem tmFiber48ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber48StateAt 1) (tmFiber48StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber48StateAt 1) (tmFiber48StateAt 3)
    (tmFiber48RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber48Key tmFiber48Expected
        (tmFiber48RowAt 3) (by decide) tmFiber48ReverseRow_3_ok
      simpa [tmFiber48StateAt, tmFiber48RowAt, tmFiber48Rows, listGetD, directRow] using h)

theorem tmFiber48ReverseRow_4_ok :
    tmRowReverseValid tmFiber48Key tmFiber48Expected (tmFiber48RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber48Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber48Chunk2] at h
  exact h.1

theorem tmFiber48ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber48StateAt 0) (tmFiber48StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber48StateAt 0) (tmFiber48StateAt 4)
    (tmFiber48RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber48Key tmFiber48Expected
        (tmFiber48RowAt 4) (by decide) tmFiber48ReverseRow_4_ok
      simpa [tmFiber48StateAt, tmFiber48RowAt, tmFiber48Rows, listGetD, directRow] using h)

theorem tmFiber48ReverseRow_5_ok :
    tmRowReverseValid tmFiber48Key tmFiber48Expected (tmFiber48RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber48Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber48Chunk2] at h
  exact h.2

theorem tmFiber48ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber48StateAt 1) (tmFiber48StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber48StateAt 1) (tmFiber48StateAt 5)
    (tmFiber48RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber48Key tmFiber48Expected
        (tmFiber48RowAt 5) (by decide) tmFiber48ReverseRow_5_ok
      simpa [tmFiber48StateAt, tmFiber48RowAt, tmFiber48Rows, listGetD, directRow] using h)

theorem tmFiber48ReverseRow_6_ok :
    tmRowReverseValid tmFiber48Key tmFiber48Expected (tmFiber48RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber48Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber48Chunk3] at h
  exact h.1

theorem tmFiber48ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber48StateAt 2) (tmFiber48StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber48StateAt 2) (tmFiber48StateAt 6)
    (tmFiber48RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber48Key tmFiber48Expected
        (tmFiber48RowAt 6) (by decide) tmFiber48ReverseRow_6_ok
      simpa [tmFiber48StateAt, tmFiber48RowAt, tmFiber48Rows, listGetD, directRow] using h)

theorem tmFiber48ReverseRow_7_ok :
    tmRowReverseValid tmFiber48Key tmFiber48Expected (tmFiber48RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber48Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber48Chunk3] at h
  exact h.2

theorem tmFiber48ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber48StateAt 3) (tmFiber48StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber48StateAt 3) (tmFiber48StateAt 7)
    (tmFiber48RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber48Key tmFiber48Expected
        (tmFiber48RowAt 7) (by decide) tmFiber48ReverseRow_7_ok
      simpa [tmFiber48StateAt, tmFiber48RowAt, tmFiber48Rows, listGetD, directRow] using h)

theorem tmFiber48ReverseRow_8_ok :
    tmRowReverseValid tmFiber48Key tmFiber48Expected (tmFiber48RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber48Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber48Chunk4] at h
  exact h.1

theorem tmFiber48ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber48StateAt 0) (tmFiber48StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber48StateAt 0) (tmFiber48StateAt 8)
    (tmFiber48RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber48Key tmFiber48Expected
        (tmFiber48RowAt 8) (by decide) tmFiber48ReverseRow_8_ok
      simpa [tmFiber48StateAt, tmFiber48RowAt, tmFiber48Rows, listGetD, directRow] using h)

theorem tmFiber48ReverseRow_9_ok :
    tmRowReverseValid tmFiber48Key tmFiber48Expected (tmFiber48RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber48Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber48Chunk4] at h
  exact h.2

theorem tmFiber48ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber48StateAt 1) (tmFiber48StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber48StateAt 1) (tmFiber48StateAt 9)
    (tmFiber48RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber48Key tmFiber48Expected
        (tmFiber48RowAt 9) (by decide) tmFiber48ReverseRow_9_ok
      simpa [tmFiber48StateAt, tmFiber48RowAt, tmFiber48Rows, listGetD, directRow] using h)

theorem tmFiber48ReverseRow_10_ok :
    tmRowReverseValid tmFiber48Key tmFiber48Expected (tmFiber48RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber48Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber48Chunk5] at h
  exact h.1

theorem tmFiber48ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber48StateAt 2) (tmFiber48StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber48StateAt 2) (tmFiber48StateAt 10)
    (tmFiber48RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber48Key tmFiber48Expected
        (tmFiber48RowAt 10) (by decide) tmFiber48ReverseRow_10_ok
      simpa [tmFiber48StateAt, tmFiber48RowAt, tmFiber48Rows, listGetD, directRow] using h)

theorem tmFiber48ReverseRow_11_ok :
    tmRowReverseValid tmFiber48Key tmFiber48Expected (tmFiber48RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber48Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber48Chunk5] at h
  exact h.2

theorem tmFiber48ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber48StateAt 3) (tmFiber48StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber48StateAt 3) (tmFiber48StateAt 11)
    (tmFiber48RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber48Key tmFiber48Expected
        (tmFiber48RowAt 11) (by decide) tmFiber48ReverseRow_11_ok
      simpa [tmFiber48StateAt, tmFiber48RowAt, tmFiber48Rows, listGetD, directRow] using h)

theorem tmFiber48ReverseRow_12_ok :
    tmRowReverseValid tmFiber48Key tmFiber48Expected (tmFiber48RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber48Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber48Chunk6] at h
  exact h.1

theorem tmFiber48ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber48StateAt 4) (tmFiber48StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber48StateAt 4) (tmFiber48StateAt 12)
    (tmFiber48RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber48Key tmFiber48Expected
        (tmFiber48RowAt 12) (by decide) tmFiber48ReverseRow_12_ok
      simpa [tmFiber48StateAt, tmFiber48RowAt, tmFiber48Rows, listGetD, directRow] using h)

theorem tmFiber48ReverseRow_13_ok :
    tmRowReverseValid tmFiber48Key tmFiber48Expected (tmFiber48RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber48Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber48Chunk6] at h
  exact h.2

theorem tmFiber48ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber48StateAt 5) (tmFiber48StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber48StateAt 5) (tmFiber48StateAt 13)
    (tmFiber48RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber48Key tmFiber48Expected
        (tmFiber48RowAt 13) (by decide) tmFiber48ReverseRow_13_ok
      simpa [tmFiber48StateAt, tmFiber48RowAt, tmFiber48Rows, listGetD, directRow] using h)

theorem tmFiber48ReverseRow_14_ok :
    tmRowReverseValid tmFiber48Key tmFiber48Expected (tmFiber48RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber48Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber48Chunk7] at h
  exact h.1

theorem tmFiber48ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber48StateAt 6) (tmFiber48StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber48StateAt 6) (tmFiber48StateAt 14)
    (tmFiber48RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber48Key tmFiber48Expected
        (tmFiber48RowAt 14) (by decide) tmFiber48ReverseRow_14_ok
      simpa [tmFiber48StateAt, tmFiber48RowAt, tmFiber48Rows, listGetD, directRow] using h)

theorem tmFiber48ReverseRow_15_ok :
    tmRowReverseValid tmFiber48Key tmFiber48Expected (tmFiber48RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber48Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber48Chunk7] at h
  exact h.2

theorem tmFiber48ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber48StateAt 7) (tmFiber48StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber48StateAt 7) (tmFiber48StateAt 15)
    (tmFiber48RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber48Key tmFiber48Expected
        (tmFiber48RowAt 15) (by decide) tmFiber48ReverseRow_15_ok
      simpa [tmFiber48StateAt, tmFiber48RowAt, tmFiber48Rows, listGetD, directRow] using h)

theorem tmFiber48State0_in_pass1_prefix :
    tmFiber48StateAt 0 ∈ chainClosureStep tmWord [tmFiber48StateAt 0] [tmFiber48StateAt 0] := by
  exact chainClosureStep_mem_of_seen tmWord [tmFiber48StateAt 0] [tmFiber48StateAt 0] (tmFiber48StateAt 0) (by simp)

theorem tmFiber48State1_in_pass1_prefix :
    tmFiber48StateAt 1 ∈ chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1] [tmFiber48StateAt 0] := by
  have hparentBefore :
      tmFiber48StateAt 0 ∈ chainClosureStep tmWord [tmFiber48StateAt 0] [tmFiber48StateAt 0] := by
    exact tmFiber48State0_in_pass1_prefix
  rw [show [tmFiber48StateAt 0, tmFiber48StateAt 1] = [tmFiber48StateAt 0] ++ [tmFiber48StateAt 1] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber48StateAt 1) []
    (chainClosureStep tmWord [tmFiber48StateAt 0] [tmFiber48StateAt 0]) (tmFiber48StateAt 0)
    hparentBefore tmFiber48ReverseSingleStep1

theorem tmFiber48State2_in_pass1_prefix :
    tmFiber48StateAt 2 ∈ chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2] [tmFiber48StateAt 0] := by
  have hparentBefore :
      tmFiber48StateAt 0 ∈ chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1] [tmFiber48StateAt 0] := by
    rw [show [tmFiber48StateAt 0, tmFiber48StateAt 1] = [tmFiber48StateAt 0] ++ [tmFiber48StateAt 1] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber48StateAt 1]
      (chainClosureStep tmWord [tmFiber48StateAt 0] [tmFiber48StateAt 0]) (tmFiber48StateAt 0)
      tmFiber48State0_in_pass1_prefix
  rw [show [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2] = [tmFiber48StateAt 0, tmFiber48StateAt 1] ++ [tmFiber48StateAt 2] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber48StateAt 2) []
    (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1] [tmFiber48StateAt 0]) (tmFiber48StateAt 0)
    hparentBefore tmFiber48ReverseSingleStep2

theorem tmFiber48State3_in_pass1_prefix :
    tmFiber48StateAt 3 ∈ chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3] [tmFiber48StateAt 0] := by
  have hparentBefore :
      tmFiber48StateAt 1 ∈ chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2] [tmFiber48StateAt 0] := by
    rw [show [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2] = [tmFiber48StateAt 0, tmFiber48StateAt 1] ++ [tmFiber48StateAt 2] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber48StateAt 2]
      (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1] [tmFiber48StateAt 0]) (tmFiber48StateAt 1)
      tmFiber48State1_in_pass1_prefix
  rw [show [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3] = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2] ++ [tmFiber48StateAt 3] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber48StateAt 3) []
    (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2] [tmFiber48StateAt 0]) (tmFiber48StateAt 1)
    hparentBefore tmFiber48ReverseSingleStep3

theorem tmFiber48State4_in_pass1_prefix :
    tmFiber48StateAt 4 ∈ chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4] [tmFiber48StateAt 0] := by
  have hparentBefore :
      tmFiber48StateAt 0 ∈ chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3] [tmFiber48StateAt 0] := by
    rw [show [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3] = [tmFiber48StateAt 0] ++ [tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3]
      (chainClosureStep tmWord [tmFiber48StateAt 0] [tmFiber48StateAt 0]) (tmFiber48StateAt 0)
      tmFiber48State0_in_pass1_prefix
  rw [show [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4] = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3] ++ [tmFiber48StateAt 4] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber48StateAt 4) []
    (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3] [tmFiber48StateAt 0]) (tmFiber48StateAt 0)
    hparentBefore tmFiber48ReverseSingleStep4

theorem tmFiber48State5_in_pass1_prefix :
    tmFiber48StateAt 5 ∈ chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5] [tmFiber48StateAt 0] := by
  have hparentBefore :
      tmFiber48StateAt 1 ∈ chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4] [tmFiber48StateAt 0] := by
    rw [show [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4] = [tmFiber48StateAt 0, tmFiber48StateAt 1] ++ [tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4]
      (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1] [tmFiber48StateAt 0]) (tmFiber48StateAt 1)
      tmFiber48State1_in_pass1_prefix
  rw [show [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5] = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4] ++ [tmFiber48StateAt 5] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber48StateAt 5) []
    (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4] [tmFiber48StateAt 0]) (tmFiber48StateAt 1)
    hparentBefore tmFiber48ReverseSingleStep5

theorem tmFiber48State6_in_pass1_prefix :
    tmFiber48StateAt 6 ∈ chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6] [tmFiber48StateAt 0] := by
  have hparentBefore :
      tmFiber48StateAt 2 ∈ chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5] [tmFiber48StateAt 0] := by
    rw [show [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5] = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2] ++ [tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5]
      (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2] [tmFiber48StateAt 0]) (tmFiber48StateAt 2)
      tmFiber48State2_in_pass1_prefix
  rw [show [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6] = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5] ++ [tmFiber48StateAt 6] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber48StateAt 6) []
    (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5] [tmFiber48StateAt 0]) (tmFiber48StateAt 2)
    hparentBefore tmFiber48ReverseSingleStep6

theorem tmFiber48State7_in_pass1_prefix :
    tmFiber48StateAt 7 ∈ chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7] [tmFiber48StateAt 0] := by
  have hparentBefore :
      tmFiber48StateAt 3 ∈ chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6] [tmFiber48StateAt 0] := by
    rw [show [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6] = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3] ++ [tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6]
      (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3] [tmFiber48StateAt 0]) (tmFiber48StateAt 3)
      tmFiber48State3_in_pass1_prefix
  rw [show [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7] = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6] ++ [tmFiber48StateAt 7] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber48StateAt 7) []
    (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6] [tmFiber48StateAt 0]) (tmFiber48StateAt 3)
    hparentBefore tmFiber48ReverseSingleStep7

theorem tmFiber48State8_in_pass1_prefix :
    tmFiber48StateAt 8 ∈ chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8] [tmFiber48StateAt 0] := by
  have hparentBefore :
      tmFiber48StateAt 0 ∈ chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7] [tmFiber48StateAt 0] := by
    rw [show [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7] = [tmFiber48StateAt 0] ++ [tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7]
      (chainClosureStep tmWord [tmFiber48StateAt 0] [tmFiber48StateAt 0]) (tmFiber48StateAt 0)
      tmFiber48State0_in_pass1_prefix
  rw [show [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8] = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7] ++ [tmFiber48StateAt 8] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber48StateAt 8) []
    (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7] [tmFiber48StateAt 0]) (tmFiber48StateAt 0)
    hparentBefore tmFiber48ReverseSingleStep8

theorem tmFiber48State9_in_pass1_prefix :
    tmFiber48StateAt 9 ∈ chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9] [tmFiber48StateAt 0] := by
  have hparentBefore :
      tmFiber48StateAt 1 ∈ chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8] [tmFiber48StateAt 0] := by
    rw [show [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8] = [tmFiber48StateAt 0, tmFiber48StateAt 1] ++ [tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8]
      (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1] [tmFiber48StateAt 0]) (tmFiber48StateAt 1)
      tmFiber48State1_in_pass1_prefix
  rw [show [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9] = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8] ++ [tmFiber48StateAt 9] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber48StateAt 9) []
    (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8] [tmFiber48StateAt 0]) (tmFiber48StateAt 1)
    hparentBefore tmFiber48ReverseSingleStep9

theorem tmFiber48State10_in_pass1_prefix :
    tmFiber48StateAt 10 ∈ chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10] [tmFiber48StateAt 0] := by
  have hparentBefore :
      tmFiber48StateAt 2 ∈ chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9] [tmFiber48StateAt 0] := by
    rw [show [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9] = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2] ++ [tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9]
      (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2] [tmFiber48StateAt 0]) (tmFiber48StateAt 2)
      tmFiber48State2_in_pass1_prefix
  rw [show [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10] = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9] ++ [tmFiber48StateAt 10] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber48StateAt 10) []
    (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9] [tmFiber48StateAt 0]) (tmFiber48StateAt 2)
    hparentBefore tmFiber48ReverseSingleStep10

theorem tmFiber48State11_in_pass1_prefix :
    tmFiber48StateAt 11 ∈ chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11] [tmFiber48StateAt 0] := by
  have hparentBefore :
      tmFiber48StateAt 3 ∈ chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10] [tmFiber48StateAt 0] := by
    rw [show [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10] = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3] ++ [tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10]
      (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3] [tmFiber48StateAt 0]) (tmFiber48StateAt 3)
      tmFiber48State3_in_pass1_prefix
  rw [show [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11] = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10] ++ [tmFiber48StateAt 11] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber48StateAt 11) []
    (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10] [tmFiber48StateAt 0]) (tmFiber48StateAt 3)
    hparentBefore tmFiber48ReverseSingleStep11

theorem tmFiber48State12_in_pass1_prefix :
    tmFiber48StateAt 12 ∈ chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12] [tmFiber48StateAt 0] := by
  have hparentBefore :
      tmFiber48StateAt 4 ∈ chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11] [tmFiber48StateAt 0] := by
    rw [show [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11] = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4] ++ [tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11]
      (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4] [tmFiber48StateAt 0]) (tmFiber48StateAt 4)
      tmFiber48State4_in_pass1_prefix
  rw [show [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12] = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11] ++ [tmFiber48StateAt 12] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber48StateAt 12) []
    (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11] [tmFiber48StateAt 0]) (tmFiber48StateAt 4)
    hparentBefore tmFiber48ReverseSingleStep12

theorem tmFiber48State13_in_pass1_prefix :
    tmFiber48StateAt 13 ∈ chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13] [tmFiber48StateAt 0] := by
  have hparentBefore :
      tmFiber48StateAt 5 ∈ chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12] [tmFiber48StateAt 0] := by
    rw [show [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12] = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5] ++ [tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12]
      (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5] [tmFiber48StateAt 0]) (tmFiber48StateAt 5)
      tmFiber48State5_in_pass1_prefix
  rw [show [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13] = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12] ++ [tmFiber48StateAt 13] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber48StateAt 13) []
    (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12] [tmFiber48StateAt 0]) (tmFiber48StateAt 5)
    hparentBefore tmFiber48ReverseSingleStep13

theorem tmFiber48State14_in_pass1_prefix :
    tmFiber48StateAt 14 ∈ chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14] [tmFiber48StateAt 0] := by
  have hparentBefore :
      tmFiber48StateAt 6 ∈ chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13] [tmFiber48StateAt 0] := by
    rw [show [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13] = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6] ++ [tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13]
      (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6] [tmFiber48StateAt 0]) (tmFiber48StateAt 6)
      tmFiber48State6_in_pass1_prefix
  rw [show [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14] = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13] ++ [tmFiber48StateAt 14] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber48StateAt 14) []
    (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13] [tmFiber48StateAt 0]) (tmFiber48StateAt 6)
    hparentBefore tmFiber48ReverseSingleStep14

theorem tmFiber48State15_in_pass1_prefix :
    tmFiber48StateAt 15 ∈ chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14, tmFiber48StateAt 15] [tmFiber48StateAt 0] := by
  have hparentBefore :
      tmFiber48StateAt 7 ∈ chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14] [tmFiber48StateAt 0] := by
    rw [show [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14] = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7] ++ [tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14]
      (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7] [tmFiber48StateAt 0]) (tmFiber48StateAt 7)
      tmFiber48State7_in_pass1_prefix
  rw [show [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14, tmFiber48StateAt 15] = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14] ++ [tmFiber48StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber48StateAt 15) []
    (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14] [tmFiber48StateAt 0]) (tmFiber48StateAt 7)
    hparentBefore tmFiber48ReverseSingleStep15

theorem tmFiber48State0_in_pass1_full :
    tmFiber48StateAt 0 ∈ chainClosureStep tmWord tmFiber48DirectStates [tmFiber48StateAt 0] := by
  rw [show tmFiber48DirectStates = [tmFiber48StateAt 0] ++ [tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14, tmFiber48StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14, tmFiber48StateAt 15]
    (chainClosureStep tmWord [tmFiber48StateAt 0] [tmFiber48StateAt 0]) (tmFiber48StateAt 0)
    tmFiber48State0_in_pass1_prefix

theorem tmFiber48State1_in_pass1_full :
    tmFiber48StateAt 1 ∈ chainClosureStep tmWord tmFiber48DirectStates [tmFiber48StateAt 0] := by
  rw [show tmFiber48DirectStates = [tmFiber48StateAt 0, tmFiber48StateAt 1] ++ [tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14, tmFiber48StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14, tmFiber48StateAt 15]
    (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1] [tmFiber48StateAt 0]) (tmFiber48StateAt 1)
    tmFiber48State1_in_pass1_prefix

theorem tmFiber48State2_in_pass1_full :
    tmFiber48StateAt 2 ∈ chainClosureStep tmWord tmFiber48DirectStates [tmFiber48StateAt 0] := by
  rw [show tmFiber48DirectStates = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2] ++ [tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14, tmFiber48StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14, tmFiber48StateAt 15]
    (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2] [tmFiber48StateAt 0]) (tmFiber48StateAt 2)
    tmFiber48State2_in_pass1_prefix

theorem tmFiber48State3_in_pass1_full :
    tmFiber48StateAt 3 ∈ chainClosureStep tmWord tmFiber48DirectStates [tmFiber48StateAt 0] := by
  rw [show tmFiber48DirectStates = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3] ++ [tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14, tmFiber48StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14, tmFiber48StateAt 15]
    (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3] [tmFiber48StateAt 0]) (tmFiber48StateAt 3)
    tmFiber48State3_in_pass1_prefix

theorem tmFiber48State4_in_pass1_full :
    tmFiber48StateAt 4 ∈ chainClosureStep tmWord tmFiber48DirectStates [tmFiber48StateAt 0] := by
  rw [show tmFiber48DirectStates = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4] ++ [tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14, tmFiber48StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14, tmFiber48StateAt 15]
    (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4] [tmFiber48StateAt 0]) (tmFiber48StateAt 4)
    tmFiber48State4_in_pass1_prefix

theorem tmFiber48State5_in_pass1_full :
    tmFiber48StateAt 5 ∈ chainClosureStep tmWord tmFiber48DirectStates [tmFiber48StateAt 0] := by
  rw [show tmFiber48DirectStates = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5] ++ [tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14, tmFiber48StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14, tmFiber48StateAt 15]
    (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5] [tmFiber48StateAt 0]) (tmFiber48StateAt 5)
    tmFiber48State5_in_pass1_prefix

theorem tmFiber48State6_in_pass1_full :
    tmFiber48StateAt 6 ∈ chainClosureStep tmWord tmFiber48DirectStates [tmFiber48StateAt 0] := by
  rw [show tmFiber48DirectStates = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6] ++ [tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14, tmFiber48StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14, tmFiber48StateAt 15]
    (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6] [tmFiber48StateAt 0]) (tmFiber48StateAt 6)
    tmFiber48State6_in_pass1_prefix

theorem tmFiber48State7_in_pass1_full :
    tmFiber48StateAt 7 ∈ chainClosureStep tmWord tmFiber48DirectStates [tmFiber48StateAt 0] := by
  rw [show tmFiber48DirectStates = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7] ++ [tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14, tmFiber48StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14, tmFiber48StateAt 15]
    (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7] [tmFiber48StateAt 0]) (tmFiber48StateAt 7)
    tmFiber48State7_in_pass1_prefix

theorem tmFiber48State8_in_pass1_full :
    tmFiber48StateAt 8 ∈ chainClosureStep tmWord tmFiber48DirectStates [tmFiber48StateAt 0] := by
  rw [show tmFiber48DirectStates = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8] ++ [tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14, tmFiber48StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14, tmFiber48StateAt 15]
    (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8] [tmFiber48StateAt 0]) (tmFiber48StateAt 8)
    tmFiber48State8_in_pass1_prefix

theorem tmFiber48State9_in_pass1_full :
    tmFiber48StateAt 9 ∈ chainClosureStep tmWord tmFiber48DirectStates [tmFiber48StateAt 0] := by
  rw [show tmFiber48DirectStates = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9] ++ [tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14, tmFiber48StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14, tmFiber48StateAt 15]
    (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9] [tmFiber48StateAt 0]) (tmFiber48StateAt 9)
    tmFiber48State9_in_pass1_prefix

theorem tmFiber48State10_in_pass1_full :
    tmFiber48StateAt 10 ∈ chainClosureStep tmWord tmFiber48DirectStates [tmFiber48StateAt 0] := by
  rw [show tmFiber48DirectStates = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10] ++ [tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14, tmFiber48StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14, tmFiber48StateAt 15]
    (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10] [tmFiber48StateAt 0]) (tmFiber48StateAt 10)
    tmFiber48State10_in_pass1_prefix

theorem tmFiber48State11_in_pass1_full :
    tmFiber48StateAt 11 ∈ chainClosureStep tmWord tmFiber48DirectStates [tmFiber48StateAt 0] := by
  rw [show tmFiber48DirectStates = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11] ++ [tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14, tmFiber48StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14, tmFiber48StateAt 15]
    (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11] [tmFiber48StateAt 0]) (tmFiber48StateAt 11)
    tmFiber48State11_in_pass1_prefix

theorem tmFiber48State12_in_pass1_full :
    tmFiber48StateAt 12 ∈ chainClosureStep tmWord tmFiber48DirectStates [tmFiber48StateAt 0] := by
  rw [show tmFiber48DirectStates = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12] ++ [tmFiber48StateAt 13, tmFiber48StateAt 14, tmFiber48StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber48StateAt 13, tmFiber48StateAt 14, tmFiber48StateAt 15]
    (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12] [tmFiber48StateAt 0]) (tmFiber48StateAt 12)
    tmFiber48State12_in_pass1_prefix

theorem tmFiber48State13_in_pass1_full :
    tmFiber48StateAt 13 ∈ chainClosureStep tmWord tmFiber48DirectStates [tmFiber48StateAt 0] := by
  rw [show tmFiber48DirectStates = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13] ++ [tmFiber48StateAt 14, tmFiber48StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber48StateAt 14, tmFiber48StateAt 15]
    (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13] [tmFiber48StateAt 0]) (tmFiber48StateAt 13)
    tmFiber48State13_in_pass1_prefix

theorem tmFiber48State14_in_pass1_full :
    tmFiber48StateAt 14 ∈ chainClosureStep tmWord tmFiber48DirectStates [tmFiber48StateAt 0] := by
  rw [show tmFiber48DirectStates = [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14] ++ [tmFiber48StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber48StateAt 15]
    (chainClosureStep tmWord [tmFiber48StateAt 0, tmFiber48StateAt 1, tmFiber48StateAt 2, tmFiber48StateAt 3, tmFiber48StateAt 4, tmFiber48StateAt 5, tmFiber48StateAt 6, tmFiber48StateAt 7, tmFiber48StateAt 8, tmFiber48StateAt 9, tmFiber48StateAt 10, tmFiber48StateAt 11, tmFiber48StateAt 12, tmFiber48StateAt 13, tmFiber48StateAt 14] [tmFiber48StateAt 0]) (tmFiber48StateAt 14)
    tmFiber48State14_in_pass1_prefix

theorem tmFiber48State15_in_pass1_full :
    tmFiber48StateAt 15 ∈ chainClosureStep tmWord tmFiber48DirectStates [tmFiber48StateAt 0] := by
  simpa [tmFiber48DirectStates] using tmFiber48State15_in_pass1_prefix

theorem tmFiber48State0_in_close :
    tmFiber48StateAt 0 ∈ closeChainFiber tmWord tmFiber48DirectStates tmFiber48DirectStates.length [tmFiber48StateAt 0] := by
  change tmFiber48StateAt 0 ∈ closeChainFiber tmWord tmFiber48DirectStates (15 + 1) [tmFiber48StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber48DirectStates 15 [tmFiber48StateAt 0] (tmFiber48StateAt 0) tmFiber48State0_in_pass1_full

theorem tmFiber48State1_in_close :
    tmFiber48StateAt 1 ∈ closeChainFiber tmWord tmFiber48DirectStates tmFiber48DirectStates.length [tmFiber48StateAt 0] := by
  change tmFiber48StateAt 1 ∈ closeChainFiber tmWord tmFiber48DirectStates (15 + 1) [tmFiber48StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber48DirectStates 15 [tmFiber48StateAt 0] (tmFiber48StateAt 1) tmFiber48State1_in_pass1_full

theorem tmFiber48State2_in_close :
    tmFiber48StateAt 2 ∈ closeChainFiber tmWord tmFiber48DirectStates tmFiber48DirectStates.length [tmFiber48StateAt 0] := by
  change tmFiber48StateAt 2 ∈ closeChainFiber tmWord tmFiber48DirectStates (15 + 1) [tmFiber48StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber48DirectStates 15 [tmFiber48StateAt 0] (tmFiber48StateAt 2) tmFiber48State2_in_pass1_full

theorem tmFiber48State3_in_close :
    tmFiber48StateAt 3 ∈ closeChainFiber tmWord tmFiber48DirectStates tmFiber48DirectStates.length [tmFiber48StateAt 0] := by
  change tmFiber48StateAt 3 ∈ closeChainFiber tmWord tmFiber48DirectStates (15 + 1) [tmFiber48StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber48DirectStates 15 [tmFiber48StateAt 0] (tmFiber48StateAt 3) tmFiber48State3_in_pass1_full

theorem tmFiber48State4_in_close :
    tmFiber48StateAt 4 ∈ closeChainFiber tmWord tmFiber48DirectStates tmFiber48DirectStates.length [tmFiber48StateAt 0] := by
  change tmFiber48StateAt 4 ∈ closeChainFiber tmWord tmFiber48DirectStates (15 + 1) [tmFiber48StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber48DirectStates 15 [tmFiber48StateAt 0] (tmFiber48StateAt 4) tmFiber48State4_in_pass1_full

theorem tmFiber48State5_in_close :
    tmFiber48StateAt 5 ∈ closeChainFiber tmWord tmFiber48DirectStates tmFiber48DirectStates.length [tmFiber48StateAt 0] := by
  change tmFiber48StateAt 5 ∈ closeChainFiber tmWord tmFiber48DirectStates (15 + 1) [tmFiber48StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber48DirectStates 15 [tmFiber48StateAt 0] (tmFiber48StateAt 5) tmFiber48State5_in_pass1_full

theorem tmFiber48State6_in_close :
    tmFiber48StateAt 6 ∈ closeChainFiber tmWord tmFiber48DirectStates tmFiber48DirectStates.length [tmFiber48StateAt 0] := by
  change tmFiber48StateAt 6 ∈ closeChainFiber tmWord tmFiber48DirectStates (15 + 1) [tmFiber48StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber48DirectStates 15 [tmFiber48StateAt 0] (tmFiber48StateAt 6) tmFiber48State6_in_pass1_full

theorem tmFiber48State7_in_close :
    tmFiber48StateAt 7 ∈ closeChainFiber tmWord tmFiber48DirectStates tmFiber48DirectStates.length [tmFiber48StateAt 0] := by
  change tmFiber48StateAt 7 ∈ closeChainFiber tmWord tmFiber48DirectStates (15 + 1) [tmFiber48StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber48DirectStates 15 [tmFiber48StateAt 0] (tmFiber48StateAt 7) tmFiber48State7_in_pass1_full

theorem tmFiber48State8_in_close :
    tmFiber48StateAt 8 ∈ closeChainFiber tmWord tmFiber48DirectStates tmFiber48DirectStates.length [tmFiber48StateAt 0] := by
  change tmFiber48StateAt 8 ∈ closeChainFiber tmWord tmFiber48DirectStates (15 + 1) [tmFiber48StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber48DirectStates 15 [tmFiber48StateAt 0] (tmFiber48StateAt 8) tmFiber48State8_in_pass1_full

theorem tmFiber48State9_in_close :
    tmFiber48StateAt 9 ∈ closeChainFiber tmWord tmFiber48DirectStates tmFiber48DirectStates.length [tmFiber48StateAt 0] := by
  change tmFiber48StateAt 9 ∈ closeChainFiber tmWord tmFiber48DirectStates (15 + 1) [tmFiber48StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber48DirectStates 15 [tmFiber48StateAt 0] (tmFiber48StateAt 9) tmFiber48State9_in_pass1_full

theorem tmFiber48State10_in_close :
    tmFiber48StateAt 10 ∈ closeChainFiber tmWord tmFiber48DirectStates tmFiber48DirectStates.length [tmFiber48StateAt 0] := by
  change tmFiber48StateAt 10 ∈ closeChainFiber tmWord tmFiber48DirectStates (15 + 1) [tmFiber48StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber48DirectStates 15 [tmFiber48StateAt 0] (tmFiber48StateAt 10) tmFiber48State10_in_pass1_full

theorem tmFiber48State11_in_close :
    tmFiber48StateAt 11 ∈ closeChainFiber tmWord tmFiber48DirectStates tmFiber48DirectStates.length [tmFiber48StateAt 0] := by
  change tmFiber48StateAt 11 ∈ closeChainFiber tmWord tmFiber48DirectStates (15 + 1) [tmFiber48StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber48DirectStates 15 [tmFiber48StateAt 0] (tmFiber48StateAt 11) tmFiber48State11_in_pass1_full

theorem tmFiber48State12_in_close :
    tmFiber48StateAt 12 ∈ closeChainFiber tmWord tmFiber48DirectStates tmFiber48DirectStates.length [tmFiber48StateAt 0] := by
  change tmFiber48StateAt 12 ∈ closeChainFiber tmWord tmFiber48DirectStates (15 + 1) [tmFiber48StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber48DirectStates 15 [tmFiber48StateAt 0] (tmFiber48StateAt 12) tmFiber48State12_in_pass1_full

theorem tmFiber48State13_in_close :
    tmFiber48StateAt 13 ∈ closeChainFiber tmWord tmFiber48DirectStates tmFiber48DirectStates.length [tmFiber48StateAt 0] := by
  change tmFiber48StateAt 13 ∈ closeChainFiber tmWord tmFiber48DirectStates (15 + 1) [tmFiber48StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber48DirectStates 15 [tmFiber48StateAt 0] (tmFiber48StateAt 13) tmFiber48State13_in_pass1_full

theorem tmFiber48State14_in_close :
    tmFiber48StateAt 14 ∈ closeChainFiber tmWord tmFiber48DirectStates tmFiber48DirectStates.length [tmFiber48StateAt 0] := by
  change tmFiber48StateAt 14 ∈ closeChainFiber tmWord tmFiber48DirectStates (15 + 1) [tmFiber48StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber48DirectStates 15 [tmFiber48StateAt 0] (tmFiber48StateAt 14) tmFiber48State14_in_pass1_full

theorem tmFiber48State15_in_close :
    tmFiber48StateAt 15 ∈ closeChainFiber tmWord tmFiber48DirectStates tmFiber48DirectStates.length [tmFiber48StateAt 0] := by
  change tmFiber48StateAt 15 ∈ closeChainFiber tmWord tmFiber48DirectStates (15 + 1) [tmFiber48StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber48DirectStates 15 [tmFiber48StateAt 0] (tmFiber48StateAt 15) tmFiber48State15_in_pass1_full

theorem tmFiber48DirectConnected :
    chainFiberConnected tmWord tmFiber48DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber48DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber48State0_in_close
  · subst state
    exact tmFiber48State1_in_close
  · subst state
    exact tmFiber48State2_in_close
  · subst state
    exact tmFiber48State3_in_close
  · subst state
    exact tmFiber48State4_in_close
  · subst state
    exact tmFiber48State5_in_close
  · subst state
    exact tmFiber48State6_in_close
  · subst state
    exact tmFiber48State7_in_close
  · subst state
    exact tmFiber48State8_in_close
  · subst state
    exact tmFiber48State9_in_close
  · subst state
    exact tmFiber48State10_in_close
  · subst state
    exact tmFiber48State11_in_close
  · subst state
    exact tmFiber48State12_in_close
  · subst state
    exact tmFiber48State13_in_close
  · subst state
    exact tmFiber48State14_in_close
  · subst state
    exact tmFiber48State15_in_close
  · cases h

def tmFiber49StateAt (i : Nat) : List TauState :=
  directStates (tmFiber49RowAt i).sourceLeft (tmFiber49RowAt i).sourceRight

def tmFiber49DirectStates : List (List TauState) :=
  [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14, tmFiber49StateAt 15]

theorem tmFiber49ReverseRow_1_ok :
    tmRowReverseValid tmFiber49Key tmFiber49Expected (tmFiber49RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber49Chunk0_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber49Chunk0] at h
  exact h.2

theorem tmFiber49ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber49StateAt 0) (tmFiber49StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber49StateAt 0) (tmFiber49StateAt 1)
    (tmFiber49RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber49Key tmFiber49Expected
        (tmFiber49RowAt 1) (by decide) tmFiber49ReverseRow_1_ok
      simpa [tmFiber49StateAt, tmFiber49RowAt, tmFiber49Rows, listGetD, directRow] using h)

theorem tmFiber49ReverseRow_2_ok :
    tmRowReverseValid tmFiber49Key tmFiber49Expected (tmFiber49RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber49Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber49Chunk1] at h
  exact h.1

theorem tmFiber49ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber49StateAt 0) (tmFiber49StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber49StateAt 0) (tmFiber49StateAt 2)
    (tmFiber49RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber49Key tmFiber49Expected
        (tmFiber49RowAt 2) (by decide) tmFiber49ReverseRow_2_ok
      simpa [tmFiber49StateAt, tmFiber49RowAt, tmFiber49Rows, listGetD, directRow] using h)

theorem tmFiber49ReverseRow_3_ok :
    tmRowReverseValid tmFiber49Key tmFiber49Expected (tmFiber49RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber49Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber49Chunk1] at h
  exact h.2

theorem tmFiber49ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber49StateAt 1) (tmFiber49StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber49StateAt 1) (tmFiber49StateAt 3)
    (tmFiber49RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber49Key tmFiber49Expected
        (tmFiber49RowAt 3) (by decide) tmFiber49ReverseRow_3_ok
      simpa [tmFiber49StateAt, tmFiber49RowAt, tmFiber49Rows, listGetD, directRow] using h)

theorem tmFiber49ReverseRow_4_ok :
    tmRowReverseValid tmFiber49Key tmFiber49Expected (tmFiber49RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber49Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber49Chunk2] at h
  exact h.1

theorem tmFiber49ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber49StateAt 0) (tmFiber49StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber49StateAt 0) (tmFiber49StateAt 4)
    (tmFiber49RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber49Key tmFiber49Expected
        (tmFiber49RowAt 4) (by decide) tmFiber49ReverseRow_4_ok
      simpa [tmFiber49StateAt, tmFiber49RowAt, tmFiber49Rows, listGetD, directRow] using h)

theorem tmFiber49ReverseRow_5_ok :
    tmRowReverseValid tmFiber49Key tmFiber49Expected (tmFiber49RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber49Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber49Chunk2] at h
  exact h.2

theorem tmFiber49ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber49StateAt 1) (tmFiber49StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber49StateAt 1) (tmFiber49StateAt 5)
    (tmFiber49RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber49Key tmFiber49Expected
        (tmFiber49RowAt 5) (by decide) tmFiber49ReverseRow_5_ok
      simpa [tmFiber49StateAt, tmFiber49RowAt, tmFiber49Rows, listGetD, directRow] using h)

theorem tmFiber49ReverseRow_6_ok :
    tmRowReverseValid tmFiber49Key tmFiber49Expected (tmFiber49RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber49Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber49Chunk3] at h
  exact h.1

theorem tmFiber49ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber49StateAt 2) (tmFiber49StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber49StateAt 2) (tmFiber49StateAt 6)
    (tmFiber49RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber49Key tmFiber49Expected
        (tmFiber49RowAt 6) (by decide) tmFiber49ReverseRow_6_ok
      simpa [tmFiber49StateAt, tmFiber49RowAt, tmFiber49Rows, listGetD, directRow] using h)

theorem tmFiber49ReverseRow_7_ok :
    tmRowReverseValid tmFiber49Key tmFiber49Expected (tmFiber49RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber49Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber49Chunk3] at h
  exact h.2

theorem tmFiber49ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber49StateAt 3) (tmFiber49StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber49StateAt 3) (tmFiber49StateAt 7)
    (tmFiber49RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber49Key tmFiber49Expected
        (tmFiber49RowAt 7) (by decide) tmFiber49ReverseRow_7_ok
      simpa [tmFiber49StateAt, tmFiber49RowAt, tmFiber49Rows, listGetD, directRow] using h)

theorem tmFiber49ReverseRow_8_ok :
    tmRowReverseValid tmFiber49Key tmFiber49Expected (tmFiber49RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber49Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber49Chunk4] at h
  exact h.1

theorem tmFiber49ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber49StateAt 4) (tmFiber49StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber49StateAt 4) (tmFiber49StateAt 8)
    (tmFiber49RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber49Key tmFiber49Expected
        (tmFiber49RowAt 8) (by decide) tmFiber49ReverseRow_8_ok
      simpa [tmFiber49StateAt, tmFiber49RowAt, tmFiber49Rows, listGetD, directRow] using h)

theorem tmFiber49ReverseRow_9_ok :
    tmRowReverseValid tmFiber49Key tmFiber49Expected (tmFiber49RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber49Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber49Chunk4] at h
  exact h.2

theorem tmFiber49ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber49StateAt 5) (tmFiber49StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber49StateAt 5) (tmFiber49StateAt 9)
    (tmFiber49RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber49Key tmFiber49Expected
        (tmFiber49RowAt 9) (by decide) tmFiber49ReverseRow_9_ok
      simpa [tmFiber49StateAt, tmFiber49RowAt, tmFiber49Rows, listGetD, directRow] using h)

theorem tmFiber49ReverseRow_10_ok :
    tmRowReverseValid tmFiber49Key tmFiber49Expected (tmFiber49RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber49Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber49Chunk5] at h
  exact h.1

theorem tmFiber49ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber49StateAt 6) (tmFiber49StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber49StateAt 6) (tmFiber49StateAt 10)
    (tmFiber49RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber49Key tmFiber49Expected
        (tmFiber49RowAt 10) (by decide) tmFiber49ReverseRow_10_ok
      simpa [tmFiber49StateAt, tmFiber49RowAt, tmFiber49Rows, listGetD, directRow] using h)

theorem tmFiber49ReverseRow_11_ok :
    tmRowReverseValid tmFiber49Key tmFiber49Expected (tmFiber49RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber49Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber49Chunk5] at h
  exact h.2

theorem tmFiber49ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber49StateAt 7) (tmFiber49StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber49StateAt 7) (tmFiber49StateAt 11)
    (tmFiber49RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber49Key tmFiber49Expected
        (tmFiber49RowAt 11) (by decide) tmFiber49ReverseRow_11_ok
      simpa [tmFiber49StateAt, tmFiber49RowAt, tmFiber49Rows, listGetD, directRow] using h)

theorem tmFiber49ReverseRow_12_ok :
    tmRowReverseValid tmFiber49Key tmFiber49Expected (tmFiber49RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber49Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber49Chunk6] at h
  exact h.1

theorem tmFiber49ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber49StateAt 0) (tmFiber49StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber49StateAt 0) (tmFiber49StateAt 12)
    (tmFiber49RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber49Key tmFiber49Expected
        (tmFiber49RowAt 12) (by decide) tmFiber49ReverseRow_12_ok
      simpa [tmFiber49StateAt, tmFiber49RowAt, tmFiber49Rows, listGetD, directRow] using h)

theorem tmFiber49ReverseRow_13_ok :
    tmRowReverseValid tmFiber49Key tmFiber49Expected (tmFiber49RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber49Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber49Chunk6] at h
  exact h.2

theorem tmFiber49ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber49StateAt 1) (tmFiber49StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber49StateAt 1) (tmFiber49StateAt 13)
    (tmFiber49RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber49Key tmFiber49Expected
        (tmFiber49RowAt 13) (by decide) tmFiber49ReverseRow_13_ok
      simpa [tmFiber49StateAt, tmFiber49RowAt, tmFiber49Rows, listGetD, directRow] using h)

theorem tmFiber49ReverseRow_14_ok :
    tmRowReverseValid tmFiber49Key tmFiber49Expected (tmFiber49RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber49Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber49Chunk7] at h
  exact h.1

theorem tmFiber49ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber49StateAt 2) (tmFiber49StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber49StateAt 2) (tmFiber49StateAt 14)
    (tmFiber49RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber49Key tmFiber49Expected
        (tmFiber49RowAt 14) (by decide) tmFiber49ReverseRow_14_ok
      simpa [tmFiber49StateAt, tmFiber49RowAt, tmFiber49Rows, listGetD, directRow] using h)

theorem tmFiber49ReverseRow_15_ok :
    tmRowReverseValid tmFiber49Key tmFiber49Expected (tmFiber49RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber49Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber49Chunk7] at h
  exact h.2

theorem tmFiber49ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber49StateAt 3) (tmFiber49StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber49StateAt 3) (tmFiber49StateAt 15)
    (tmFiber49RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber49Key tmFiber49Expected
        (tmFiber49RowAt 15) (by decide) tmFiber49ReverseRow_15_ok
      simpa [tmFiber49StateAt, tmFiber49RowAt, tmFiber49Rows, listGetD, directRow] using h)

theorem tmFiber49State0_in_pass1_prefix :
    tmFiber49StateAt 0 ∈ chainClosureStep tmWord [tmFiber49StateAt 0] [tmFiber49StateAt 0] := by
  exact chainClosureStep_mem_of_seen tmWord [tmFiber49StateAt 0] [tmFiber49StateAt 0] (tmFiber49StateAt 0) (by simp)

theorem tmFiber49State1_in_pass1_prefix :
    tmFiber49StateAt 1 ∈ chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1] [tmFiber49StateAt 0] := by
  have hparentBefore :
      tmFiber49StateAt 0 ∈ chainClosureStep tmWord [tmFiber49StateAt 0] [tmFiber49StateAt 0] := by
    exact tmFiber49State0_in_pass1_prefix
  rw [show [tmFiber49StateAt 0, tmFiber49StateAt 1] = [tmFiber49StateAt 0] ++ [tmFiber49StateAt 1] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber49StateAt 1) []
    (chainClosureStep tmWord [tmFiber49StateAt 0] [tmFiber49StateAt 0]) (tmFiber49StateAt 0)
    hparentBefore tmFiber49ReverseSingleStep1

theorem tmFiber49State2_in_pass1_prefix :
    tmFiber49StateAt 2 ∈ chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2] [tmFiber49StateAt 0] := by
  have hparentBefore :
      tmFiber49StateAt 0 ∈ chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1] [tmFiber49StateAt 0] := by
    rw [show [tmFiber49StateAt 0, tmFiber49StateAt 1] = [tmFiber49StateAt 0] ++ [tmFiber49StateAt 1] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber49StateAt 1]
      (chainClosureStep tmWord [tmFiber49StateAt 0] [tmFiber49StateAt 0]) (tmFiber49StateAt 0)
      tmFiber49State0_in_pass1_prefix
  rw [show [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2] = [tmFiber49StateAt 0, tmFiber49StateAt 1] ++ [tmFiber49StateAt 2] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber49StateAt 2) []
    (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1] [tmFiber49StateAt 0]) (tmFiber49StateAt 0)
    hparentBefore tmFiber49ReverseSingleStep2

theorem tmFiber49State3_in_pass1_prefix :
    tmFiber49StateAt 3 ∈ chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3] [tmFiber49StateAt 0] := by
  have hparentBefore :
      tmFiber49StateAt 1 ∈ chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2] [tmFiber49StateAt 0] := by
    rw [show [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2] = [tmFiber49StateAt 0, tmFiber49StateAt 1] ++ [tmFiber49StateAt 2] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber49StateAt 2]
      (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1] [tmFiber49StateAt 0]) (tmFiber49StateAt 1)
      tmFiber49State1_in_pass1_prefix
  rw [show [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3] = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2] ++ [tmFiber49StateAt 3] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber49StateAt 3) []
    (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2] [tmFiber49StateAt 0]) (tmFiber49StateAt 1)
    hparentBefore tmFiber49ReverseSingleStep3

theorem tmFiber49State4_in_pass1_prefix :
    tmFiber49StateAt 4 ∈ chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4] [tmFiber49StateAt 0] := by
  have hparentBefore :
      tmFiber49StateAt 0 ∈ chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3] [tmFiber49StateAt 0] := by
    rw [show [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3] = [tmFiber49StateAt 0] ++ [tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3]
      (chainClosureStep tmWord [tmFiber49StateAt 0] [tmFiber49StateAt 0]) (tmFiber49StateAt 0)
      tmFiber49State0_in_pass1_prefix
  rw [show [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4] = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3] ++ [tmFiber49StateAt 4] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber49StateAt 4) []
    (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3] [tmFiber49StateAt 0]) (tmFiber49StateAt 0)
    hparentBefore tmFiber49ReverseSingleStep4

theorem tmFiber49State5_in_pass1_prefix :
    tmFiber49StateAt 5 ∈ chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5] [tmFiber49StateAt 0] := by
  have hparentBefore :
      tmFiber49StateAt 1 ∈ chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4] [tmFiber49StateAt 0] := by
    rw [show [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4] = [tmFiber49StateAt 0, tmFiber49StateAt 1] ++ [tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4]
      (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1] [tmFiber49StateAt 0]) (tmFiber49StateAt 1)
      tmFiber49State1_in_pass1_prefix
  rw [show [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5] = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4] ++ [tmFiber49StateAt 5] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber49StateAt 5) []
    (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4] [tmFiber49StateAt 0]) (tmFiber49StateAt 1)
    hparentBefore tmFiber49ReverseSingleStep5

theorem tmFiber49State6_in_pass1_prefix :
    tmFiber49StateAt 6 ∈ chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6] [tmFiber49StateAt 0] := by
  have hparentBefore :
      tmFiber49StateAt 2 ∈ chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5] [tmFiber49StateAt 0] := by
    rw [show [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5] = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2] ++ [tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5]
      (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2] [tmFiber49StateAt 0]) (tmFiber49StateAt 2)
      tmFiber49State2_in_pass1_prefix
  rw [show [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6] = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5] ++ [tmFiber49StateAt 6] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber49StateAt 6) []
    (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5] [tmFiber49StateAt 0]) (tmFiber49StateAt 2)
    hparentBefore tmFiber49ReverseSingleStep6

theorem tmFiber49State7_in_pass1_prefix :
    tmFiber49StateAt 7 ∈ chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7] [tmFiber49StateAt 0] := by
  have hparentBefore :
      tmFiber49StateAt 3 ∈ chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6] [tmFiber49StateAt 0] := by
    rw [show [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6] = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3] ++ [tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6]
      (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3] [tmFiber49StateAt 0]) (tmFiber49StateAt 3)
      tmFiber49State3_in_pass1_prefix
  rw [show [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7] = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6] ++ [tmFiber49StateAt 7] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber49StateAt 7) []
    (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6] [tmFiber49StateAt 0]) (tmFiber49StateAt 3)
    hparentBefore tmFiber49ReverseSingleStep7

theorem tmFiber49State8_in_pass1_prefix :
    tmFiber49StateAt 8 ∈ chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8] [tmFiber49StateAt 0] := by
  have hparentBefore :
      tmFiber49StateAt 4 ∈ chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7] [tmFiber49StateAt 0] := by
    rw [show [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7] = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4] ++ [tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7]
      (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4] [tmFiber49StateAt 0]) (tmFiber49StateAt 4)
      tmFiber49State4_in_pass1_prefix
  rw [show [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8] = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7] ++ [tmFiber49StateAt 8] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber49StateAt 8) []
    (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7] [tmFiber49StateAt 0]) (tmFiber49StateAt 4)
    hparentBefore tmFiber49ReverseSingleStep8

theorem tmFiber49State9_in_pass1_prefix :
    tmFiber49StateAt 9 ∈ chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9] [tmFiber49StateAt 0] := by
  have hparentBefore :
      tmFiber49StateAt 5 ∈ chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8] [tmFiber49StateAt 0] := by
    rw [show [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8] = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5] ++ [tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8]
      (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5] [tmFiber49StateAt 0]) (tmFiber49StateAt 5)
      tmFiber49State5_in_pass1_prefix
  rw [show [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9] = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8] ++ [tmFiber49StateAt 9] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber49StateAt 9) []
    (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8] [tmFiber49StateAt 0]) (tmFiber49StateAt 5)
    hparentBefore tmFiber49ReverseSingleStep9

theorem tmFiber49State10_in_pass1_prefix :
    tmFiber49StateAt 10 ∈ chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10] [tmFiber49StateAt 0] := by
  have hparentBefore :
      tmFiber49StateAt 6 ∈ chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9] [tmFiber49StateAt 0] := by
    rw [show [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9] = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6] ++ [tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9]
      (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6] [tmFiber49StateAt 0]) (tmFiber49StateAt 6)
      tmFiber49State6_in_pass1_prefix
  rw [show [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10] = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9] ++ [tmFiber49StateAt 10] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber49StateAt 10) []
    (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9] [tmFiber49StateAt 0]) (tmFiber49StateAt 6)
    hparentBefore tmFiber49ReverseSingleStep10

theorem tmFiber49State11_in_pass1_prefix :
    tmFiber49StateAt 11 ∈ chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11] [tmFiber49StateAt 0] := by
  have hparentBefore :
      tmFiber49StateAt 7 ∈ chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10] [tmFiber49StateAt 0] := by
    rw [show [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10] = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7] ++ [tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10]
      (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7] [tmFiber49StateAt 0]) (tmFiber49StateAt 7)
      tmFiber49State7_in_pass1_prefix
  rw [show [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11] = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10] ++ [tmFiber49StateAt 11] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber49StateAt 11) []
    (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10] [tmFiber49StateAt 0]) (tmFiber49StateAt 7)
    hparentBefore tmFiber49ReverseSingleStep11

theorem tmFiber49State12_in_pass1_prefix :
    tmFiber49StateAt 12 ∈ chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12] [tmFiber49StateAt 0] := by
  have hparentBefore :
      tmFiber49StateAt 0 ∈ chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11] [tmFiber49StateAt 0] := by
    rw [show [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11] = [tmFiber49StateAt 0] ++ [tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11]
      (chainClosureStep tmWord [tmFiber49StateAt 0] [tmFiber49StateAt 0]) (tmFiber49StateAt 0)
      tmFiber49State0_in_pass1_prefix
  rw [show [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12] = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11] ++ [tmFiber49StateAt 12] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber49StateAt 12) []
    (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11] [tmFiber49StateAt 0]) (tmFiber49StateAt 0)
    hparentBefore tmFiber49ReverseSingleStep12

theorem tmFiber49State13_in_pass1_prefix :
    tmFiber49StateAt 13 ∈ chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13] [tmFiber49StateAt 0] := by
  have hparentBefore :
      tmFiber49StateAt 1 ∈ chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12] [tmFiber49StateAt 0] := by
    rw [show [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12] = [tmFiber49StateAt 0, tmFiber49StateAt 1] ++ [tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12]
      (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1] [tmFiber49StateAt 0]) (tmFiber49StateAt 1)
      tmFiber49State1_in_pass1_prefix
  rw [show [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13] = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12] ++ [tmFiber49StateAt 13] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber49StateAt 13) []
    (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12] [tmFiber49StateAt 0]) (tmFiber49StateAt 1)
    hparentBefore tmFiber49ReverseSingleStep13

theorem tmFiber49State14_in_pass1_prefix :
    tmFiber49StateAt 14 ∈ chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14] [tmFiber49StateAt 0] := by
  have hparentBefore :
      tmFiber49StateAt 2 ∈ chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13] [tmFiber49StateAt 0] := by
    rw [show [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13] = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2] ++ [tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13]
      (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2] [tmFiber49StateAt 0]) (tmFiber49StateAt 2)
      tmFiber49State2_in_pass1_prefix
  rw [show [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14] = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13] ++ [tmFiber49StateAt 14] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber49StateAt 14) []
    (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13] [tmFiber49StateAt 0]) (tmFiber49StateAt 2)
    hparentBefore tmFiber49ReverseSingleStep14

theorem tmFiber49State15_in_pass1_prefix :
    tmFiber49StateAt 15 ∈ chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14, tmFiber49StateAt 15] [tmFiber49StateAt 0] := by
  have hparentBefore :
      tmFiber49StateAt 3 ∈ chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14] [tmFiber49StateAt 0] := by
    rw [show [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14] = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3] ++ [tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14]
      (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3] [tmFiber49StateAt 0]) (tmFiber49StateAt 3)
      tmFiber49State3_in_pass1_prefix
  rw [show [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14, tmFiber49StateAt 15] = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14] ++ [tmFiber49StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber49StateAt 15) []
    (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14] [tmFiber49StateAt 0]) (tmFiber49StateAt 3)
    hparentBefore tmFiber49ReverseSingleStep15

theorem tmFiber49State0_in_pass1_full :
    tmFiber49StateAt 0 ∈ chainClosureStep tmWord tmFiber49DirectStates [tmFiber49StateAt 0] := by
  rw [show tmFiber49DirectStates = [tmFiber49StateAt 0] ++ [tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14, tmFiber49StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14, tmFiber49StateAt 15]
    (chainClosureStep tmWord [tmFiber49StateAt 0] [tmFiber49StateAt 0]) (tmFiber49StateAt 0)
    tmFiber49State0_in_pass1_prefix

theorem tmFiber49State1_in_pass1_full :
    tmFiber49StateAt 1 ∈ chainClosureStep tmWord tmFiber49DirectStates [tmFiber49StateAt 0] := by
  rw [show tmFiber49DirectStates = [tmFiber49StateAt 0, tmFiber49StateAt 1] ++ [tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14, tmFiber49StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14, tmFiber49StateAt 15]
    (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1] [tmFiber49StateAt 0]) (tmFiber49StateAt 1)
    tmFiber49State1_in_pass1_prefix

theorem tmFiber49State2_in_pass1_full :
    tmFiber49StateAt 2 ∈ chainClosureStep tmWord tmFiber49DirectStates [tmFiber49StateAt 0] := by
  rw [show tmFiber49DirectStates = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2] ++ [tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14, tmFiber49StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14, tmFiber49StateAt 15]
    (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2] [tmFiber49StateAt 0]) (tmFiber49StateAt 2)
    tmFiber49State2_in_pass1_prefix

theorem tmFiber49State3_in_pass1_full :
    tmFiber49StateAt 3 ∈ chainClosureStep tmWord tmFiber49DirectStates [tmFiber49StateAt 0] := by
  rw [show tmFiber49DirectStates = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3] ++ [tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14, tmFiber49StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14, tmFiber49StateAt 15]
    (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3] [tmFiber49StateAt 0]) (tmFiber49StateAt 3)
    tmFiber49State3_in_pass1_prefix

theorem tmFiber49State4_in_pass1_full :
    tmFiber49StateAt 4 ∈ chainClosureStep tmWord tmFiber49DirectStates [tmFiber49StateAt 0] := by
  rw [show tmFiber49DirectStates = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4] ++ [tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14, tmFiber49StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14, tmFiber49StateAt 15]
    (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4] [tmFiber49StateAt 0]) (tmFiber49StateAt 4)
    tmFiber49State4_in_pass1_prefix

theorem tmFiber49State5_in_pass1_full :
    tmFiber49StateAt 5 ∈ chainClosureStep tmWord tmFiber49DirectStates [tmFiber49StateAt 0] := by
  rw [show tmFiber49DirectStates = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5] ++ [tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14, tmFiber49StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14, tmFiber49StateAt 15]
    (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5] [tmFiber49StateAt 0]) (tmFiber49StateAt 5)
    tmFiber49State5_in_pass1_prefix

theorem tmFiber49State6_in_pass1_full :
    tmFiber49StateAt 6 ∈ chainClosureStep tmWord tmFiber49DirectStates [tmFiber49StateAt 0] := by
  rw [show tmFiber49DirectStates = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6] ++ [tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14, tmFiber49StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14, tmFiber49StateAt 15]
    (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6] [tmFiber49StateAt 0]) (tmFiber49StateAt 6)
    tmFiber49State6_in_pass1_prefix

theorem tmFiber49State7_in_pass1_full :
    tmFiber49StateAt 7 ∈ chainClosureStep tmWord tmFiber49DirectStates [tmFiber49StateAt 0] := by
  rw [show tmFiber49DirectStates = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7] ++ [tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14, tmFiber49StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14, tmFiber49StateAt 15]
    (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7] [tmFiber49StateAt 0]) (tmFiber49StateAt 7)
    tmFiber49State7_in_pass1_prefix

theorem tmFiber49State8_in_pass1_full :
    tmFiber49StateAt 8 ∈ chainClosureStep tmWord tmFiber49DirectStates [tmFiber49StateAt 0] := by
  rw [show tmFiber49DirectStates = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8] ++ [tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14, tmFiber49StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14, tmFiber49StateAt 15]
    (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8] [tmFiber49StateAt 0]) (tmFiber49StateAt 8)
    tmFiber49State8_in_pass1_prefix

theorem tmFiber49State9_in_pass1_full :
    tmFiber49StateAt 9 ∈ chainClosureStep tmWord tmFiber49DirectStates [tmFiber49StateAt 0] := by
  rw [show tmFiber49DirectStates = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9] ++ [tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14, tmFiber49StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14, tmFiber49StateAt 15]
    (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9] [tmFiber49StateAt 0]) (tmFiber49StateAt 9)
    tmFiber49State9_in_pass1_prefix

theorem tmFiber49State10_in_pass1_full :
    tmFiber49StateAt 10 ∈ chainClosureStep tmWord tmFiber49DirectStates [tmFiber49StateAt 0] := by
  rw [show tmFiber49DirectStates = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10] ++ [tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14, tmFiber49StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14, tmFiber49StateAt 15]
    (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10] [tmFiber49StateAt 0]) (tmFiber49StateAt 10)
    tmFiber49State10_in_pass1_prefix

theorem tmFiber49State11_in_pass1_full :
    tmFiber49StateAt 11 ∈ chainClosureStep tmWord tmFiber49DirectStates [tmFiber49StateAt 0] := by
  rw [show tmFiber49DirectStates = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11] ++ [tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14, tmFiber49StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14, tmFiber49StateAt 15]
    (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11] [tmFiber49StateAt 0]) (tmFiber49StateAt 11)
    tmFiber49State11_in_pass1_prefix

theorem tmFiber49State12_in_pass1_full :
    tmFiber49StateAt 12 ∈ chainClosureStep tmWord tmFiber49DirectStates [tmFiber49StateAt 0] := by
  rw [show tmFiber49DirectStates = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12] ++ [tmFiber49StateAt 13, tmFiber49StateAt 14, tmFiber49StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber49StateAt 13, tmFiber49StateAt 14, tmFiber49StateAt 15]
    (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12] [tmFiber49StateAt 0]) (tmFiber49StateAt 12)
    tmFiber49State12_in_pass1_prefix

theorem tmFiber49State13_in_pass1_full :
    tmFiber49StateAt 13 ∈ chainClosureStep tmWord tmFiber49DirectStates [tmFiber49StateAt 0] := by
  rw [show tmFiber49DirectStates = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13] ++ [tmFiber49StateAt 14, tmFiber49StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber49StateAt 14, tmFiber49StateAt 15]
    (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13] [tmFiber49StateAt 0]) (tmFiber49StateAt 13)
    tmFiber49State13_in_pass1_prefix

theorem tmFiber49State14_in_pass1_full :
    tmFiber49StateAt 14 ∈ chainClosureStep tmWord tmFiber49DirectStates [tmFiber49StateAt 0] := by
  rw [show tmFiber49DirectStates = [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14] ++ [tmFiber49StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber49StateAt 15]
    (chainClosureStep tmWord [tmFiber49StateAt 0, tmFiber49StateAt 1, tmFiber49StateAt 2, tmFiber49StateAt 3, tmFiber49StateAt 4, tmFiber49StateAt 5, tmFiber49StateAt 6, tmFiber49StateAt 7, tmFiber49StateAt 8, tmFiber49StateAt 9, tmFiber49StateAt 10, tmFiber49StateAt 11, tmFiber49StateAt 12, tmFiber49StateAt 13, tmFiber49StateAt 14] [tmFiber49StateAt 0]) (tmFiber49StateAt 14)
    tmFiber49State14_in_pass1_prefix

theorem tmFiber49State15_in_pass1_full :
    tmFiber49StateAt 15 ∈ chainClosureStep tmWord tmFiber49DirectStates [tmFiber49StateAt 0] := by
  simpa [tmFiber49DirectStates] using tmFiber49State15_in_pass1_prefix

theorem tmFiber49State0_in_close :
    tmFiber49StateAt 0 ∈ closeChainFiber tmWord tmFiber49DirectStates tmFiber49DirectStates.length [tmFiber49StateAt 0] := by
  change tmFiber49StateAt 0 ∈ closeChainFiber tmWord tmFiber49DirectStates (15 + 1) [tmFiber49StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber49DirectStates 15 [tmFiber49StateAt 0] (tmFiber49StateAt 0) tmFiber49State0_in_pass1_full

theorem tmFiber49State1_in_close :
    tmFiber49StateAt 1 ∈ closeChainFiber tmWord tmFiber49DirectStates tmFiber49DirectStates.length [tmFiber49StateAt 0] := by
  change tmFiber49StateAt 1 ∈ closeChainFiber tmWord tmFiber49DirectStates (15 + 1) [tmFiber49StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber49DirectStates 15 [tmFiber49StateAt 0] (tmFiber49StateAt 1) tmFiber49State1_in_pass1_full

theorem tmFiber49State2_in_close :
    tmFiber49StateAt 2 ∈ closeChainFiber tmWord tmFiber49DirectStates tmFiber49DirectStates.length [tmFiber49StateAt 0] := by
  change tmFiber49StateAt 2 ∈ closeChainFiber tmWord tmFiber49DirectStates (15 + 1) [tmFiber49StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber49DirectStates 15 [tmFiber49StateAt 0] (tmFiber49StateAt 2) tmFiber49State2_in_pass1_full

theorem tmFiber49State3_in_close :
    tmFiber49StateAt 3 ∈ closeChainFiber tmWord tmFiber49DirectStates tmFiber49DirectStates.length [tmFiber49StateAt 0] := by
  change tmFiber49StateAt 3 ∈ closeChainFiber tmWord tmFiber49DirectStates (15 + 1) [tmFiber49StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber49DirectStates 15 [tmFiber49StateAt 0] (tmFiber49StateAt 3) tmFiber49State3_in_pass1_full

theorem tmFiber49State4_in_close :
    tmFiber49StateAt 4 ∈ closeChainFiber tmWord tmFiber49DirectStates tmFiber49DirectStates.length [tmFiber49StateAt 0] := by
  change tmFiber49StateAt 4 ∈ closeChainFiber tmWord tmFiber49DirectStates (15 + 1) [tmFiber49StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber49DirectStates 15 [tmFiber49StateAt 0] (tmFiber49StateAt 4) tmFiber49State4_in_pass1_full

theorem tmFiber49State5_in_close :
    tmFiber49StateAt 5 ∈ closeChainFiber tmWord tmFiber49DirectStates tmFiber49DirectStates.length [tmFiber49StateAt 0] := by
  change tmFiber49StateAt 5 ∈ closeChainFiber tmWord tmFiber49DirectStates (15 + 1) [tmFiber49StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber49DirectStates 15 [tmFiber49StateAt 0] (tmFiber49StateAt 5) tmFiber49State5_in_pass1_full

theorem tmFiber49State6_in_close :
    tmFiber49StateAt 6 ∈ closeChainFiber tmWord tmFiber49DirectStates tmFiber49DirectStates.length [tmFiber49StateAt 0] := by
  change tmFiber49StateAt 6 ∈ closeChainFiber tmWord tmFiber49DirectStates (15 + 1) [tmFiber49StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber49DirectStates 15 [tmFiber49StateAt 0] (tmFiber49StateAt 6) tmFiber49State6_in_pass1_full

theorem tmFiber49State7_in_close :
    tmFiber49StateAt 7 ∈ closeChainFiber tmWord tmFiber49DirectStates tmFiber49DirectStates.length [tmFiber49StateAt 0] := by
  change tmFiber49StateAt 7 ∈ closeChainFiber tmWord tmFiber49DirectStates (15 + 1) [tmFiber49StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber49DirectStates 15 [tmFiber49StateAt 0] (tmFiber49StateAt 7) tmFiber49State7_in_pass1_full

theorem tmFiber49State8_in_close :
    tmFiber49StateAt 8 ∈ closeChainFiber tmWord tmFiber49DirectStates tmFiber49DirectStates.length [tmFiber49StateAt 0] := by
  change tmFiber49StateAt 8 ∈ closeChainFiber tmWord tmFiber49DirectStates (15 + 1) [tmFiber49StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber49DirectStates 15 [tmFiber49StateAt 0] (tmFiber49StateAt 8) tmFiber49State8_in_pass1_full

theorem tmFiber49State9_in_close :
    tmFiber49StateAt 9 ∈ closeChainFiber tmWord tmFiber49DirectStates tmFiber49DirectStates.length [tmFiber49StateAt 0] := by
  change tmFiber49StateAt 9 ∈ closeChainFiber tmWord tmFiber49DirectStates (15 + 1) [tmFiber49StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber49DirectStates 15 [tmFiber49StateAt 0] (tmFiber49StateAt 9) tmFiber49State9_in_pass1_full

theorem tmFiber49State10_in_close :
    tmFiber49StateAt 10 ∈ closeChainFiber tmWord tmFiber49DirectStates tmFiber49DirectStates.length [tmFiber49StateAt 0] := by
  change tmFiber49StateAt 10 ∈ closeChainFiber tmWord tmFiber49DirectStates (15 + 1) [tmFiber49StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber49DirectStates 15 [tmFiber49StateAt 0] (tmFiber49StateAt 10) tmFiber49State10_in_pass1_full

theorem tmFiber49State11_in_close :
    tmFiber49StateAt 11 ∈ closeChainFiber tmWord tmFiber49DirectStates tmFiber49DirectStates.length [tmFiber49StateAt 0] := by
  change tmFiber49StateAt 11 ∈ closeChainFiber tmWord tmFiber49DirectStates (15 + 1) [tmFiber49StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber49DirectStates 15 [tmFiber49StateAt 0] (tmFiber49StateAt 11) tmFiber49State11_in_pass1_full

theorem tmFiber49State12_in_close :
    tmFiber49StateAt 12 ∈ closeChainFiber tmWord tmFiber49DirectStates tmFiber49DirectStates.length [tmFiber49StateAt 0] := by
  change tmFiber49StateAt 12 ∈ closeChainFiber tmWord tmFiber49DirectStates (15 + 1) [tmFiber49StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber49DirectStates 15 [tmFiber49StateAt 0] (tmFiber49StateAt 12) tmFiber49State12_in_pass1_full

theorem tmFiber49State13_in_close :
    tmFiber49StateAt 13 ∈ closeChainFiber tmWord tmFiber49DirectStates tmFiber49DirectStates.length [tmFiber49StateAt 0] := by
  change tmFiber49StateAt 13 ∈ closeChainFiber tmWord tmFiber49DirectStates (15 + 1) [tmFiber49StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber49DirectStates 15 [tmFiber49StateAt 0] (tmFiber49StateAt 13) tmFiber49State13_in_pass1_full

theorem tmFiber49State14_in_close :
    tmFiber49StateAt 14 ∈ closeChainFiber tmWord tmFiber49DirectStates tmFiber49DirectStates.length [tmFiber49StateAt 0] := by
  change tmFiber49StateAt 14 ∈ closeChainFiber tmWord tmFiber49DirectStates (15 + 1) [tmFiber49StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber49DirectStates 15 [tmFiber49StateAt 0] (tmFiber49StateAt 14) tmFiber49State14_in_pass1_full

theorem tmFiber49State15_in_close :
    tmFiber49StateAt 15 ∈ closeChainFiber tmWord tmFiber49DirectStates tmFiber49DirectStates.length [tmFiber49StateAt 0] := by
  change tmFiber49StateAt 15 ∈ closeChainFiber tmWord tmFiber49DirectStates (15 + 1) [tmFiber49StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber49DirectStates 15 [tmFiber49StateAt 0] (tmFiber49StateAt 15) tmFiber49State15_in_pass1_full

theorem tmFiber49DirectConnected :
    chainFiberConnected tmWord tmFiber49DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber49DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber49State0_in_close
  · subst state
    exact tmFiber49State1_in_close
  · subst state
    exact tmFiber49State2_in_close
  · subst state
    exact tmFiber49State3_in_close
  · subst state
    exact tmFiber49State4_in_close
  · subst state
    exact tmFiber49State5_in_close
  · subst state
    exact tmFiber49State6_in_close
  · subst state
    exact tmFiber49State7_in_close
  · subst state
    exact tmFiber49State8_in_close
  · subst state
    exact tmFiber49State9_in_close
  · subst state
    exact tmFiber49State10_in_close
  · subst state
    exact tmFiber49State11_in_close
  · subst state
    exact tmFiber49State12_in_close
  · subst state
    exact tmFiber49State13_in_close
  · subst state
    exact tmFiber49State14_in_close
  · subst state
    exact tmFiber49State15_in_close
  · cases h

end GoertzelLemma818LengthTwoTMShape16Bridge

end Mettapedia.GraphTheory.FourColor
