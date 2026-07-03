import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for size-16 `normal,mirror` length-two fibers, group 4

This module proves direct connectedness for four generated `normal,mirror`
size-16 fibers from row-local reverse certificate chunks, keeping Lean on
default recursion limits.
-/

namespace GoertzelLemma818LengthTwoTMShape16Bridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818TauMirrorCertificate
open GoertzelLemma818TauMirrorReverseAudit

def tmFiber61StateAt (i : Nat) : List TauState :=
  directStates (tmFiber61RowAt i).sourceLeft (tmFiber61RowAt i).sourceRight

def tmFiber61DirectStates : List (List TauState) :=
  [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14, tmFiber61StateAt 15]

theorem tmFiber61ReverseRow_1_ok :
    tmRowReverseValid tmFiber61Key tmFiber61Expected (tmFiber61RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber61Chunk0_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber61Chunk0] at h
  exact h.2

theorem tmFiber61ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber61StateAt 0) (tmFiber61StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber61StateAt 0) (tmFiber61StateAt 1)
    (tmFiber61RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber61Key tmFiber61Expected
        (tmFiber61RowAt 1) (by decide) tmFiber61ReverseRow_1_ok
      simpa [tmFiber61StateAt, tmFiber61RowAt, tmFiber61Rows, listGetD, directRow] using h)

theorem tmFiber61ReverseRow_2_ok :
    tmRowReverseValid tmFiber61Key tmFiber61Expected (tmFiber61RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber61Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber61Chunk1] at h
  exact h.1

theorem tmFiber61ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber61StateAt 0) (tmFiber61StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber61StateAt 0) (tmFiber61StateAt 2)
    (tmFiber61RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber61Key tmFiber61Expected
        (tmFiber61RowAt 2) (by decide) tmFiber61ReverseRow_2_ok
      simpa [tmFiber61StateAt, tmFiber61RowAt, tmFiber61Rows, listGetD, directRow] using h)

theorem tmFiber61ReverseRow_3_ok :
    tmRowReverseValid tmFiber61Key tmFiber61Expected (tmFiber61RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber61Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber61Chunk1] at h
  exact h.2

theorem tmFiber61ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber61StateAt 1) (tmFiber61StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber61StateAt 1) (tmFiber61StateAt 3)
    (tmFiber61RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber61Key tmFiber61Expected
        (tmFiber61RowAt 3) (by decide) tmFiber61ReverseRow_3_ok
      simpa [tmFiber61StateAt, tmFiber61RowAt, tmFiber61Rows, listGetD, directRow] using h)

theorem tmFiber61ReverseRow_4_ok :
    tmRowReverseValid tmFiber61Key tmFiber61Expected (tmFiber61RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber61Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber61Chunk2] at h
  exact h.1

theorem tmFiber61ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber61StateAt 0) (tmFiber61StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber61StateAt 0) (tmFiber61StateAt 4)
    (tmFiber61RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber61Key tmFiber61Expected
        (tmFiber61RowAt 4) (by decide) tmFiber61ReverseRow_4_ok
      simpa [tmFiber61StateAt, tmFiber61RowAt, tmFiber61Rows, listGetD, directRow] using h)

theorem tmFiber61ReverseRow_5_ok :
    tmRowReverseValid tmFiber61Key tmFiber61Expected (tmFiber61RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber61Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber61Chunk2] at h
  exact h.2

theorem tmFiber61ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber61StateAt 1) (tmFiber61StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber61StateAt 1) (tmFiber61StateAt 5)
    (tmFiber61RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber61Key tmFiber61Expected
        (tmFiber61RowAt 5) (by decide) tmFiber61ReverseRow_5_ok
      simpa [tmFiber61StateAt, tmFiber61RowAt, tmFiber61Rows, listGetD, directRow] using h)

theorem tmFiber61ReverseRow_6_ok :
    tmRowReverseValid tmFiber61Key tmFiber61Expected (tmFiber61RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber61Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber61Chunk3] at h
  exact h.1

theorem tmFiber61ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber61StateAt 2) (tmFiber61StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber61StateAt 2) (tmFiber61StateAt 6)
    (tmFiber61RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber61Key tmFiber61Expected
        (tmFiber61RowAt 6) (by decide) tmFiber61ReverseRow_6_ok
      simpa [tmFiber61StateAt, tmFiber61RowAt, tmFiber61Rows, listGetD, directRow] using h)

theorem tmFiber61ReverseRow_7_ok :
    tmRowReverseValid tmFiber61Key tmFiber61Expected (tmFiber61RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber61Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber61Chunk3] at h
  exact h.2

theorem tmFiber61ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber61StateAt 3) (tmFiber61StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber61StateAt 3) (tmFiber61StateAt 7)
    (tmFiber61RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber61Key tmFiber61Expected
        (tmFiber61RowAt 7) (by decide) tmFiber61ReverseRow_7_ok
      simpa [tmFiber61StateAt, tmFiber61RowAt, tmFiber61Rows, listGetD, directRow] using h)

theorem tmFiber61ReverseRow_8_ok :
    tmRowReverseValid tmFiber61Key tmFiber61Expected (tmFiber61RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber61Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber61Chunk4] at h
  exact h.1

theorem tmFiber61ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber61StateAt 4) (tmFiber61StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber61StateAt 4) (tmFiber61StateAt 8)
    (tmFiber61RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber61Key tmFiber61Expected
        (tmFiber61RowAt 8) (by decide) tmFiber61ReverseRow_8_ok
      simpa [tmFiber61StateAt, tmFiber61RowAt, tmFiber61Rows, listGetD, directRow] using h)

theorem tmFiber61ReverseRow_9_ok :
    tmRowReverseValid tmFiber61Key tmFiber61Expected (tmFiber61RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber61Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber61Chunk4] at h
  exact h.2

theorem tmFiber61ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber61StateAt 5) (tmFiber61StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber61StateAt 5) (tmFiber61StateAt 9)
    (tmFiber61RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber61Key tmFiber61Expected
        (tmFiber61RowAt 9) (by decide) tmFiber61ReverseRow_9_ok
      simpa [tmFiber61StateAt, tmFiber61RowAt, tmFiber61Rows, listGetD, directRow] using h)

theorem tmFiber61ReverseRow_10_ok :
    tmRowReverseValid tmFiber61Key tmFiber61Expected (tmFiber61RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber61Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber61Chunk5] at h
  exact h.1

theorem tmFiber61ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber61StateAt 6) (tmFiber61StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber61StateAt 6) (tmFiber61StateAt 10)
    (tmFiber61RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber61Key tmFiber61Expected
        (tmFiber61RowAt 10) (by decide) tmFiber61ReverseRow_10_ok
      simpa [tmFiber61StateAt, tmFiber61RowAt, tmFiber61Rows, listGetD, directRow] using h)

theorem tmFiber61ReverseRow_11_ok :
    tmRowReverseValid tmFiber61Key tmFiber61Expected (tmFiber61RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber61Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber61Chunk5] at h
  exact h.2

theorem tmFiber61ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber61StateAt 7) (tmFiber61StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber61StateAt 7) (tmFiber61StateAt 11)
    (tmFiber61RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber61Key tmFiber61Expected
        (tmFiber61RowAt 11) (by decide) tmFiber61ReverseRow_11_ok
      simpa [tmFiber61StateAt, tmFiber61RowAt, tmFiber61Rows, listGetD, directRow] using h)

theorem tmFiber61ReverseRow_12_ok :
    tmRowReverseValid tmFiber61Key tmFiber61Expected (tmFiber61RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber61Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber61Chunk6] at h
  exact h.1

theorem tmFiber61ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber61StateAt 0) (tmFiber61StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber61StateAt 0) (tmFiber61StateAt 12)
    (tmFiber61RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber61Key tmFiber61Expected
        (tmFiber61RowAt 12) (by decide) tmFiber61ReverseRow_12_ok
      simpa [tmFiber61StateAt, tmFiber61RowAt, tmFiber61Rows, listGetD, directRow] using h)

theorem tmFiber61ReverseRow_13_ok :
    tmRowReverseValid tmFiber61Key tmFiber61Expected (tmFiber61RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber61Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber61Chunk6] at h
  exact h.2

theorem tmFiber61ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber61StateAt 1) (tmFiber61StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber61StateAt 1) (tmFiber61StateAt 13)
    (tmFiber61RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber61Key tmFiber61Expected
        (tmFiber61RowAt 13) (by decide) tmFiber61ReverseRow_13_ok
      simpa [tmFiber61StateAt, tmFiber61RowAt, tmFiber61Rows, listGetD, directRow] using h)

theorem tmFiber61ReverseRow_14_ok :
    tmRowReverseValid tmFiber61Key tmFiber61Expected (tmFiber61RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber61Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber61Chunk7] at h
  exact h.1

theorem tmFiber61ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber61StateAt 2) (tmFiber61StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber61StateAt 2) (tmFiber61StateAt 14)
    (tmFiber61RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber61Key tmFiber61Expected
        (tmFiber61RowAt 14) (by decide) tmFiber61ReverseRow_14_ok
      simpa [tmFiber61StateAt, tmFiber61RowAt, tmFiber61Rows, listGetD, directRow] using h)

theorem tmFiber61ReverseRow_15_ok :
    tmRowReverseValid tmFiber61Key tmFiber61Expected (tmFiber61RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber61Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber61Chunk7] at h
  exact h.2

theorem tmFiber61ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber61StateAt 3) (tmFiber61StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber61StateAt 3) (tmFiber61StateAt 15)
    (tmFiber61RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber61Key tmFiber61Expected
        (tmFiber61RowAt 15) (by decide) tmFiber61ReverseRow_15_ok
      simpa [tmFiber61StateAt, tmFiber61RowAt, tmFiber61Rows, listGetD, directRow] using h)

theorem tmFiber61State0_in_pass1_prefix :
    tmFiber61StateAt 0 ∈ chainClosureStep tmWord [tmFiber61StateAt 0] [tmFiber61StateAt 0] := by
  exact chainClosureStep_mem_of_seen tmWord [tmFiber61StateAt 0] [tmFiber61StateAt 0] (tmFiber61StateAt 0) (by simp)

theorem tmFiber61State1_in_pass1_prefix :
    tmFiber61StateAt 1 ∈ chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1] [tmFiber61StateAt 0] := by
  have hparentBefore :
      tmFiber61StateAt 0 ∈ chainClosureStep tmWord [tmFiber61StateAt 0] [tmFiber61StateAt 0] := by
    exact tmFiber61State0_in_pass1_prefix
  rw [show [tmFiber61StateAt 0, tmFiber61StateAt 1] = [tmFiber61StateAt 0] ++ [tmFiber61StateAt 1] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber61StateAt 1) []
    (chainClosureStep tmWord [tmFiber61StateAt 0] [tmFiber61StateAt 0]) (tmFiber61StateAt 0)
    hparentBefore tmFiber61ReverseSingleStep1

theorem tmFiber61State2_in_pass1_prefix :
    tmFiber61StateAt 2 ∈ chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2] [tmFiber61StateAt 0] := by
  have hparentBefore :
      tmFiber61StateAt 0 ∈ chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1] [tmFiber61StateAt 0] := by
    rw [show [tmFiber61StateAt 0, tmFiber61StateAt 1] = [tmFiber61StateAt 0] ++ [tmFiber61StateAt 1] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber61StateAt 1]
      (chainClosureStep tmWord [tmFiber61StateAt 0] [tmFiber61StateAt 0]) (tmFiber61StateAt 0)
      tmFiber61State0_in_pass1_prefix
  rw [show [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2] = [tmFiber61StateAt 0, tmFiber61StateAt 1] ++ [tmFiber61StateAt 2] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber61StateAt 2) []
    (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1] [tmFiber61StateAt 0]) (tmFiber61StateAt 0)
    hparentBefore tmFiber61ReverseSingleStep2

theorem tmFiber61State3_in_pass1_prefix :
    tmFiber61StateAt 3 ∈ chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3] [tmFiber61StateAt 0] := by
  have hparentBefore :
      tmFiber61StateAt 1 ∈ chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2] [tmFiber61StateAt 0] := by
    rw [show [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2] = [tmFiber61StateAt 0, tmFiber61StateAt 1] ++ [tmFiber61StateAt 2] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber61StateAt 2]
      (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1] [tmFiber61StateAt 0]) (tmFiber61StateAt 1)
      tmFiber61State1_in_pass1_prefix
  rw [show [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3] = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2] ++ [tmFiber61StateAt 3] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber61StateAt 3) []
    (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2] [tmFiber61StateAt 0]) (tmFiber61StateAt 1)
    hparentBefore tmFiber61ReverseSingleStep3

theorem tmFiber61State4_in_pass1_prefix :
    tmFiber61StateAt 4 ∈ chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4] [tmFiber61StateAt 0] := by
  have hparentBefore :
      tmFiber61StateAt 0 ∈ chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3] [tmFiber61StateAt 0] := by
    rw [show [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3] = [tmFiber61StateAt 0] ++ [tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3]
      (chainClosureStep tmWord [tmFiber61StateAt 0] [tmFiber61StateAt 0]) (tmFiber61StateAt 0)
      tmFiber61State0_in_pass1_prefix
  rw [show [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4] = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3] ++ [tmFiber61StateAt 4] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber61StateAt 4) []
    (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3] [tmFiber61StateAt 0]) (tmFiber61StateAt 0)
    hparentBefore tmFiber61ReverseSingleStep4

theorem tmFiber61State5_in_pass1_prefix :
    tmFiber61StateAt 5 ∈ chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5] [tmFiber61StateAt 0] := by
  have hparentBefore :
      tmFiber61StateAt 1 ∈ chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4] [tmFiber61StateAt 0] := by
    rw [show [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4] = [tmFiber61StateAt 0, tmFiber61StateAt 1] ++ [tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4]
      (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1] [tmFiber61StateAt 0]) (tmFiber61StateAt 1)
      tmFiber61State1_in_pass1_prefix
  rw [show [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5] = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4] ++ [tmFiber61StateAt 5] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber61StateAt 5) []
    (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4] [tmFiber61StateAt 0]) (tmFiber61StateAt 1)
    hparentBefore tmFiber61ReverseSingleStep5

theorem tmFiber61State6_in_pass1_prefix :
    tmFiber61StateAt 6 ∈ chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6] [tmFiber61StateAt 0] := by
  have hparentBefore :
      tmFiber61StateAt 2 ∈ chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5] [tmFiber61StateAt 0] := by
    rw [show [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5] = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2] ++ [tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5]
      (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2] [tmFiber61StateAt 0]) (tmFiber61StateAt 2)
      tmFiber61State2_in_pass1_prefix
  rw [show [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6] = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5] ++ [tmFiber61StateAt 6] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber61StateAt 6) []
    (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5] [tmFiber61StateAt 0]) (tmFiber61StateAt 2)
    hparentBefore tmFiber61ReverseSingleStep6

theorem tmFiber61State7_in_pass1_prefix :
    tmFiber61StateAt 7 ∈ chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7] [tmFiber61StateAt 0] := by
  have hparentBefore :
      tmFiber61StateAt 3 ∈ chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6] [tmFiber61StateAt 0] := by
    rw [show [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6] = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3] ++ [tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6]
      (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3] [tmFiber61StateAt 0]) (tmFiber61StateAt 3)
      tmFiber61State3_in_pass1_prefix
  rw [show [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7] = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6] ++ [tmFiber61StateAt 7] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber61StateAt 7) []
    (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6] [tmFiber61StateAt 0]) (tmFiber61StateAt 3)
    hparentBefore tmFiber61ReverseSingleStep7

theorem tmFiber61State8_in_pass1_prefix :
    tmFiber61StateAt 8 ∈ chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8] [tmFiber61StateAt 0] := by
  have hparentBefore :
      tmFiber61StateAt 4 ∈ chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7] [tmFiber61StateAt 0] := by
    rw [show [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7] = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4] ++ [tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7]
      (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4] [tmFiber61StateAt 0]) (tmFiber61StateAt 4)
      tmFiber61State4_in_pass1_prefix
  rw [show [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8] = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7] ++ [tmFiber61StateAt 8] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber61StateAt 8) []
    (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7] [tmFiber61StateAt 0]) (tmFiber61StateAt 4)
    hparentBefore tmFiber61ReverseSingleStep8

theorem tmFiber61State9_in_pass1_prefix :
    tmFiber61StateAt 9 ∈ chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9] [tmFiber61StateAt 0] := by
  have hparentBefore :
      tmFiber61StateAt 5 ∈ chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8] [tmFiber61StateAt 0] := by
    rw [show [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8] = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5] ++ [tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8]
      (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5] [tmFiber61StateAt 0]) (tmFiber61StateAt 5)
      tmFiber61State5_in_pass1_prefix
  rw [show [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9] = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8] ++ [tmFiber61StateAt 9] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber61StateAt 9) []
    (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8] [tmFiber61StateAt 0]) (tmFiber61StateAt 5)
    hparentBefore tmFiber61ReverseSingleStep9

theorem tmFiber61State10_in_pass1_prefix :
    tmFiber61StateAt 10 ∈ chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10] [tmFiber61StateAt 0] := by
  have hparentBefore :
      tmFiber61StateAt 6 ∈ chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9] [tmFiber61StateAt 0] := by
    rw [show [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9] = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6] ++ [tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9]
      (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6] [tmFiber61StateAt 0]) (tmFiber61StateAt 6)
      tmFiber61State6_in_pass1_prefix
  rw [show [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10] = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9] ++ [tmFiber61StateAt 10] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber61StateAt 10) []
    (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9] [tmFiber61StateAt 0]) (tmFiber61StateAt 6)
    hparentBefore tmFiber61ReverseSingleStep10

theorem tmFiber61State11_in_pass1_prefix :
    tmFiber61StateAt 11 ∈ chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11] [tmFiber61StateAt 0] := by
  have hparentBefore :
      tmFiber61StateAt 7 ∈ chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10] [tmFiber61StateAt 0] := by
    rw [show [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10] = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7] ++ [tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10]
      (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7] [tmFiber61StateAt 0]) (tmFiber61StateAt 7)
      tmFiber61State7_in_pass1_prefix
  rw [show [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11] = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10] ++ [tmFiber61StateAt 11] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber61StateAt 11) []
    (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10] [tmFiber61StateAt 0]) (tmFiber61StateAt 7)
    hparentBefore tmFiber61ReverseSingleStep11

theorem tmFiber61State12_in_pass1_prefix :
    tmFiber61StateAt 12 ∈ chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12] [tmFiber61StateAt 0] := by
  have hparentBefore :
      tmFiber61StateAt 0 ∈ chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11] [tmFiber61StateAt 0] := by
    rw [show [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11] = [tmFiber61StateAt 0] ++ [tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11]
      (chainClosureStep tmWord [tmFiber61StateAt 0] [tmFiber61StateAt 0]) (tmFiber61StateAt 0)
      tmFiber61State0_in_pass1_prefix
  rw [show [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12] = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11] ++ [tmFiber61StateAt 12] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber61StateAt 12) []
    (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11] [tmFiber61StateAt 0]) (tmFiber61StateAt 0)
    hparentBefore tmFiber61ReverseSingleStep12

theorem tmFiber61State13_in_pass1_prefix :
    tmFiber61StateAt 13 ∈ chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13] [tmFiber61StateAt 0] := by
  have hparentBefore :
      tmFiber61StateAt 1 ∈ chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12] [tmFiber61StateAt 0] := by
    rw [show [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12] = [tmFiber61StateAt 0, tmFiber61StateAt 1] ++ [tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12]
      (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1] [tmFiber61StateAt 0]) (tmFiber61StateAt 1)
      tmFiber61State1_in_pass1_prefix
  rw [show [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13] = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12] ++ [tmFiber61StateAt 13] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber61StateAt 13) []
    (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12] [tmFiber61StateAt 0]) (tmFiber61StateAt 1)
    hparentBefore tmFiber61ReverseSingleStep13

theorem tmFiber61State14_in_pass1_prefix :
    tmFiber61StateAt 14 ∈ chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14] [tmFiber61StateAt 0] := by
  have hparentBefore :
      tmFiber61StateAt 2 ∈ chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13] [tmFiber61StateAt 0] := by
    rw [show [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13] = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2] ++ [tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13]
      (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2] [tmFiber61StateAt 0]) (tmFiber61StateAt 2)
      tmFiber61State2_in_pass1_prefix
  rw [show [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14] = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13] ++ [tmFiber61StateAt 14] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber61StateAt 14) []
    (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13] [tmFiber61StateAt 0]) (tmFiber61StateAt 2)
    hparentBefore tmFiber61ReverseSingleStep14

theorem tmFiber61State15_in_pass1_prefix :
    tmFiber61StateAt 15 ∈ chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14, tmFiber61StateAt 15] [tmFiber61StateAt 0] := by
  have hparentBefore :
      tmFiber61StateAt 3 ∈ chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14] [tmFiber61StateAt 0] := by
    rw [show [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14] = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3] ++ [tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14]
      (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3] [tmFiber61StateAt 0]) (tmFiber61StateAt 3)
      tmFiber61State3_in_pass1_prefix
  rw [show [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14, tmFiber61StateAt 15] = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14] ++ [tmFiber61StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber61StateAt 15) []
    (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14] [tmFiber61StateAt 0]) (tmFiber61StateAt 3)
    hparentBefore tmFiber61ReverseSingleStep15

theorem tmFiber61State0_in_pass1_full :
    tmFiber61StateAt 0 ∈ chainClosureStep tmWord tmFiber61DirectStates [tmFiber61StateAt 0] := by
  rw [show tmFiber61DirectStates = [tmFiber61StateAt 0] ++ [tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14, tmFiber61StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14, tmFiber61StateAt 15]
    (chainClosureStep tmWord [tmFiber61StateAt 0] [tmFiber61StateAt 0]) (tmFiber61StateAt 0)
    tmFiber61State0_in_pass1_prefix

theorem tmFiber61State1_in_pass1_full :
    tmFiber61StateAt 1 ∈ chainClosureStep tmWord tmFiber61DirectStates [tmFiber61StateAt 0] := by
  rw [show tmFiber61DirectStates = [tmFiber61StateAt 0, tmFiber61StateAt 1] ++ [tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14, tmFiber61StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14, tmFiber61StateAt 15]
    (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1] [tmFiber61StateAt 0]) (tmFiber61StateAt 1)
    tmFiber61State1_in_pass1_prefix

theorem tmFiber61State2_in_pass1_full :
    tmFiber61StateAt 2 ∈ chainClosureStep tmWord tmFiber61DirectStates [tmFiber61StateAt 0] := by
  rw [show tmFiber61DirectStates = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2] ++ [tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14, tmFiber61StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14, tmFiber61StateAt 15]
    (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2] [tmFiber61StateAt 0]) (tmFiber61StateAt 2)
    tmFiber61State2_in_pass1_prefix

theorem tmFiber61State3_in_pass1_full :
    tmFiber61StateAt 3 ∈ chainClosureStep tmWord tmFiber61DirectStates [tmFiber61StateAt 0] := by
  rw [show tmFiber61DirectStates = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3] ++ [tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14, tmFiber61StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14, tmFiber61StateAt 15]
    (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3] [tmFiber61StateAt 0]) (tmFiber61StateAt 3)
    tmFiber61State3_in_pass1_prefix

theorem tmFiber61State4_in_pass1_full :
    tmFiber61StateAt 4 ∈ chainClosureStep tmWord tmFiber61DirectStates [tmFiber61StateAt 0] := by
  rw [show tmFiber61DirectStates = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4] ++ [tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14, tmFiber61StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14, tmFiber61StateAt 15]
    (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4] [tmFiber61StateAt 0]) (tmFiber61StateAt 4)
    tmFiber61State4_in_pass1_prefix

theorem tmFiber61State5_in_pass1_full :
    tmFiber61StateAt 5 ∈ chainClosureStep tmWord tmFiber61DirectStates [tmFiber61StateAt 0] := by
  rw [show tmFiber61DirectStates = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5] ++ [tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14, tmFiber61StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14, tmFiber61StateAt 15]
    (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5] [tmFiber61StateAt 0]) (tmFiber61StateAt 5)
    tmFiber61State5_in_pass1_prefix

theorem tmFiber61State6_in_pass1_full :
    tmFiber61StateAt 6 ∈ chainClosureStep tmWord tmFiber61DirectStates [tmFiber61StateAt 0] := by
  rw [show tmFiber61DirectStates = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6] ++ [tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14, tmFiber61StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14, tmFiber61StateAt 15]
    (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6] [tmFiber61StateAt 0]) (tmFiber61StateAt 6)
    tmFiber61State6_in_pass1_prefix

theorem tmFiber61State7_in_pass1_full :
    tmFiber61StateAt 7 ∈ chainClosureStep tmWord tmFiber61DirectStates [tmFiber61StateAt 0] := by
  rw [show tmFiber61DirectStates = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7] ++ [tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14, tmFiber61StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14, tmFiber61StateAt 15]
    (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7] [tmFiber61StateAt 0]) (tmFiber61StateAt 7)
    tmFiber61State7_in_pass1_prefix

theorem tmFiber61State8_in_pass1_full :
    tmFiber61StateAt 8 ∈ chainClosureStep tmWord tmFiber61DirectStates [tmFiber61StateAt 0] := by
  rw [show tmFiber61DirectStates = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8] ++ [tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14, tmFiber61StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14, tmFiber61StateAt 15]
    (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8] [tmFiber61StateAt 0]) (tmFiber61StateAt 8)
    tmFiber61State8_in_pass1_prefix

theorem tmFiber61State9_in_pass1_full :
    tmFiber61StateAt 9 ∈ chainClosureStep tmWord tmFiber61DirectStates [tmFiber61StateAt 0] := by
  rw [show tmFiber61DirectStates = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9] ++ [tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14, tmFiber61StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14, tmFiber61StateAt 15]
    (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9] [tmFiber61StateAt 0]) (tmFiber61StateAt 9)
    tmFiber61State9_in_pass1_prefix

theorem tmFiber61State10_in_pass1_full :
    tmFiber61StateAt 10 ∈ chainClosureStep tmWord tmFiber61DirectStates [tmFiber61StateAt 0] := by
  rw [show tmFiber61DirectStates = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10] ++ [tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14, tmFiber61StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14, tmFiber61StateAt 15]
    (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10] [tmFiber61StateAt 0]) (tmFiber61StateAt 10)
    tmFiber61State10_in_pass1_prefix

theorem tmFiber61State11_in_pass1_full :
    tmFiber61StateAt 11 ∈ chainClosureStep tmWord tmFiber61DirectStates [tmFiber61StateAt 0] := by
  rw [show tmFiber61DirectStates = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11] ++ [tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14, tmFiber61StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14, tmFiber61StateAt 15]
    (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11] [tmFiber61StateAt 0]) (tmFiber61StateAt 11)
    tmFiber61State11_in_pass1_prefix

theorem tmFiber61State12_in_pass1_full :
    tmFiber61StateAt 12 ∈ chainClosureStep tmWord tmFiber61DirectStates [tmFiber61StateAt 0] := by
  rw [show tmFiber61DirectStates = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12] ++ [tmFiber61StateAt 13, tmFiber61StateAt 14, tmFiber61StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber61StateAt 13, tmFiber61StateAt 14, tmFiber61StateAt 15]
    (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12] [tmFiber61StateAt 0]) (tmFiber61StateAt 12)
    tmFiber61State12_in_pass1_prefix

theorem tmFiber61State13_in_pass1_full :
    tmFiber61StateAt 13 ∈ chainClosureStep tmWord tmFiber61DirectStates [tmFiber61StateAt 0] := by
  rw [show tmFiber61DirectStates = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13] ++ [tmFiber61StateAt 14, tmFiber61StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber61StateAt 14, tmFiber61StateAt 15]
    (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13] [tmFiber61StateAt 0]) (tmFiber61StateAt 13)
    tmFiber61State13_in_pass1_prefix

theorem tmFiber61State14_in_pass1_full :
    tmFiber61StateAt 14 ∈ chainClosureStep tmWord tmFiber61DirectStates [tmFiber61StateAt 0] := by
  rw [show tmFiber61DirectStates = [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14] ++ [tmFiber61StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber61StateAt 15]
    (chainClosureStep tmWord [tmFiber61StateAt 0, tmFiber61StateAt 1, tmFiber61StateAt 2, tmFiber61StateAt 3, tmFiber61StateAt 4, tmFiber61StateAt 5, tmFiber61StateAt 6, tmFiber61StateAt 7, tmFiber61StateAt 8, tmFiber61StateAt 9, tmFiber61StateAt 10, tmFiber61StateAt 11, tmFiber61StateAt 12, tmFiber61StateAt 13, tmFiber61StateAt 14] [tmFiber61StateAt 0]) (tmFiber61StateAt 14)
    tmFiber61State14_in_pass1_prefix

theorem tmFiber61State15_in_pass1_full :
    tmFiber61StateAt 15 ∈ chainClosureStep tmWord tmFiber61DirectStates [tmFiber61StateAt 0] := by
  simpa [tmFiber61DirectStates] using tmFiber61State15_in_pass1_prefix

theorem tmFiber61State0_in_close :
    tmFiber61StateAt 0 ∈ closeChainFiber tmWord tmFiber61DirectStates tmFiber61DirectStates.length [tmFiber61StateAt 0] := by
  change tmFiber61StateAt 0 ∈ closeChainFiber tmWord tmFiber61DirectStates (15 + 1) [tmFiber61StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber61DirectStates 15 [tmFiber61StateAt 0] (tmFiber61StateAt 0) tmFiber61State0_in_pass1_full

theorem tmFiber61State1_in_close :
    tmFiber61StateAt 1 ∈ closeChainFiber tmWord tmFiber61DirectStates tmFiber61DirectStates.length [tmFiber61StateAt 0] := by
  change tmFiber61StateAt 1 ∈ closeChainFiber tmWord tmFiber61DirectStates (15 + 1) [tmFiber61StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber61DirectStates 15 [tmFiber61StateAt 0] (tmFiber61StateAt 1) tmFiber61State1_in_pass1_full

theorem tmFiber61State2_in_close :
    tmFiber61StateAt 2 ∈ closeChainFiber tmWord tmFiber61DirectStates tmFiber61DirectStates.length [tmFiber61StateAt 0] := by
  change tmFiber61StateAt 2 ∈ closeChainFiber tmWord tmFiber61DirectStates (15 + 1) [tmFiber61StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber61DirectStates 15 [tmFiber61StateAt 0] (tmFiber61StateAt 2) tmFiber61State2_in_pass1_full

theorem tmFiber61State3_in_close :
    tmFiber61StateAt 3 ∈ closeChainFiber tmWord tmFiber61DirectStates tmFiber61DirectStates.length [tmFiber61StateAt 0] := by
  change tmFiber61StateAt 3 ∈ closeChainFiber tmWord tmFiber61DirectStates (15 + 1) [tmFiber61StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber61DirectStates 15 [tmFiber61StateAt 0] (tmFiber61StateAt 3) tmFiber61State3_in_pass1_full

theorem tmFiber61State4_in_close :
    tmFiber61StateAt 4 ∈ closeChainFiber tmWord tmFiber61DirectStates tmFiber61DirectStates.length [tmFiber61StateAt 0] := by
  change tmFiber61StateAt 4 ∈ closeChainFiber tmWord tmFiber61DirectStates (15 + 1) [tmFiber61StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber61DirectStates 15 [tmFiber61StateAt 0] (tmFiber61StateAt 4) tmFiber61State4_in_pass1_full

theorem tmFiber61State5_in_close :
    tmFiber61StateAt 5 ∈ closeChainFiber tmWord tmFiber61DirectStates tmFiber61DirectStates.length [tmFiber61StateAt 0] := by
  change tmFiber61StateAt 5 ∈ closeChainFiber tmWord tmFiber61DirectStates (15 + 1) [tmFiber61StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber61DirectStates 15 [tmFiber61StateAt 0] (tmFiber61StateAt 5) tmFiber61State5_in_pass1_full

theorem tmFiber61State6_in_close :
    tmFiber61StateAt 6 ∈ closeChainFiber tmWord tmFiber61DirectStates tmFiber61DirectStates.length [tmFiber61StateAt 0] := by
  change tmFiber61StateAt 6 ∈ closeChainFiber tmWord tmFiber61DirectStates (15 + 1) [tmFiber61StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber61DirectStates 15 [tmFiber61StateAt 0] (tmFiber61StateAt 6) tmFiber61State6_in_pass1_full

theorem tmFiber61State7_in_close :
    tmFiber61StateAt 7 ∈ closeChainFiber tmWord tmFiber61DirectStates tmFiber61DirectStates.length [tmFiber61StateAt 0] := by
  change tmFiber61StateAt 7 ∈ closeChainFiber tmWord tmFiber61DirectStates (15 + 1) [tmFiber61StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber61DirectStates 15 [tmFiber61StateAt 0] (tmFiber61StateAt 7) tmFiber61State7_in_pass1_full

theorem tmFiber61State8_in_close :
    tmFiber61StateAt 8 ∈ closeChainFiber tmWord tmFiber61DirectStates tmFiber61DirectStates.length [tmFiber61StateAt 0] := by
  change tmFiber61StateAt 8 ∈ closeChainFiber tmWord tmFiber61DirectStates (15 + 1) [tmFiber61StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber61DirectStates 15 [tmFiber61StateAt 0] (tmFiber61StateAt 8) tmFiber61State8_in_pass1_full

theorem tmFiber61State9_in_close :
    tmFiber61StateAt 9 ∈ closeChainFiber tmWord tmFiber61DirectStates tmFiber61DirectStates.length [tmFiber61StateAt 0] := by
  change tmFiber61StateAt 9 ∈ closeChainFiber tmWord tmFiber61DirectStates (15 + 1) [tmFiber61StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber61DirectStates 15 [tmFiber61StateAt 0] (tmFiber61StateAt 9) tmFiber61State9_in_pass1_full

theorem tmFiber61State10_in_close :
    tmFiber61StateAt 10 ∈ closeChainFiber tmWord tmFiber61DirectStates tmFiber61DirectStates.length [tmFiber61StateAt 0] := by
  change tmFiber61StateAt 10 ∈ closeChainFiber tmWord tmFiber61DirectStates (15 + 1) [tmFiber61StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber61DirectStates 15 [tmFiber61StateAt 0] (tmFiber61StateAt 10) tmFiber61State10_in_pass1_full

theorem tmFiber61State11_in_close :
    tmFiber61StateAt 11 ∈ closeChainFiber tmWord tmFiber61DirectStates tmFiber61DirectStates.length [tmFiber61StateAt 0] := by
  change tmFiber61StateAt 11 ∈ closeChainFiber tmWord tmFiber61DirectStates (15 + 1) [tmFiber61StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber61DirectStates 15 [tmFiber61StateAt 0] (tmFiber61StateAt 11) tmFiber61State11_in_pass1_full

theorem tmFiber61State12_in_close :
    tmFiber61StateAt 12 ∈ closeChainFiber tmWord tmFiber61DirectStates tmFiber61DirectStates.length [tmFiber61StateAt 0] := by
  change tmFiber61StateAt 12 ∈ closeChainFiber tmWord tmFiber61DirectStates (15 + 1) [tmFiber61StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber61DirectStates 15 [tmFiber61StateAt 0] (tmFiber61StateAt 12) tmFiber61State12_in_pass1_full

theorem tmFiber61State13_in_close :
    tmFiber61StateAt 13 ∈ closeChainFiber tmWord tmFiber61DirectStates tmFiber61DirectStates.length [tmFiber61StateAt 0] := by
  change tmFiber61StateAt 13 ∈ closeChainFiber tmWord tmFiber61DirectStates (15 + 1) [tmFiber61StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber61DirectStates 15 [tmFiber61StateAt 0] (tmFiber61StateAt 13) tmFiber61State13_in_pass1_full

theorem tmFiber61State14_in_close :
    tmFiber61StateAt 14 ∈ closeChainFiber tmWord tmFiber61DirectStates tmFiber61DirectStates.length [tmFiber61StateAt 0] := by
  change tmFiber61StateAt 14 ∈ closeChainFiber tmWord tmFiber61DirectStates (15 + 1) [tmFiber61StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber61DirectStates 15 [tmFiber61StateAt 0] (tmFiber61StateAt 14) tmFiber61State14_in_pass1_full

theorem tmFiber61State15_in_close :
    tmFiber61StateAt 15 ∈ closeChainFiber tmWord tmFiber61DirectStates tmFiber61DirectStates.length [tmFiber61StateAt 0] := by
  change tmFiber61StateAt 15 ∈ closeChainFiber tmWord tmFiber61DirectStates (15 + 1) [tmFiber61StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber61DirectStates 15 [tmFiber61StateAt 0] (tmFiber61StateAt 15) tmFiber61State15_in_pass1_full

theorem tmFiber61DirectConnected :
    chainFiberConnected tmWord tmFiber61DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber61DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber61State0_in_close
  · subst state
    exact tmFiber61State1_in_close
  · subst state
    exact tmFiber61State2_in_close
  · subst state
    exact tmFiber61State3_in_close
  · subst state
    exact tmFiber61State4_in_close
  · subst state
    exact tmFiber61State5_in_close
  · subst state
    exact tmFiber61State6_in_close
  · subst state
    exact tmFiber61State7_in_close
  · subst state
    exact tmFiber61State8_in_close
  · subst state
    exact tmFiber61State9_in_close
  · subst state
    exact tmFiber61State10_in_close
  · subst state
    exact tmFiber61State11_in_close
  · subst state
    exact tmFiber61State12_in_close
  · subst state
    exact tmFiber61State13_in_close
  · subst state
    exact tmFiber61State14_in_close
  · subst state
    exact tmFiber61State15_in_close
  · cases h

def tmFiber62StateAt (i : Nat) : List TauState :=
  directStates (tmFiber62RowAt i).sourceLeft (tmFiber62RowAt i).sourceRight

def tmFiber62DirectStates : List (List TauState) :=
  [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14, tmFiber62StateAt 15]

theorem tmFiber62ReverseRow_1_ok :
    tmRowReverseValid tmFiber62Key tmFiber62Expected (tmFiber62RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber62Chunk0_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber62Chunk0] at h
  exact h.2

theorem tmFiber62ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber62StateAt 0) (tmFiber62StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber62StateAt 0) (tmFiber62StateAt 1)
    (tmFiber62RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber62Key tmFiber62Expected
        (tmFiber62RowAt 1) (by decide) tmFiber62ReverseRow_1_ok
      simpa [tmFiber62StateAt, tmFiber62RowAt, tmFiber62Rows, listGetD, directRow] using h)

theorem tmFiber62ReverseRow_2_ok :
    tmRowReverseValid tmFiber62Key tmFiber62Expected (tmFiber62RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber62Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber62Chunk1] at h
  exact h.1

theorem tmFiber62ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber62StateAt 0) (tmFiber62StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber62StateAt 0) (tmFiber62StateAt 2)
    (tmFiber62RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber62Key tmFiber62Expected
        (tmFiber62RowAt 2) (by decide) tmFiber62ReverseRow_2_ok
      simpa [tmFiber62StateAt, tmFiber62RowAt, tmFiber62Rows, listGetD, directRow] using h)

theorem tmFiber62ReverseRow_3_ok :
    tmRowReverseValid tmFiber62Key tmFiber62Expected (tmFiber62RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber62Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber62Chunk1] at h
  exact h.2

theorem tmFiber62ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber62StateAt 1) (tmFiber62StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber62StateAt 1) (tmFiber62StateAt 3)
    (tmFiber62RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber62Key tmFiber62Expected
        (tmFiber62RowAt 3) (by decide) tmFiber62ReverseRow_3_ok
      simpa [tmFiber62StateAt, tmFiber62RowAt, tmFiber62Rows, listGetD, directRow] using h)

theorem tmFiber62ReverseRow_4_ok :
    tmRowReverseValid tmFiber62Key tmFiber62Expected (tmFiber62RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber62Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber62Chunk2] at h
  exact h.1

theorem tmFiber62ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber62StateAt 0) (tmFiber62StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber62StateAt 0) (tmFiber62StateAt 4)
    (tmFiber62RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber62Key tmFiber62Expected
        (tmFiber62RowAt 4) (by decide) tmFiber62ReverseRow_4_ok
      simpa [tmFiber62StateAt, tmFiber62RowAt, tmFiber62Rows, listGetD, directRow] using h)

theorem tmFiber62ReverseRow_5_ok :
    tmRowReverseValid tmFiber62Key tmFiber62Expected (tmFiber62RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber62Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber62Chunk2] at h
  exact h.2

theorem tmFiber62ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber62StateAt 1) (tmFiber62StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber62StateAt 1) (tmFiber62StateAt 5)
    (tmFiber62RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber62Key tmFiber62Expected
        (tmFiber62RowAt 5) (by decide) tmFiber62ReverseRow_5_ok
      simpa [tmFiber62StateAt, tmFiber62RowAt, tmFiber62Rows, listGetD, directRow] using h)

theorem tmFiber62ReverseRow_6_ok :
    tmRowReverseValid tmFiber62Key tmFiber62Expected (tmFiber62RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber62Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber62Chunk3] at h
  exact h.1

theorem tmFiber62ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber62StateAt 2) (tmFiber62StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber62StateAt 2) (tmFiber62StateAt 6)
    (tmFiber62RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber62Key tmFiber62Expected
        (tmFiber62RowAt 6) (by decide) tmFiber62ReverseRow_6_ok
      simpa [tmFiber62StateAt, tmFiber62RowAt, tmFiber62Rows, listGetD, directRow] using h)

theorem tmFiber62ReverseRow_7_ok :
    tmRowReverseValid tmFiber62Key tmFiber62Expected (tmFiber62RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber62Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber62Chunk3] at h
  exact h.2

theorem tmFiber62ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber62StateAt 3) (tmFiber62StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber62StateAt 3) (tmFiber62StateAt 7)
    (tmFiber62RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber62Key tmFiber62Expected
        (tmFiber62RowAt 7) (by decide) tmFiber62ReverseRow_7_ok
      simpa [tmFiber62StateAt, tmFiber62RowAt, tmFiber62Rows, listGetD, directRow] using h)

theorem tmFiber62ReverseRow_8_ok :
    tmRowReverseValid tmFiber62Key tmFiber62Expected (tmFiber62RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber62Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber62Chunk4] at h
  exact h.1

theorem tmFiber62ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber62StateAt 0) (tmFiber62StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber62StateAt 0) (tmFiber62StateAt 8)
    (tmFiber62RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber62Key tmFiber62Expected
        (tmFiber62RowAt 8) (by decide) tmFiber62ReverseRow_8_ok
      simpa [tmFiber62StateAt, tmFiber62RowAt, tmFiber62Rows, listGetD, directRow] using h)

theorem tmFiber62ReverseRow_9_ok :
    tmRowReverseValid tmFiber62Key tmFiber62Expected (tmFiber62RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber62Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber62Chunk4] at h
  exact h.2

theorem tmFiber62ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber62StateAt 1) (tmFiber62StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber62StateAt 1) (tmFiber62StateAt 9)
    (tmFiber62RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber62Key tmFiber62Expected
        (tmFiber62RowAt 9) (by decide) tmFiber62ReverseRow_9_ok
      simpa [tmFiber62StateAt, tmFiber62RowAt, tmFiber62Rows, listGetD, directRow] using h)

theorem tmFiber62ReverseRow_10_ok :
    tmRowReverseValid tmFiber62Key tmFiber62Expected (tmFiber62RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber62Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber62Chunk5] at h
  exact h.1

theorem tmFiber62ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber62StateAt 2) (tmFiber62StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber62StateAt 2) (tmFiber62StateAt 10)
    (tmFiber62RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber62Key tmFiber62Expected
        (tmFiber62RowAt 10) (by decide) tmFiber62ReverseRow_10_ok
      simpa [tmFiber62StateAt, tmFiber62RowAt, tmFiber62Rows, listGetD, directRow] using h)

theorem tmFiber62ReverseRow_11_ok :
    tmRowReverseValid tmFiber62Key tmFiber62Expected (tmFiber62RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber62Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber62Chunk5] at h
  exact h.2

theorem tmFiber62ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber62StateAt 3) (tmFiber62StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber62StateAt 3) (tmFiber62StateAt 11)
    (tmFiber62RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber62Key tmFiber62Expected
        (tmFiber62RowAt 11) (by decide) tmFiber62ReverseRow_11_ok
      simpa [tmFiber62StateAt, tmFiber62RowAt, tmFiber62Rows, listGetD, directRow] using h)

theorem tmFiber62ReverseRow_12_ok :
    tmRowReverseValid tmFiber62Key tmFiber62Expected (tmFiber62RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber62Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber62Chunk6] at h
  exact h.1

theorem tmFiber62ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber62StateAt 4) (tmFiber62StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber62StateAt 4) (tmFiber62StateAt 12)
    (tmFiber62RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber62Key tmFiber62Expected
        (tmFiber62RowAt 12) (by decide) tmFiber62ReverseRow_12_ok
      simpa [tmFiber62StateAt, tmFiber62RowAt, tmFiber62Rows, listGetD, directRow] using h)

theorem tmFiber62ReverseRow_13_ok :
    tmRowReverseValid tmFiber62Key tmFiber62Expected (tmFiber62RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber62Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber62Chunk6] at h
  exact h.2

theorem tmFiber62ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber62StateAt 5) (tmFiber62StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber62StateAt 5) (tmFiber62StateAt 13)
    (tmFiber62RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber62Key tmFiber62Expected
        (tmFiber62RowAt 13) (by decide) tmFiber62ReverseRow_13_ok
      simpa [tmFiber62StateAt, tmFiber62RowAt, tmFiber62Rows, listGetD, directRow] using h)

theorem tmFiber62ReverseRow_14_ok :
    tmRowReverseValid tmFiber62Key tmFiber62Expected (tmFiber62RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber62Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber62Chunk7] at h
  exact h.1

theorem tmFiber62ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber62StateAt 6) (tmFiber62StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber62StateAt 6) (tmFiber62StateAt 14)
    (tmFiber62RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber62Key tmFiber62Expected
        (tmFiber62RowAt 14) (by decide) tmFiber62ReverseRow_14_ok
      simpa [tmFiber62StateAt, tmFiber62RowAt, tmFiber62Rows, listGetD, directRow] using h)

theorem tmFiber62ReverseRow_15_ok :
    tmRowReverseValid tmFiber62Key tmFiber62Expected (tmFiber62RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber62Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber62Chunk7] at h
  exact h.2

theorem tmFiber62ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber62StateAt 7) (tmFiber62StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber62StateAt 7) (tmFiber62StateAt 15)
    (tmFiber62RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber62Key tmFiber62Expected
        (tmFiber62RowAt 15) (by decide) tmFiber62ReverseRow_15_ok
      simpa [tmFiber62StateAt, tmFiber62RowAt, tmFiber62Rows, listGetD, directRow] using h)

theorem tmFiber62State0_in_pass1_prefix :
    tmFiber62StateAt 0 ∈ chainClosureStep tmWord [tmFiber62StateAt 0] [tmFiber62StateAt 0] := by
  exact chainClosureStep_mem_of_seen tmWord [tmFiber62StateAt 0] [tmFiber62StateAt 0] (tmFiber62StateAt 0) (by simp)

theorem tmFiber62State1_in_pass1_prefix :
    tmFiber62StateAt 1 ∈ chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1] [tmFiber62StateAt 0] := by
  have hparentBefore :
      tmFiber62StateAt 0 ∈ chainClosureStep tmWord [tmFiber62StateAt 0] [tmFiber62StateAt 0] := by
    exact tmFiber62State0_in_pass1_prefix
  rw [show [tmFiber62StateAt 0, tmFiber62StateAt 1] = [tmFiber62StateAt 0] ++ [tmFiber62StateAt 1] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber62StateAt 1) []
    (chainClosureStep tmWord [tmFiber62StateAt 0] [tmFiber62StateAt 0]) (tmFiber62StateAt 0)
    hparentBefore tmFiber62ReverseSingleStep1

theorem tmFiber62State2_in_pass1_prefix :
    tmFiber62StateAt 2 ∈ chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2] [tmFiber62StateAt 0] := by
  have hparentBefore :
      tmFiber62StateAt 0 ∈ chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1] [tmFiber62StateAt 0] := by
    rw [show [tmFiber62StateAt 0, tmFiber62StateAt 1] = [tmFiber62StateAt 0] ++ [tmFiber62StateAt 1] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber62StateAt 1]
      (chainClosureStep tmWord [tmFiber62StateAt 0] [tmFiber62StateAt 0]) (tmFiber62StateAt 0)
      tmFiber62State0_in_pass1_prefix
  rw [show [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2] = [tmFiber62StateAt 0, tmFiber62StateAt 1] ++ [tmFiber62StateAt 2] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber62StateAt 2) []
    (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1] [tmFiber62StateAt 0]) (tmFiber62StateAt 0)
    hparentBefore tmFiber62ReverseSingleStep2

theorem tmFiber62State3_in_pass1_prefix :
    tmFiber62StateAt 3 ∈ chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3] [tmFiber62StateAt 0] := by
  have hparentBefore :
      tmFiber62StateAt 1 ∈ chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2] [tmFiber62StateAt 0] := by
    rw [show [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2] = [tmFiber62StateAt 0, tmFiber62StateAt 1] ++ [tmFiber62StateAt 2] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber62StateAt 2]
      (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1] [tmFiber62StateAt 0]) (tmFiber62StateAt 1)
      tmFiber62State1_in_pass1_prefix
  rw [show [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3] = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2] ++ [tmFiber62StateAt 3] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber62StateAt 3) []
    (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2] [tmFiber62StateAt 0]) (tmFiber62StateAt 1)
    hparentBefore tmFiber62ReverseSingleStep3

theorem tmFiber62State4_in_pass1_prefix :
    tmFiber62StateAt 4 ∈ chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4] [tmFiber62StateAt 0] := by
  have hparentBefore :
      tmFiber62StateAt 0 ∈ chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3] [tmFiber62StateAt 0] := by
    rw [show [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3] = [tmFiber62StateAt 0] ++ [tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3]
      (chainClosureStep tmWord [tmFiber62StateAt 0] [tmFiber62StateAt 0]) (tmFiber62StateAt 0)
      tmFiber62State0_in_pass1_prefix
  rw [show [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4] = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3] ++ [tmFiber62StateAt 4] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber62StateAt 4) []
    (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3] [tmFiber62StateAt 0]) (tmFiber62StateAt 0)
    hparentBefore tmFiber62ReverseSingleStep4

theorem tmFiber62State5_in_pass1_prefix :
    tmFiber62StateAt 5 ∈ chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5] [tmFiber62StateAt 0] := by
  have hparentBefore :
      tmFiber62StateAt 1 ∈ chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4] [tmFiber62StateAt 0] := by
    rw [show [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4] = [tmFiber62StateAt 0, tmFiber62StateAt 1] ++ [tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4]
      (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1] [tmFiber62StateAt 0]) (tmFiber62StateAt 1)
      tmFiber62State1_in_pass1_prefix
  rw [show [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5] = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4] ++ [tmFiber62StateAt 5] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber62StateAt 5) []
    (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4] [tmFiber62StateAt 0]) (tmFiber62StateAt 1)
    hparentBefore tmFiber62ReverseSingleStep5

theorem tmFiber62State6_in_pass1_prefix :
    tmFiber62StateAt 6 ∈ chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6] [tmFiber62StateAt 0] := by
  have hparentBefore :
      tmFiber62StateAt 2 ∈ chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5] [tmFiber62StateAt 0] := by
    rw [show [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5] = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2] ++ [tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5]
      (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2] [tmFiber62StateAt 0]) (tmFiber62StateAt 2)
      tmFiber62State2_in_pass1_prefix
  rw [show [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6] = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5] ++ [tmFiber62StateAt 6] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber62StateAt 6) []
    (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5] [tmFiber62StateAt 0]) (tmFiber62StateAt 2)
    hparentBefore tmFiber62ReverseSingleStep6

theorem tmFiber62State7_in_pass1_prefix :
    tmFiber62StateAt 7 ∈ chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7] [tmFiber62StateAt 0] := by
  have hparentBefore :
      tmFiber62StateAt 3 ∈ chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6] [tmFiber62StateAt 0] := by
    rw [show [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6] = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3] ++ [tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6]
      (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3] [tmFiber62StateAt 0]) (tmFiber62StateAt 3)
      tmFiber62State3_in_pass1_prefix
  rw [show [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7] = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6] ++ [tmFiber62StateAt 7] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber62StateAt 7) []
    (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6] [tmFiber62StateAt 0]) (tmFiber62StateAt 3)
    hparentBefore tmFiber62ReverseSingleStep7

theorem tmFiber62State8_in_pass1_prefix :
    tmFiber62StateAt 8 ∈ chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8] [tmFiber62StateAt 0] := by
  have hparentBefore :
      tmFiber62StateAt 0 ∈ chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7] [tmFiber62StateAt 0] := by
    rw [show [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7] = [tmFiber62StateAt 0] ++ [tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7]
      (chainClosureStep tmWord [tmFiber62StateAt 0] [tmFiber62StateAt 0]) (tmFiber62StateAt 0)
      tmFiber62State0_in_pass1_prefix
  rw [show [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8] = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7] ++ [tmFiber62StateAt 8] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber62StateAt 8) []
    (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7] [tmFiber62StateAt 0]) (tmFiber62StateAt 0)
    hparentBefore tmFiber62ReverseSingleStep8

theorem tmFiber62State9_in_pass1_prefix :
    tmFiber62StateAt 9 ∈ chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9] [tmFiber62StateAt 0] := by
  have hparentBefore :
      tmFiber62StateAt 1 ∈ chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8] [tmFiber62StateAt 0] := by
    rw [show [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8] = [tmFiber62StateAt 0, tmFiber62StateAt 1] ++ [tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8]
      (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1] [tmFiber62StateAt 0]) (tmFiber62StateAt 1)
      tmFiber62State1_in_pass1_prefix
  rw [show [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9] = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8] ++ [tmFiber62StateAt 9] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber62StateAt 9) []
    (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8] [tmFiber62StateAt 0]) (tmFiber62StateAt 1)
    hparentBefore tmFiber62ReverseSingleStep9

theorem tmFiber62State10_in_pass1_prefix :
    tmFiber62StateAt 10 ∈ chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10] [tmFiber62StateAt 0] := by
  have hparentBefore :
      tmFiber62StateAt 2 ∈ chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9] [tmFiber62StateAt 0] := by
    rw [show [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9] = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2] ++ [tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9]
      (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2] [tmFiber62StateAt 0]) (tmFiber62StateAt 2)
      tmFiber62State2_in_pass1_prefix
  rw [show [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10] = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9] ++ [tmFiber62StateAt 10] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber62StateAt 10) []
    (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9] [tmFiber62StateAt 0]) (tmFiber62StateAt 2)
    hparentBefore tmFiber62ReverseSingleStep10

theorem tmFiber62State11_in_pass1_prefix :
    tmFiber62StateAt 11 ∈ chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11] [tmFiber62StateAt 0] := by
  have hparentBefore :
      tmFiber62StateAt 3 ∈ chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10] [tmFiber62StateAt 0] := by
    rw [show [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10] = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3] ++ [tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10]
      (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3] [tmFiber62StateAt 0]) (tmFiber62StateAt 3)
      tmFiber62State3_in_pass1_prefix
  rw [show [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11] = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10] ++ [tmFiber62StateAt 11] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber62StateAt 11) []
    (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10] [tmFiber62StateAt 0]) (tmFiber62StateAt 3)
    hparentBefore tmFiber62ReverseSingleStep11

theorem tmFiber62State12_in_pass1_prefix :
    tmFiber62StateAt 12 ∈ chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12] [tmFiber62StateAt 0] := by
  have hparentBefore :
      tmFiber62StateAt 4 ∈ chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11] [tmFiber62StateAt 0] := by
    rw [show [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11] = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4] ++ [tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11]
      (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4] [tmFiber62StateAt 0]) (tmFiber62StateAt 4)
      tmFiber62State4_in_pass1_prefix
  rw [show [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12] = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11] ++ [tmFiber62StateAt 12] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber62StateAt 12) []
    (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11] [tmFiber62StateAt 0]) (tmFiber62StateAt 4)
    hparentBefore tmFiber62ReverseSingleStep12

theorem tmFiber62State13_in_pass1_prefix :
    tmFiber62StateAt 13 ∈ chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13] [tmFiber62StateAt 0] := by
  have hparentBefore :
      tmFiber62StateAt 5 ∈ chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12] [tmFiber62StateAt 0] := by
    rw [show [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12] = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5] ++ [tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12]
      (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5] [tmFiber62StateAt 0]) (tmFiber62StateAt 5)
      tmFiber62State5_in_pass1_prefix
  rw [show [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13] = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12] ++ [tmFiber62StateAt 13] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber62StateAt 13) []
    (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12] [tmFiber62StateAt 0]) (tmFiber62StateAt 5)
    hparentBefore tmFiber62ReverseSingleStep13

theorem tmFiber62State14_in_pass1_prefix :
    tmFiber62StateAt 14 ∈ chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14] [tmFiber62StateAt 0] := by
  have hparentBefore :
      tmFiber62StateAt 6 ∈ chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13] [tmFiber62StateAt 0] := by
    rw [show [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13] = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6] ++ [tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13]
      (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6] [tmFiber62StateAt 0]) (tmFiber62StateAt 6)
      tmFiber62State6_in_pass1_prefix
  rw [show [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14] = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13] ++ [tmFiber62StateAt 14] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber62StateAt 14) []
    (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13] [tmFiber62StateAt 0]) (tmFiber62StateAt 6)
    hparentBefore tmFiber62ReverseSingleStep14

theorem tmFiber62State15_in_pass1_prefix :
    tmFiber62StateAt 15 ∈ chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14, tmFiber62StateAt 15] [tmFiber62StateAt 0] := by
  have hparentBefore :
      tmFiber62StateAt 7 ∈ chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14] [tmFiber62StateAt 0] := by
    rw [show [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14] = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7] ++ [tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14]
      (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7] [tmFiber62StateAt 0]) (tmFiber62StateAt 7)
      tmFiber62State7_in_pass1_prefix
  rw [show [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14, tmFiber62StateAt 15] = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14] ++ [tmFiber62StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber62StateAt 15) []
    (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14] [tmFiber62StateAt 0]) (tmFiber62StateAt 7)
    hparentBefore tmFiber62ReverseSingleStep15

theorem tmFiber62State0_in_pass1_full :
    tmFiber62StateAt 0 ∈ chainClosureStep tmWord tmFiber62DirectStates [tmFiber62StateAt 0] := by
  rw [show tmFiber62DirectStates = [tmFiber62StateAt 0] ++ [tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14, tmFiber62StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14, tmFiber62StateAt 15]
    (chainClosureStep tmWord [tmFiber62StateAt 0] [tmFiber62StateAt 0]) (tmFiber62StateAt 0)
    tmFiber62State0_in_pass1_prefix

theorem tmFiber62State1_in_pass1_full :
    tmFiber62StateAt 1 ∈ chainClosureStep tmWord tmFiber62DirectStates [tmFiber62StateAt 0] := by
  rw [show tmFiber62DirectStates = [tmFiber62StateAt 0, tmFiber62StateAt 1] ++ [tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14, tmFiber62StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14, tmFiber62StateAt 15]
    (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1] [tmFiber62StateAt 0]) (tmFiber62StateAt 1)
    tmFiber62State1_in_pass1_prefix

theorem tmFiber62State2_in_pass1_full :
    tmFiber62StateAt 2 ∈ chainClosureStep tmWord tmFiber62DirectStates [tmFiber62StateAt 0] := by
  rw [show tmFiber62DirectStates = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2] ++ [tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14, tmFiber62StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14, tmFiber62StateAt 15]
    (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2] [tmFiber62StateAt 0]) (tmFiber62StateAt 2)
    tmFiber62State2_in_pass1_prefix

theorem tmFiber62State3_in_pass1_full :
    tmFiber62StateAt 3 ∈ chainClosureStep tmWord tmFiber62DirectStates [tmFiber62StateAt 0] := by
  rw [show tmFiber62DirectStates = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3] ++ [tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14, tmFiber62StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14, tmFiber62StateAt 15]
    (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3] [tmFiber62StateAt 0]) (tmFiber62StateAt 3)
    tmFiber62State3_in_pass1_prefix

theorem tmFiber62State4_in_pass1_full :
    tmFiber62StateAt 4 ∈ chainClosureStep tmWord tmFiber62DirectStates [tmFiber62StateAt 0] := by
  rw [show tmFiber62DirectStates = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4] ++ [tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14, tmFiber62StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14, tmFiber62StateAt 15]
    (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4] [tmFiber62StateAt 0]) (tmFiber62StateAt 4)
    tmFiber62State4_in_pass1_prefix

theorem tmFiber62State5_in_pass1_full :
    tmFiber62StateAt 5 ∈ chainClosureStep tmWord tmFiber62DirectStates [tmFiber62StateAt 0] := by
  rw [show tmFiber62DirectStates = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5] ++ [tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14, tmFiber62StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14, tmFiber62StateAt 15]
    (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5] [tmFiber62StateAt 0]) (tmFiber62StateAt 5)
    tmFiber62State5_in_pass1_prefix

theorem tmFiber62State6_in_pass1_full :
    tmFiber62StateAt 6 ∈ chainClosureStep tmWord tmFiber62DirectStates [tmFiber62StateAt 0] := by
  rw [show tmFiber62DirectStates = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6] ++ [tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14, tmFiber62StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14, tmFiber62StateAt 15]
    (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6] [tmFiber62StateAt 0]) (tmFiber62StateAt 6)
    tmFiber62State6_in_pass1_prefix

theorem tmFiber62State7_in_pass1_full :
    tmFiber62StateAt 7 ∈ chainClosureStep tmWord tmFiber62DirectStates [tmFiber62StateAt 0] := by
  rw [show tmFiber62DirectStates = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7] ++ [tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14, tmFiber62StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14, tmFiber62StateAt 15]
    (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7] [tmFiber62StateAt 0]) (tmFiber62StateAt 7)
    tmFiber62State7_in_pass1_prefix

theorem tmFiber62State8_in_pass1_full :
    tmFiber62StateAt 8 ∈ chainClosureStep tmWord tmFiber62DirectStates [tmFiber62StateAt 0] := by
  rw [show tmFiber62DirectStates = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8] ++ [tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14, tmFiber62StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14, tmFiber62StateAt 15]
    (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8] [tmFiber62StateAt 0]) (tmFiber62StateAt 8)
    tmFiber62State8_in_pass1_prefix

theorem tmFiber62State9_in_pass1_full :
    tmFiber62StateAt 9 ∈ chainClosureStep tmWord tmFiber62DirectStates [tmFiber62StateAt 0] := by
  rw [show tmFiber62DirectStates = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9] ++ [tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14, tmFiber62StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14, tmFiber62StateAt 15]
    (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9] [tmFiber62StateAt 0]) (tmFiber62StateAt 9)
    tmFiber62State9_in_pass1_prefix

theorem tmFiber62State10_in_pass1_full :
    tmFiber62StateAt 10 ∈ chainClosureStep tmWord tmFiber62DirectStates [tmFiber62StateAt 0] := by
  rw [show tmFiber62DirectStates = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10] ++ [tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14, tmFiber62StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14, tmFiber62StateAt 15]
    (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10] [tmFiber62StateAt 0]) (tmFiber62StateAt 10)
    tmFiber62State10_in_pass1_prefix

theorem tmFiber62State11_in_pass1_full :
    tmFiber62StateAt 11 ∈ chainClosureStep tmWord tmFiber62DirectStates [tmFiber62StateAt 0] := by
  rw [show tmFiber62DirectStates = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11] ++ [tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14, tmFiber62StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14, tmFiber62StateAt 15]
    (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11] [tmFiber62StateAt 0]) (tmFiber62StateAt 11)
    tmFiber62State11_in_pass1_prefix

theorem tmFiber62State12_in_pass1_full :
    tmFiber62StateAt 12 ∈ chainClosureStep tmWord tmFiber62DirectStates [tmFiber62StateAt 0] := by
  rw [show tmFiber62DirectStates = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12] ++ [tmFiber62StateAt 13, tmFiber62StateAt 14, tmFiber62StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber62StateAt 13, tmFiber62StateAt 14, tmFiber62StateAt 15]
    (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12] [tmFiber62StateAt 0]) (tmFiber62StateAt 12)
    tmFiber62State12_in_pass1_prefix

theorem tmFiber62State13_in_pass1_full :
    tmFiber62StateAt 13 ∈ chainClosureStep tmWord tmFiber62DirectStates [tmFiber62StateAt 0] := by
  rw [show tmFiber62DirectStates = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13] ++ [tmFiber62StateAt 14, tmFiber62StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber62StateAt 14, tmFiber62StateAt 15]
    (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13] [tmFiber62StateAt 0]) (tmFiber62StateAt 13)
    tmFiber62State13_in_pass1_prefix

theorem tmFiber62State14_in_pass1_full :
    tmFiber62StateAt 14 ∈ chainClosureStep tmWord tmFiber62DirectStates [tmFiber62StateAt 0] := by
  rw [show tmFiber62DirectStates = [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14] ++ [tmFiber62StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber62StateAt 15]
    (chainClosureStep tmWord [tmFiber62StateAt 0, tmFiber62StateAt 1, tmFiber62StateAt 2, tmFiber62StateAt 3, tmFiber62StateAt 4, tmFiber62StateAt 5, tmFiber62StateAt 6, tmFiber62StateAt 7, tmFiber62StateAt 8, tmFiber62StateAt 9, tmFiber62StateAt 10, tmFiber62StateAt 11, tmFiber62StateAt 12, tmFiber62StateAt 13, tmFiber62StateAt 14] [tmFiber62StateAt 0]) (tmFiber62StateAt 14)
    tmFiber62State14_in_pass1_prefix

theorem tmFiber62State15_in_pass1_full :
    tmFiber62StateAt 15 ∈ chainClosureStep tmWord tmFiber62DirectStates [tmFiber62StateAt 0] := by
  simpa [tmFiber62DirectStates] using tmFiber62State15_in_pass1_prefix

theorem tmFiber62State0_in_close :
    tmFiber62StateAt 0 ∈ closeChainFiber tmWord tmFiber62DirectStates tmFiber62DirectStates.length [tmFiber62StateAt 0] := by
  change tmFiber62StateAt 0 ∈ closeChainFiber tmWord tmFiber62DirectStates (15 + 1) [tmFiber62StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber62DirectStates 15 [tmFiber62StateAt 0] (tmFiber62StateAt 0) tmFiber62State0_in_pass1_full

theorem tmFiber62State1_in_close :
    tmFiber62StateAt 1 ∈ closeChainFiber tmWord tmFiber62DirectStates tmFiber62DirectStates.length [tmFiber62StateAt 0] := by
  change tmFiber62StateAt 1 ∈ closeChainFiber tmWord tmFiber62DirectStates (15 + 1) [tmFiber62StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber62DirectStates 15 [tmFiber62StateAt 0] (tmFiber62StateAt 1) tmFiber62State1_in_pass1_full

theorem tmFiber62State2_in_close :
    tmFiber62StateAt 2 ∈ closeChainFiber tmWord tmFiber62DirectStates tmFiber62DirectStates.length [tmFiber62StateAt 0] := by
  change tmFiber62StateAt 2 ∈ closeChainFiber tmWord tmFiber62DirectStates (15 + 1) [tmFiber62StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber62DirectStates 15 [tmFiber62StateAt 0] (tmFiber62StateAt 2) tmFiber62State2_in_pass1_full

theorem tmFiber62State3_in_close :
    tmFiber62StateAt 3 ∈ closeChainFiber tmWord tmFiber62DirectStates tmFiber62DirectStates.length [tmFiber62StateAt 0] := by
  change tmFiber62StateAt 3 ∈ closeChainFiber tmWord tmFiber62DirectStates (15 + 1) [tmFiber62StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber62DirectStates 15 [tmFiber62StateAt 0] (tmFiber62StateAt 3) tmFiber62State3_in_pass1_full

theorem tmFiber62State4_in_close :
    tmFiber62StateAt 4 ∈ closeChainFiber tmWord tmFiber62DirectStates tmFiber62DirectStates.length [tmFiber62StateAt 0] := by
  change tmFiber62StateAt 4 ∈ closeChainFiber tmWord tmFiber62DirectStates (15 + 1) [tmFiber62StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber62DirectStates 15 [tmFiber62StateAt 0] (tmFiber62StateAt 4) tmFiber62State4_in_pass1_full

theorem tmFiber62State5_in_close :
    tmFiber62StateAt 5 ∈ closeChainFiber tmWord tmFiber62DirectStates tmFiber62DirectStates.length [tmFiber62StateAt 0] := by
  change tmFiber62StateAt 5 ∈ closeChainFiber tmWord tmFiber62DirectStates (15 + 1) [tmFiber62StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber62DirectStates 15 [tmFiber62StateAt 0] (tmFiber62StateAt 5) tmFiber62State5_in_pass1_full

theorem tmFiber62State6_in_close :
    tmFiber62StateAt 6 ∈ closeChainFiber tmWord tmFiber62DirectStates tmFiber62DirectStates.length [tmFiber62StateAt 0] := by
  change tmFiber62StateAt 6 ∈ closeChainFiber tmWord tmFiber62DirectStates (15 + 1) [tmFiber62StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber62DirectStates 15 [tmFiber62StateAt 0] (tmFiber62StateAt 6) tmFiber62State6_in_pass1_full

theorem tmFiber62State7_in_close :
    tmFiber62StateAt 7 ∈ closeChainFiber tmWord tmFiber62DirectStates tmFiber62DirectStates.length [tmFiber62StateAt 0] := by
  change tmFiber62StateAt 7 ∈ closeChainFiber tmWord tmFiber62DirectStates (15 + 1) [tmFiber62StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber62DirectStates 15 [tmFiber62StateAt 0] (tmFiber62StateAt 7) tmFiber62State7_in_pass1_full

theorem tmFiber62State8_in_close :
    tmFiber62StateAt 8 ∈ closeChainFiber tmWord tmFiber62DirectStates tmFiber62DirectStates.length [tmFiber62StateAt 0] := by
  change tmFiber62StateAt 8 ∈ closeChainFiber tmWord tmFiber62DirectStates (15 + 1) [tmFiber62StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber62DirectStates 15 [tmFiber62StateAt 0] (tmFiber62StateAt 8) tmFiber62State8_in_pass1_full

theorem tmFiber62State9_in_close :
    tmFiber62StateAt 9 ∈ closeChainFiber tmWord tmFiber62DirectStates tmFiber62DirectStates.length [tmFiber62StateAt 0] := by
  change tmFiber62StateAt 9 ∈ closeChainFiber tmWord tmFiber62DirectStates (15 + 1) [tmFiber62StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber62DirectStates 15 [tmFiber62StateAt 0] (tmFiber62StateAt 9) tmFiber62State9_in_pass1_full

theorem tmFiber62State10_in_close :
    tmFiber62StateAt 10 ∈ closeChainFiber tmWord tmFiber62DirectStates tmFiber62DirectStates.length [tmFiber62StateAt 0] := by
  change tmFiber62StateAt 10 ∈ closeChainFiber tmWord tmFiber62DirectStates (15 + 1) [tmFiber62StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber62DirectStates 15 [tmFiber62StateAt 0] (tmFiber62StateAt 10) tmFiber62State10_in_pass1_full

theorem tmFiber62State11_in_close :
    tmFiber62StateAt 11 ∈ closeChainFiber tmWord tmFiber62DirectStates tmFiber62DirectStates.length [tmFiber62StateAt 0] := by
  change tmFiber62StateAt 11 ∈ closeChainFiber tmWord tmFiber62DirectStates (15 + 1) [tmFiber62StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber62DirectStates 15 [tmFiber62StateAt 0] (tmFiber62StateAt 11) tmFiber62State11_in_pass1_full

theorem tmFiber62State12_in_close :
    tmFiber62StateAt 12 ∈ closeChainFiber tmWord tmFiber62DirectStates tmFiber62DirectStates.length [tmFiber62StateAt 0] := by
  change tmFiber62StateAt 12 ∈ closeChainFiber tmWord tmFiber62DirectStates (15 + 1) [tmFiber62StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber62DirectStates 15 [tmFiber62StateAt 0] (tmFiber62StateAt 12) tmFiber62State12_in_pass1_full

theorem tmFiber62State13_in_close :
    tmFiber62StateAt 13 ∈ closeChainFiber tmWord tmFiber62DirectStates tmFiber62DirectStates.length [tmFiber62StateAt 0] := by
  change tmFiber62StateAt 13 ∈ closeChainFiber tmWord tmFiber62DirectStates (15 + 1) [tmFiber62StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber62DirectStates 15 [tmFiber62StateAt 0] (tmFiber62StateAt 13) tmFiber62State13_in_pass1_full

theorem tmFiber62State14_in_close :
    tmFiber62StateAt 14 ∈ closeChainFiber tmWord tmFiber62DirectStates tmFiber62DirectStates.length [tmFiber62StateAt 0] := by
  change tmFiber62StateAt 14 ∈ closeChainFiber tmWord tmFiber62DirectStates (15 + 1) [tmFiber62StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber62DirectStates 15 [tmFiber62StateAt 0] (tmFiber62StateAt 14) tmFiber62State14_in_pass1_full

theorem tmFiber62State15_in_close :
    tmFiber62StateAt 15 ∈ closeChainFiber tmWord tmFiber62DirectStates tmFiber62DirectStates.length [tmFiber62StateAt 0] := by
  change tmFiber62StateAt 15 ∈ closeChainFiber tmWord tmFiber62DirectStates (15 + 1) [tmFiber62StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber62DirectStates 15 [tmFiber62StateAt 0] (tmFiber62StateAt 15) tmFiber62State15_in_pass1_full

theorem tmFiber62DirectConnected :
    chainFiberConnected tmWord tmFiber62DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber62DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber62State0_in_close
  · subst state
    exact tmFiber62State1_in_close
  · subst state
    exact tmFiber62State2_in_close
  · subst state
    exact tmFiber62State3_in_close
  · subst state
    exact tmFiber62State4_in_close
  · subst state
    exact tmFiber62State5_in_close
  · subst state
    exact tmFiber62State6_in_close
  · subst state
    exact tmFiber62State7_in_close
  · subst state
    exact tmFiber62State8_in_close
  · subst state
    exact tmFiber62State9_in_close
  · subst state
    exact tmFiber62State10_in_close
  · subst state
    exact tmFiber62State11_in_close
  · subst state
    exact tmFiber62State12_in_close
  · subst state
    exact tmFiber62State13_in_close
  · subst state
    exact tmFiber62State14_in_close
  · subst state
    exact tmFiber62State15_in_close
  · cases h

def tmFiber69StateAt (i : Nat) : List TauState :=
  directStates (tmFiber69RowAt i).sourceLeft (tmFiber69RowAt i).sourceRight

def tmFiber69DirectStates : List (List TauState) :=
  [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14, tmFiber69StateAt 15]

theorem tmFiber69ReverseRow_1_ok :
    tmRowReverseValid tmFiber69Key tmFiber69Expected (tmFiber69RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber69Chunk0_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber69Chunk0] at h
  exact h.2

theorem tmFiber69ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber69StateAt 0) (tmFiber69StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber69StateAt 0) (tmFiber69StateAt 1)
    (tmFiber69RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber69Key tmFiber69Expected
        (tmFiber69RowAt 1) (by decide) tmFiber69ReverseRow_1_ok
      simpa [tmFiber69StateAt, tmFiber69RowAt, tmFiber69Rows, listGetD, directRow] using h)

theorem tmFiber69ReverseRow_2_ok :
    tmRowReverseValid tmFiber69Key tmFiber69Expected (tmFiber69RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber69Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber69Chunk1] at h
  exact h.1

theorem tmFiber69ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber69StateAt 1) (tmFiber69StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber69StateAt 1) (tmFiber69StateAt 2)
    (tmFiber69RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber69Key tmFiber69Expected
        (tmFiber69RowAt 2) (by decide) tmFiber69ReverseRow_2_ok
      simpa [tmFiber69StateAt, tmFiber69RowAt, tmFiber69Rows, listGetD, directRow] using h)

theorem tmFiber69ReverseRow_3_ok :
    tmRowReverseValid tmFiber69Key tmFiber69Expected (tmFiber69RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber69Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber69Chunk1] at h
  exact h.2

theorem tmFiber69ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber69StateAt 0) (tmFiber69StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber69StateAt 0) (tmFiber69StateAt 3)
    (tmFiber69RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber69Key tmFiber69Expected
        (tmFiber69RowAt 3) (by decide) tmFiber69ReverseRow_3_ok
      simpa [tmFiber69StateAt, tmFiber69RowAt, tmFiber69Rows, listGetD, directRow] using h)

theorem tmFiber69ReverseRow_4_ok :
    tmRowReverseValid tmFiber69Key tmFiber69Expected (tmFiber69RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber69Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber69Chunk2] at h
  exact h.1

theorem tmFiber69ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber69StateAt 0) (tmFiber69StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber69StateAt 0) (tmFiber69StateAt 4)
    (tmFiber69RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber69Key tmFiber69Expected
        (tmFiber69RowAt 4) (by decide) tmFiber69ReverseRow_4_ok
      simpa [tmFiber69StateAt, tmFiber69RowAt, tmFiber69Rows, listGetD, directRow] using h)

theorem tmFiber69ReverseRow_5_ok :
    tmRowReverseValid tmFiber69Key tmFiber69Expected (tmFiber69RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber69Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber69Chunk2] at h
  exact h.2

theorem tmFiber69ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber69StateAt 1) (tmFiber69StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber69StateAt 1) (tmFiber69StateAt 5)
    (tmFiber69RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber69Key tmFiber69Expected
        (tmFiber69RowAt 5) (by decide) tmFiber69ReverseRow_5_ok
      simpa [tmFiber69StateAt, tmFiber69RowAt, tmFiber69Rows, listGetD, directRow] using h)

theorem tmFiber69ReverseRow_6_ok :
    tmRowReverseValid tmFiber69Key tmFiber69Expected (tmFiber69RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber69Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber69Chunk3] at h
  exact h.1

theorem tmFiber69ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber69StateAt 2) (tmFiber69StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber69StateAt 2) (tmFiber69StateAt 6)
    (tmFiber69RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber69Key tmFiber69Expected
        (tmFiber69RowAt 6) (by decide) tmFiber69ReverseRow_6_ok
      simpa [tmFiber69StateAt, tmFiber69RowAt, tmFiber69Rows, listGetD, directRow] using h)

theorem tmFiber69ReverseRow_7_ok :
    tmRowReverseValid tmFiber69Key tmFiber69Expected (tmFiber69RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber69Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber69Chunk3] at h
  exact h.2

theorem tmFiber69ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber69StateAt 3) (tmFiber69StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber69StateAt 3) (tmFiber69StateAt 7)
    (tmFiber69RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber69Key tmFiber69Expected
        (tmFiber69RowAt 7) (by decide) tmFiber69ReverseRow_7_ok
      simpa [tmFiber69StateAt, tmFiber69RowAt, tmFiber69Rows, listGetD, directRow] using h)

theorem tmFiber69ReverseRow_8_ok :
    tmRowReverseValid tmFiber69Key tmFiber69Expected (tmFiber69RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber69Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber69Chunk4] at h
  exact h.1

theorem tmFiber69ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber69StateAt 0) (tmFiber69StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber69StateAt 0) (tmFiber69StateAt 8)
    (tmFiber69RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber69Key tmFiber69Expected
        (tmFiber69RowAt 8) (by decide) tmFiber69ReverseRow_8_ok
      simpa [tmFiber69StateAt, tmFiber69RowAt, tmFiber69Rows, listGetD, directRow] using h)

theorem tmFiber69ReverseRow_9_ok :
    tmRowReverseValid tmFiber69Key tmFiber69Expected (tmFiber69RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber69Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber69Chunk4] at h
  exact h.2

theorem tmFiber69ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber69StateAt 1) (tmFiber69StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber69StateAt 1) (tmFiber69StateAt 9)
    (tmFiber69RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber69Key tmFiber69Expected
        (tmFiber69RowAt 9) (by decide) tmFiber69ReverseRow_9_ok
      simpa [tmFiber69StateAt, tmFiber69RowAt, tmFiber69Rows, listGetD, directRow] using h)

theorem tmFiber69ReverseRow_10_ok :
    tmRowReverseValid tmFiber69Key tmFiber69Expected (tmFiber69RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber69Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber69Chunk5] at h
  exact h.1

theorem tmFiber69ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber69StateAt 2) (tmFiber69StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber69StateAt 2) (tmFiber69StateAt 10)
    (tmFiber69RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber69Key tmFiber69Expected
        (tmFiber69RowAt 10) (by decide) tmFiber69ReverseRow_10_ok
      simpa [tmFiber69StateAt, tmFiber69RowAt, tmFiber69Rows, listGetD, directRow] using h)

theorem tmFiber69ReverseRow_11_ok :
    tmRowReverseValid tmFiber69Key tmFiber69Expected (tmFiber69RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber69Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber69Chunk5] at h
  exact h.2

theorem tmFiber69ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber69StateAt 3) (tmFiber69StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber69StateAt 3) (tmFiber69StateAt 11)
    (tmFiber69RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber69Key tmFiber69Expected
        (tmFiber69RowAt 11) (by decide) tmFiber69ReverseRow_11_ok
      simpa [tmFiber69StateAt, tmFiber69RowAt, tmFiber69Rows, listGetD, directRow] using h)

theorem tmFiber69ReverseRow_12_ok :
    tmRowReverseValid tmFiber69Key tmFiber69Expected (tmFiber69RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber69Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber69Chunk6] at h
  exact h.1

theorem tmFiber69ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber69StateAt 4) (tmFiber69StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber69StateAt 4) (tmFiber69StateAt 12)
    (tmFiber69RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber69Key tmFiber69Expected
        (tmFiber69RowAt 12) (by decide) tmFiber69ReverseRow_12_ok
      simpa [tmFiber69StateAt, tmFiber69RowAt, tmFiber69Rows, listGetD, directRow] using h)

theorem tmFiber69ReverseRow_13_ok :
    tmRowReverseValid tmFiber69Key tmFiber69Expected (tmFiber69RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber69Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber69Chunk6] at h
  exact h.2

theorem tmFiber69ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber69StateAt 5) (tmFiber69StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber69StateAt 5) (tmFiber69StateAt 13)
    (tmFiber69RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber69Key tmFiber69Expected
        (tmFiber69RowAt 13) (by decide) tmFiber69ReverseRow_13_ok
      simpa [tmFiber69StateAt, tmFiber69RowAt, tmFiber69Rows, listGetD, directRow] using h)

theorem tmFiber69ReverseRow_14_ok :
    tmRowReverseValid tmFiber69Key tmFiber69Expected (tmFiber69RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber69Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber69Chunk7] at h
  exact h.1

theorem tmFiber69ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber69StateAt 6) (tmFiber69StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber69StateAt 6) (tmFiber69StateAt 14)
    (tmFiber69RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber69Key tmFiber69Expected
        (tmFiber69RowAt 14) (by decide) tmFiber69ReverseRow_14_ok
      simpa [tmFiber69StateAt, tmFiber69RowAt, tmFiber69Rows, listGetD, directRow] using h)

theorem tmFiber69ReverseRow_15_ok :
    tmRowReverseValid tmFiber69Key tmFiber69Expected (tmFiber69RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber69Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber69Chunk7] at h
  exact h.2

theorem tmFiber69ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber69StateAt 7) (tmFiber69StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber69StateAt 7) (tmFiber69StateAt 15)
    (tmFiber69RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber69Key tmFiber69Expected
        (tmFiber69RowAt 15) (by decide) tmFiber69ReverseRow_15_ok
      simpa [tmFiber69StateAt, tmFiber69RowAt, tmFiber69Rows, listGetD, directRow] using h)

theorem tmFiber69State0_in_pass1_prefix :
    tmFiber69StateAt 0 ∈ chainClosureStep tmWord [tmFiber69StateAt 0] [tmFiber69StateAt 0] := by
  exact chainClosureStep_mem_of_seen tmWord [tmFiber69StateAt 0] [tmFiber69StateAt 0] (tmFiber69StateAt 0) (by simp)

theorem tmFiber69State1_in_pass1_prefix :
    tmFiber69StateAt 1 ∈ chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1] [tmFiber69StateAt 0] := by
  have hparentBefore :
      tmFiber69StateAt 0 ∈ chainClosureStep tmWord [tmFiber69StateAt 0] [tmFiber69StateAt 0] := by
    exact tmFiber69State0_in_pass1_prefix
  rw [show [tmFiber69StateAt 0, tmFiber69StateAt 1] = [tmFiber69StateAt 0] ++ [tmFiber69StateAt 1] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber69StateAt 1) []
    (chainClosureStep tmWord [tmFiber69StateAt 0] [tmFiber69StateAt 0]) (tmFiber69StateAt 0)
    hparentBefore tmFiber69ReverseSingleStep1

theorem tmFiber69State2_in_pass1_prefix :
    tmFiber69StateAt 2 ∈ chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2] [tmFiber69StateAt 0] := by
  have hparentBefore :
      tmFiber69StateAt 1 ∈ chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1] [tmFiber69StateAt 0] := by
    exact tmFiber69State1_in_pass1_prefix
  rw [show [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2] = [tmFiber69StateAt 0, tmFiber69StateAt 1] ++ [tmFiber69StateAt 2] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber69StateAt 2) []
    (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1] [tmFiber69StateAt 0]) (tmFiber69StateAt 1)
    hparentBefore tmFiber69ReverseSingleStep2

theorem tmFiber69State3_in_pass1_prefix :
    tmFiber69StateAt 3 ∈ chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3] [tmFiber69StateAt 0] := by
  have hparentBefore :
      tmFiber69StateAt 0 ∈ chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2] [tmFiber69StateAt 0] := by
    rw [show [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2] = [tmFiber69StateAt 0] ++ [tmFiber69StateAt 1, tmFiber69StateAt 2] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber69StateAt 1, tmFiber69StateAt 2]
      (chainClosureStep tmWord [tmFiber69StateAt 0] [tmFiber69StateAt 0]) (tmFiber69StateAt 0)
      tmFiber69State0_in_pass1_prefix
  rw [show [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3] = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2] ++ [tmFiber69StateAt 3] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber69StateAt 3) []
    (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2] [tmFiber69StateAt 0]) (tmFiber69StateAt 0)
    hparentBefore tmFiber69ReverseSingleStep3

theorem tmFiber69State4_in_pass1_prefix :
    tmFiber69StateAt 4 ∈ chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4] [tmFiber69StateAt 0] := by
  have hparentBefore :
      tmFiber69StateAt 0 ∈ chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3] [tmFiber69StateAt 0] := by
    rw [show [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3] = [tmFiber69StateAt 0] ++ [tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3]
      (chainClosureStep tmWord [tmFiber69StateAt 0] [tmFiber69StateAt 0]) (tmFiber69StateAt 0)
      tmFiber69State0_in_pass1_prefix
  rw [show [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4] = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3] ++ [tmFiber69StateAt 4] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber69StateAt 4) []
    (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3] [tmFiber69StateAt 0]) (tmFiber69StateAt 0)
    hparentBefore tmFiber69ReverseSingleStep4

theorem tmFiber69State5_in_pass1_prefix :
    tmFiber69StateAt 5 ∈ chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5] [tmFiber69StateAt 0] := by
  have hparentBefore :
      tmFiber69StateAt 1 ∈ chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4] [tmFiber69StateAt 0] := by
    rw [show [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4] = [tmFiber69StateAt 0, tmFiber69StateAt 1] ++ [tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4]
      (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1] [tmFiber69StateAt 0]) (tmFiber69StateAt 1)
      tmFiber69State1_in_pass1_prefix
  rw [show [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5] = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4] ++ [tmFiber69StateAt 5] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber69StateAt 5) []
    (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4] [tmFiber69StateAt 0]) (tmFiber69StateAt 1)
    hparentBefore tmFiber69ReverseSingleStep5

theorem tmFiber69State6_in_pass1_prefix :
    tmFiber69StateAt 6 ∈ chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6] [tmFiber69StateAt 0] := by
  have hparentBefore :
      tmFiber69StateAt 2 ∈ chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5] [tmFiber69StateAt 0] := by
    rw [show [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5] = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2] ++ [tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5]
      (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2] [tmFiber69StateAt 0]) (tmFiber69StateAt 2)
      tmFiber69State2_in_pass1_prefix
  rw [show [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6] = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5] ++ [tmFiber69StateAt 6] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber69StateAt 6) []
    (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5] [tmFiber69StateAt 0]) (tmFiber69StateAt 2)
    hparentBefore tmFiber69ReverseSingleStep6

theorem tmFiber69State7_in_pass1_prefix :
    tmFiber69StateAt 7 ∈ chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7] [tmFiber69StateAt 0] := by
  have hparentBefore :
      tmFiber69StateAt 3 ∈ chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6] [tmFiber69StateAt 0] := by
    rw [show [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6] = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3] ++ [tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6]
      (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3] [tmFiber69StateAt 0]) (tmFiber69StateAt 3)
      tmFiber69State3_in_pass1_prefix
  rw [show [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7] = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6] ++ [tmFiber69StateAt 7] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber69StateAt 7) []
    (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6] [tmFiber69StateAt 0]) (tmFiber69StateAt 3)
    hparentBefore tmFiber69ReverseSingleStep7

theorem tmFiber69State8_in_pass1_prefix :
    tmFiber69StateAt 8 ∈ chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8] [tmFiber69StateAt 0] := by
  have hparentBefore :
      tmFiber69StateAt 0 ∈ chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7] [tmFiber69StateAt 0] := by
    rw [show [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7] = [tmFiber69StateAt 0] ++ [tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7]
      (chainClosureStep tmWord [tmFiber69StateAt 0] [tmFiber69StateAt 0]) (tmFiber69StateAt 0)
      tmFiber69State0_in_pass1_prefix
  rw [show [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8] = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7] ++ [tmFiber69StateAt 8] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber69StateAt 8) []
    (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7] [tmFiber69StateAt 0]) (tmFiber69StateAt 0)
    hparentBefore tmFiber69ReverseSingleStep8

theorem tmFiber69State9_in_pass1_prefix :
    tmFiber69StateAt 9 ∈ chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9] [tmFiber69StateAt 0] := by
  have hparentBefore :
      tmFiber69StateAt 1 ∈ chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8] [tmFiber69StateAt 0] := by
    rw [show [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8] = [tmFiber69StateAt 0, tmFiber69StateAt 1] ++ [tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8]
      (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1] [tmFiber69StateAt 0]) (tmFiber69StateAt 1)
      tmFiber69State1_in_pass1_prefix
  rw [show [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9] = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8] ++ [tmFiber69StateAt 9] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber69StateAt 9) []
    (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8] [tmFiber69StateAt 0]) (tmFiber69StateAt 1)
    hparentBefore tmFiber69ReverseSingleStep9

theorem tmFiber69State10_in_pass1_prefix :
    tmFiber69StateAt 10 ∈ chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10] [tmFiber69StateAt 0] := by
  have hparentBefore :
      tmFiber69StateAt 2 ∈ chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9] [tmFiber69StateAt 0] := by
    rw [show [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9] = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2] ++ [tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9]
      (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2] [tmFiber69StateAt 0]) (tmFiber69StateAt 2)
      tmFiber69State2_in_pass1_prefix
  rw [show [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10] = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9] ++ [tmFiber69StateAt 10] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber69StateAt 10) []
    (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9] [tmFiber69StateAt 0]) (tmFiber69StateAt 2)
    hparentBefore tmFiber69ReverseSingleStep10

theorem tmFiber69State11_in_pass1_prefix :
    tmFiber69StateAt 11 ∈ chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11] [tmFiber69StateAt 0] := by
  have hparentBefore :
      tmFiber69StateAt 3 ∈ chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10] [tmFiber69StateAt 0] := by
    rw [show [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10] = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3] ++ [tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10]
      (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3] [tmFiber69StateAt 0]) (tmFiber69StateAt 3)
      tmFiber69State3_in_pass1_prefix
  rw [show [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11] = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10] ++ [tmFiber69StateAt 11] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber69StateAt 11) []
    (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10] [tmFiber69StateAt 0]) (tmFiber69StateAt 3)
    hparentBefore tmFiber69ReverseSingleStep11

theorem tmFiber69State12_in_pass1_prefix :
    tmFiber69StateAt 12 ∈ chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12] [tmFiber69StateAt 0] := by
  have hparentBefore :
      tmFiber69StateAt 4 ∈ chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11] [tmFiber69StateAt 0] := by
    rw [show [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11] = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4] ++ [tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11]
      (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4] [tmFiber69StateAt 0]) (tmFiber69StateAt 4)
      tmFiber69State4_in_pass1_prefix
  rw [show [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12] = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11] ++ [tmFiber69StateAt 12] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber69StateAt 12) []
    (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11] [tmFiber69StateAt 0]) (tmFiber69StateAt 4)
    hparentBefore tmFiber69ReverseSingleStep12

theorem tmFiber69State13_in_pass1_prefix :
    tmFiber69StateAt 13 ∈ chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13] [tmFiber69StateAt 0] := by
  have hparentBefore :
      tmFiber69StateAt 5 ∈ chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12] [tmFiber69StateAt 0] := by
    rw [show [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12] = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5] ++ [tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12]
      (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5] [tmFiber69StateAt 0]) (tmFiber69StateAt 5)
      tmFiber69State5_in_pass1_prefix
  rw [show [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13] = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12] ++ [tmFiber69StateAt 13] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber69StateAt 13) []
    (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12] [tmFiber69StateAt 0]) (tmFiber69StateAt 5)
    hparentBefore tmFiber69ReverseSingleStep13

theorem tmFiber69State14_in_pass1_prefix :
    tmFiber69StateAt 14 ∈ chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14] [tmFiber69StateAt 0] := by
  have hparentBefore :
      tmFiber69StateAt 6 ∈ chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13] [tmFiber69StateAt 0] := by
    rw [show [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13] = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6] ++ [tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13]
      (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6] [tmFiber69StateAt 0]) (tmFiber69StateAt 6)
      tmFiber69State6_in_pass1_prefix
  rw [show [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14] = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13] ++ [tmFiber69StateAt 14] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber69StateAt 14) []
    (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13] [tmFiber69StateAt 0]) (tmFiber69StateAt 6)
    hparentBefore tmFiber69ReverseSingleStep14

theorem tmFiber69State15_in_pass1_prefix :
    tmFiber69StateAt 15 ∈ chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14, tmFiber69StateAt 15] [tmFiber69StateAt 0] := by
  have hparentBefore :
      tmFiber69StateAt 7 ∈ chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14] [tmFiber69StateAt 0] := by
    rw [show [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14] = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7] ++ [tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14]
      (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7] [tmFiber69StateAt 0]) (tmFiber69StateAt 7)
      tmFiber69State7_in_pass1_prefix
  rw [show [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14, tmFiber69StateAt 15] = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14] ++ [tmFiber69StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber69StateAt 15) []
    (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14] [tmFiber69StateAt 0]) (tmFiber69StateAt 7)
    hparentBefore tmFiber69ReverseSingleStep15

theorem tmFiber69State0_in_pass1_full :
    tmFiber69StateAt 0 ∈ chainClosureStep tmWord tmFiber69DirectStates [tmFiber69StateAt 0] := by
  rw [show tmFiber69DirectStates = [tmFiber69StateAt 0] ++ [tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14, tmFiber69StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14, tmFiber69StateAt 15]
    (chainClosureStep tmWord [tmFiber69StateAt 0] [tmFiber69StateAt 0]) (tmFiber69StateAt 0)
    tmFiber69State0_in_pass1_prefix

theorem tmFiber69State1_in_pass1_full :
    tmFiber69StateAt 1 ∈ chainClosureStep tmWord tmFiber69DirectStates [tmFiber69StateAt 0] := by
  rw [show tmFiber69DirectStates = [tmFiber69StateAt 0, tmFiber69StateAt 1] ++ [tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14, tmFiber69StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14, tmFiber69StateAt 15]
    (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1] [tmFiber69StateAt 0]) (tmFiber69StateAt 1)
    tmFiber69State1_in_pass1_prefix

theorem tmFiber69State2_in_pass1_full :
    tmFiber69StateAt 2 ∈ chainClosureStep tmWord tmFiber69DirectStates [tmFiber69StateAt 0] := by
  rw [show tmFiber69DirectStates = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2] ++ [tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14, tmFiber69StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14, tmFiber69StateAt 15]
    (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2] [tmFiber69StateAt 0]) (tmFiber69StateAt 2)
    tmFiber69State2_in_pass1_prefix

theorem tmFiber69State3_in_pass1_full :
    tmFiber69StateAt 3 ∈ chainClosureStep tmWord tmFiber69DirectStates [tmFiber69StateAt 0] := by
  rw [show tmFiber69DirectStates = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3] ++ [tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14, tmFiber69StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14, tmFiber69StateAt 15]
    (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3] [tmFiber69StateAt 0]) (tmFiber69StateAt 3)
    tmFiber69State3_in_pass1_prefix

theorem tmFiber69State4_in_pass1_full :
    tmFiber69StateAt 4 ∈ chainClosureStep tmWord tmFiber69DirectStates [tmFiber69StateAt 0] := by
  rw [show tmFiber69DirectStates = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4] ++ [tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14, tmFiber69StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14, tmFiber69StateAt 15]
    (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4] [tmFiber69StateAt 0]) (tmFiber69StateAt 4)
    tmFiber69State4_in_pass1_prefix

theorem tmFiber69State5_in_pass1_full :
    tmFiber69StateAt 5 ∈ chainClosureStep tmWord tmFiber69DirectStates [tmFiber69StateAt 0] := by
  rw [show tmFiber69DirectStates = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5] ++ [tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14, tmFiber69StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14, tmFiber69StateAt 15]
    (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5] [tmFiber69StateAt 0]) (tmFiber69StateAt 5)
    tmFiber69State5_in_pass1_prefix

theorem tmFiber69State6_in_pass1_full :
    tmFiber69StateAt 6 ∈ chainClosureStep tmWord tmFiber69DirectStates [tmFiber69StateAt 0] := by
  rw [show tmFiber69DirectStates = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6] ++ [tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14, tmFiber69StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14, tmFiber69StateAt 15]
    (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6] [tmFiber69StateAt 0]) (tmFiber69StateAt 6)
    tmFiber69State6_in_pass1_prefix

theorem tmFiber69State7_in_pass1_full :
    tmFiber69StateAt 7 ∈ chainClosureStep tmWord tmFiber69DirectStates [tmFiber69StateAt 0] := by
  rw [show tmFiber69DirectStates = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7] ++ [tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14, tmFiber69StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14, tmFiber69StateAt 15]
    (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7] [tmFiber69StateAt 0]) (tmFiber69StateAt 7)
    tmFiber69State7_in_pass1_prefix

theorem tmFiber69State8_in_pass1_full :
    tmFiber69StateAt 8 ∈ chainClosureStep tmWord tmFiber69DirectStates [tmFiber69StateAt 0] := by
  rw [show tmFiber69DirectStates = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8] ++ [tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14, tmFiber69StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14, tmFiber69StateAt 15]
    (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8] [tmFiber69StateAt 0]) (tmFiber69StateAt 8)
    tmFiber69State8_in_pass1_prefix

theorem tmFiber69State9_in_pass1_full :
    tmFiber69StateAt 9 ∈ chainClosureStep tmWord tmFiber69DirectStates [tmFiber69StateAt 0] := by
  rw [show tmFiber69DirectStates = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9] ++ [tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14, tmFiber69StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14, tmFiber69StateAt 15]
    (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9] [tmFiber69StateAt 0]) (tmFiber69StateAt 9)
    tmFiber69State9_in_pass1_prefix

theorem tmFiber69State10_in_pass1_full :
    tmFiber69StateAt 10 ∈ chainClosureStep tmWord tmFiber69DirectStates [tmFiber69StateAt 0] := by
  rw [show tmFiber69DirectStates = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10] ++ [tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14, tmFiber69StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14, tmFiber69StateAt 15]
    (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10] [tmFiber69StateAt 0]) (tmFiber69StateAt 10)
    tmFiber69State10_in_pass1_prefix

theorem tmFiber69State11_in_pass1_full :
    tmFiber69StateAt 11 ∈ chainClosureStep tmWord tmFiber69DirectStates [tmFiber69StateAt 0] := by
  rw [show tmFiber69DirectStates = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11] ++ [tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14, tmFiber69StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14, tmFiber69StateAt 15]
    (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11] [tmFiber69StateAt 0]) (tmFiber69StateAt 11)
    tmFiber69State11_in_pass1_prefix

theorem tmFiber69State12_in_pass1_full :
    tmFiber69StateAt 12 ∈ chainClosureStep tmWord tmFiber69DirectStates [tmFiber69StateAt 0] := by
  rw [show tmFiber69DirectStates = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12] ++ [tmFiber69StateAt 13, tmFiber69StateAt 14, tmFiber69StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber69StateAt 13, tmFiber69StateAt 14, tmFiber69StateAt 15]
    (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12] [tmFiber69StateAt 0]) (tmFiber69StateAt 12)
    tmFiber69State12_in_pass1_prefix

theorem tmFiber69State13_in_pass1_full :
    tmFiber69StateAt 13 ∈ chainClosureStep tmWord tmFiber69DirectStates [tmFiber69StateAt 0] := by
  rw [show tmFiber69DirectStates = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13] ++ [tmFiber69StateAt 14, tmFiber69StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber69StateAt 14, tmFiber69StateAt 15]
    (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13] [tmFiber69StateAt 0]) (tmFiber69StateAt 13)
    tmFiber69State13_in_pass1_prefix

theorem tmFiber69State14_in_pass1_full :
    tmFiber69StateAt 14 ∈ chainClosureStep tmWord tmFiber69DirectStates [tmFiber69StateAt 0] := by
  rw [show tmFiber69DirectStates = [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14] ++ [tmFiber69StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber69StateAt 15]
    (chainClosureStep tmWord [tmFiber69StateAt 0, tmFiber69StateAt 1, tmFiber69StateAt 2, tmFiber69StateAt 3, tmFiber69StateAt 4, tmFiber69StateAt 5, tmFiber69StateAt 6, tmFiber69StateAt 7, tmFiber69StateAt 8, tmFiber69StateAt 9, tmFiber69StateAt 10, tmFiber69StateAt 11, tmFiber69StateAt 12, tmFiber69StateAt 13, tmFiber69StateAt 14] [tmFiber69StateAt 0]) (tmFiber69StateAt 14)
    tmFiber69State14_in_pass1_prefix

theorem tmFiber69State15_in_pass1_full :
    tmFiber69StateAt 15 ∈ chainClosureStep tmWord tmFiber69DirectStates [tmFiber69StateAt 0] := by
  simpa [tmFiber69DirectStates] using tmFiber69State15_in_pass1_prefix

theorem tmFiber69State0_in_close :
    tmFiber69StateAt 0 ∈ closeChainFiber tmWord tmFiber69DirectStates tmFiber69DirectStates.length [tmFiber69StateAt 0] := by
  change tmFiber69StateAt 0 ∈ closeChainFiber tmWord tmFiber69DirectStates (15 + 1) [tmFiber69StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber69DirectStates 15 [tmFiber69StateAt 0] (tmFiber69StateAt 0) tmFiber69State0_in_pass1_full

theorem tmFiber69State1_in_close :
    tmFiber69StateAt 1 ∈ closeChainFiber tmWord tmFiber69DirectStates tmFiber69DirectStates.length [tmFiber69StateAt 0] := by
  change tmFiber69StateAt 1 ∈ closeChainFiber tmWord tmFiber69DirectStates (15 + 1) [tmFiber69StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber69DirectStates 15 [tmFiber69StateAt 0] (tmFiber69StateAt 1) tmFiber69State1_in_pass1_full

theorem tmFiber69State2_in_close :
    tmFiber69StateAt 2 ∈ closeChainFiber tmWord tmFiber69DirectStates tmFiber69DirectStates.length [tmFiber69StateAt 0] := by
  change tmFiber69StateAt 2 ∈ closeChainFiber tmWord tmFiber69DirectStates (15 + 1) [tmFiber69StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber69DirectStates 15 [tmFiber69StateAt 0] (tmFiber69StateAt 2) tmFiber69State2_in_pass1_full

theorem tmFiber69State3_in_close :
    tmFiber69StateAt 3 ∈ closeChainFiber tmWord tmFiber69DirectStates tmFiber69DirectStates.length [tmFiber69StateAt 0] := by
  change tmFiber69StateAt 3 ∈ closeChainFiber tmWord tmFiber69DirectStates (15 + 1) [tmFiber69StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber69DirectStates 15 [tmFiber69StateAt 0] (tmFiber69StateAt 3) tmFiber69State3_in_pass1_full

theorem tmFiber69State4_in_close :
    tmFiber69StateAt 4 ∈ closeChainFiber tmWord tmFiber69DirectStates tmFiber69DirectStates.length [tmFiber69StateAt 0] := by
  change tmFiber69StateAt 4 ∈ closeChainFiber tmWord tmFiber69DirectStates (15 + 1) [tmFiber69StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber69DirectStates 15 [tmFiber69StateAt 0] (tmFiber69StateAt 4) tmFiber69State4_in_pass1_full

theorem tmFiber69State5_in_close :
    tmFiber69StateAt 5 ∈ closeChainFiber tmWord tmFiber69DirectStates tmFiber69DirectStates.length [tmFiber69StateAt 0] := by
  change tmFiber69StateAt 5 ∈ closeChainFiber tmWord tmFiber69DirectStates (15 + 1) [tmFiber69StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber69DirectStates 15 [tmFiber69StateAt 0] (tmFiber69StateAt 5) tmFiber69State5_in_pass1_full

theorem tmFiber69State6_in_close :
    tmFiber69StateAt 6 ∈ closeChainFiber tmWord tmFiber69DirectStates tmFiber69DirectStates.length [tmFiber69StateAt 0] := by
  change tmFiber69StateAt 6 ∈ closeChainFiber tmWord tmFiber69DirectStates (15 + 1) [tmFiber69StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber69DirectStates 15 [tmFiber69StateAt 0] (tmFiber69StateAt 6) tmFiber69State6_in_pass1_full

theorem tmFiber69State7_in_close :
    tmFiber69StateAt 7 ∈ closeChainFiber tmWord tmFiber69DirectStates tmFiber69DirectStates.length [tmFiber69StateAt 0] := by
  change tmFiber69StateAt 7 ∈ closeChainFiber tmWord tmFiber69DirectStates (15 + 1) [tmFiber69StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber69DirectStates 15 [tmFiber69StateAt 0] (tmFiber69StateAt 7) tmFiber69State7_in_pass1_full

theorem tmFiber69State8_in_close :
    tmFiber69StateAt 8 ∈ closeChainFiber tmWord tmFiber69DirectStates tmFiber69DirectStates.length [tmFiber69StateAt 0] := by
  change tmFiber69StateAt 8 ∈ closeChainFiber tmWord tmFiber69DirectStates (15 + 1) [tmFiber69StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber69DirectStates 15 [tmFiber69StateAt 0] (tmFiber69StateAt 8) tmFiber69State8_in_pass1_full

theorem tmFiber69State9_in_close :
    tmFiber69StateAt 9 ∈ closeChainFiber tmWord tmFiber69DirectStates tmFiber69DirectStates.length [tmFiber69StateAt 0] := by
  change tmFiber69StateAt 9 ∈ closeChainFiber tmWord tmFiber69DirectStates (15 + 1) [tmFiber69StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber69DirectStates 15 [tmFiber69StateAt 0] (tmFiber69StateAt 9) tmFiber69State9_in_pass1_full

theorem tmFiber69State10_in_close :
    tmFiber69StateAt 10 ∈ closeChainFiber tmWord tmFiber69DirectStates tmFiber69DirectStates.length [tmFiber69StateAt 0] := by
  change tmFiber69StateAt 10 ∈ closeChainFiber tmWord tmFiber69DirectStates (15 + 1) [tmFiber69StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber69DirectStates 15 [tmFiber69StateAt 0] (tmFiber69StateAt 10) tmFiber69State10_in_pass1_full

theorem tmFiber69State11_in_close :
    tmFiber69StateAt 11 ∈ closeChainFiber tmWord tmFiber69DirectStates tmFiber69DirectStates.length [tmFiber69StateAt 0] := by
  change tmFiber69StateAt 11 ∈ closeChainFiber tmWord tmFiber69DirectStates (15 + 1) [tmFiber69StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber69DirectStates 15 [tmFiber69StateAt 0] (tmFiber69StateAt 11) tmFiber69State11_in_pass1_full

theorem tmFiber69State12_in_close :
    tmFiber69StateAt 12 ∈ closeChainFiber tmWord tmFiber69DirectStates tmFiber69DirectStates.length [tmFiber69StateAt 0] := by
  change tmFiber69StateAt 12 ∈ closeChainFiber tmWord tmFiber69DirectStates (15 + 1) [tmFiber69StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber69DirectStates 15 [tmFiber69StateAt 0] (tmFiber69StateAt 12) tmFiber69State12_in_pass1_full

theorem tmFiber69State13_in_close :
    tmFiber69StateAt 13 ∈ closeChainFiber tmWord tmFiber69DirectStates tmFiber69DirectStates.length [tmFiber69StateAt 0] := by
  change tmFiber69StateAt 13 ∈ closeChainFiber tmWord tmFiber69DirectStates (15 + 1) [tmFiber69StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber69DirectStates 15 [tmFiber69StateAt 0] (tmFiber69StateAt 13) tmFiber69State13_in_pass1_full

theorem tmFiber69State14_in_close :
    tmFiber69StateAt 14 ∈ closeChainFiber tmWord tmFiber69DirectStates tmFiber69DirectStates.length [tmFiber69StateAt 0] := by
  change tmFiber69StateAt 14 ∈ closeChainFiber tmWord tmFiber69DirectStates (15 + 1) [tmFiber69StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber69DirectStates 15 [tmFiber69StateAt 0] (tmFiber69StateAt 14) tmFiber69State14_in_pass1_full

theorem tmFiber69State15_in_close :
    tmFiber69StateAt 15 ∈ closeChainFiber tmWord tmFiber69DirectStates tmFiber69DirectStates.length [tmFiber69StateAt 0] := by
  change tmFiber69StateAt 15 ∈ closeChainFiber tmWord tmFiber69DirectStates (15 + 1) [tmFiber69StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber69DirectStates 15 [tmFiber69StateAt 0] (tmFiber69StateAt 15) tmFiber69State15_in_pass1_full

theorem tmFiber69DirectConnected :
    chainFiberConnected tmWord tmFiber69DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber69DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber69State0_in_close
  · subst state
    exact tmFiber69State1_in_close
  · subst state
    exact tmFiber69State2_in_close
  · subst state
    exact tmFiber69State3_in_close
  · subst state
    exact tmFiber69State4_in_close
  · subst state
    exact tmFiber69State5_in_close
  · subst state
    exact tmFiber69State6_in_close
  · subst state
    exact tmFiber69State7_in_close
  · subst state
    exact tmFiber69State8_in_close
  · subst state
    exact tmFiber69State9_in_close
  · subst state
    exact tmFiber69State10_in_close
  · subst state
    exact tmFiber69State11_in_close
  · subst state
    exact tmFiber69State12_in_close
  · subst state
    exact tmFiber69State13_in_close
  · subst state
    exact tmFiber69State14_in_close
  · subst state
    exact tmFiber69State15_in_close
  · cases h

def tmFiber71StateAt (i : Nat) : List TauState :=
  directStates (tmFiber71RowAt i).sourceLeft (tmFiber71RowAt i).sourceRight

def tmFiber71DirectStates : List (List TauState) :=
  [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14, tmFiber71StateAt 15]

theorem tmFiber71ReverseRow_1_ok :
    tmRowReverseValid tmFiber71Key tmFiber71Expected (tmFiber71RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber71Chunk0_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber71Chunk0] at h
  exact h.2

theorem tmFiber71ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber71StateAt 0) (tmFiber71StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber71StateAt 0) (tmFiber71StateAt 1)
    (tmFiber71RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber71Key tmFiber71Expected
        (tmFiber71RowAt 1) (by decide) tmFiber71ReverseRow_1_ok
      simpa [tmFiber71StateAt, tmFiber71RowAt, tmFiber71Rows, listGetD, directRow] using h)

theorem tmFiber71ReverseRow_2_ok :
    tmRowReverseValid tmFiber71Key tmFiber71Expected (tmFiber71RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber71Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber71Chunk1] at h
  exact h.1

theorem tmFiber71ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber71StateAt 1) (tmFiber71StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber71StateAt 1) (tmFiber71StateAt 2)
    (tmFiber71RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber71Key tmFiber71Expected
        (tmFiber71RowAt 2) (by decide) tmFiber71ReverseRow_2_ok
      simpa [tmFiber71StateAt, tmFiber71RowAt, tmFiber71Rows, listGetD, directRow] using h)

theorem tmFiber71ReverseRow_3_ok :
    tmRowReverseValid tmFiber71Key tmFiber71Expected (tmFiber71RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber71Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber71Chunk1] at h
  exact h.2

theorem tmFiber71ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber71StateAt 0) (tmFiber71StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber71StateAt 0) (tmFiber71StateAt 3)
    (tmFiber71RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber71Key tmFiber71Expected
        (tmFiber71RowAt 3) (by decide) tmFiber71ReverseRow_3_ok
      simpa [tmFiber71StateAt, tmFiber71RowAt, tmFiber71Rows, listGetD, directRow] using h)

theorem tmFiber71ReverseRow_4_ok :
    tmRowReverseValid tmFiber71Key tmFiber71Expected (tmFiber71RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber71Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber71Chunk2] at h
  exact h.1

theorem tmFiber71ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber71StateAt 0) (tmFiber71StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber71StateAt 0) (tmFiber71StateAt 4)
    (tmFiber71RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber71Key tmFiber71Expected
        (tmFiber71RowAt 4) (by decide) tmFiber71ReverseRow_4_ok
      simpa [tmFiber71StateAt, tmFiber71RowAt, tmFiber71Rows, listGetD, directRow] using h)

theorem tmFiber71ReverseRow_5_ok :
    tmRowReverseValid tmFiber71Key tmFiber71Expected (tmFiber71RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber71Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber71Chunk2] at h
  exact h.2

theorem tmFiber71ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber71StateAt 1) (tmFiber71StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber71StateAt 1) (tmFiber71StateAt 5)
    (tmFiber71RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber71Key tmFiber71Expected
        (tmFiber71RowAt 5) (by decide) tmFiber71ReverseRow_5_ok
      simpa [tmFiber71StateAt, tmFiber71RowAt, tmFiber71Rows, listGetD, directRow] using h)

theorem tmFiber71ReverseRow_6_ok :
    tmRowReverseValid tmFiber71Key tmFiber71Expected (tmFiber71RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber71Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber71Chunk3] at h
  exact h.1

theorem tmFiber71ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber71StateAt 2) (tmFiber71StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber71StateAt 2) (tmFiber71StateAt 6)
    (tmFiber71RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber71Key tmFiber71Expected
        (tmFiber71RowAt 6) (by decide) tmFiber71ReverseRow_6_ok
      simpa [tmFiber71StateAt, tmFiber71RowAt, tmFiber71Rows, listGetD, directRow] using h)

theorem tmFiber71ReverseRow_7_ok :
    tmRowReverseValid tmFiber71Key tmFiber71Expected (tmFiber71RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber71Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber71Chunk3] at h
  exact h.2

theorem tmFiber71ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber71StateAt 3) (tmFiber71StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber71StateAt 3) (tmFiber71StateAt 7)
    (tmFiber71RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber71Key tmFiber71Expected
        (tmFiber71RowAt 7) (by decide) tmFiber71ReverseRow_7_ok
      simpa [tmFiber71StateAt, tmFiber71RowAt, tmFiber71Rows, listGetD, directRow] using h)

theorem tmFiber71ReverseRow_8_ok :
    tmRowReverseValid tmFiber71Key tmFiber71Expected (tmFiber71RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber71Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber71Chunk4] at h
  exact h.1

theorem tmFiber71ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber71StateAt 0) (tmFiber71StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber71StateAt 0) (tmFiber71StateAt 8)
    (tmFiber71RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber71Key tmFiber71Expected
        (tmFiber71RowAt 8) (by decide) tmFiber71ReverseRow_8_ok
      simpa [tmFiber71StateAt, tmFiber71RowAt, tmFiber71Rows, listGetD, directRow] using h)

theorem tmFiber71ReverseRow_9_ok :
    tmRowReverseValid tmFiber71Key tmFiber71Expected (tmFiber71RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber71Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber71Chunk4] at h
  exact h.2

theorem tmFiber71ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber71StateAt 1) (tmFiber71StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber71StateAt 1) (tmFiber71StateAt 9)
    (tmFiber71RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber71Key tmFiber71Expected
        (tmFiber71RowAt 9) (by decide) tmFiber71ReverseRow_9_ok
      simpa [tmFiber71StateAt, tmFiber71RowAt, tmFiber71Rows, listGetD, directRow] using h)

theorem tmFiber71ReverseRow_10_ok :
    tmRowReverseValid tmFiber71Key tmFiber71Expected (tmFiber71RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber71Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber71Chunk5] at h
  exact h.1

theorem tmFiber71ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber71StateAt 2) (tmFiber71StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber71StateAt 2) (tmFiber71StateAt 10)
    (tmFiber71RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber71Key tmFiber71Expected
        (tmFiber71RowAt 10) (by decide) tmFiber71ReverseRow_10_ok
      simpa [tmFiber71StateAt, tmFiber71RowAt, tmFiber71Rows, listGetD, directRow] using h)

theorem tmFiber71ReverseRow_11_ok :
    tmRowReverseValid tmFiber71Key tmFiber71Expected (tmFiber71RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber71Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber71Chunk5] at h
  exact h.2

theorem tmFiber71ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber71StateAt 3) (tmFiber71StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber71StateAt 3) (tmFiber71StateAt 11)
    (tmFiber71RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber71Key tmFiber71Expected
        (tmFiber71RowAt 11) (by decide) tmFiber71ReverseRow_11_ok
      simpa [tmFiber71StateAt, tmFiber71RowAt, tmFiber71Rows, listGetD, directRow] using h)

theorem tmFiber71ReverseRow_12_ok :
    tmRowReverseValid tmFiber71Key tmFiber71Expected (tmFiber71RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber71Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber71Chunk6] at h
  exact h.1

theorem tmFiber71ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber71StateAt 4) (tmFiber71StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber71StateAt 4) (tmFiber71StateAt 12)
    (tmFiber71RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber71Key tmFiber71Expected
        (tmFiber71RowAt 12) (by decide) tmFiber71ReverseRow_12_ok
      simpa [tmFiber71StateAt, tmFiber71RowAt, tmFiber71Rows, listGetD, directRow] using h)

theorem tmFiber71ReverseRow_13_ok :
    tmRowReverseValid tmFiber71Key tmFiber71Expected (tmFiber71RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber71Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber71Chunk6] at h
  exact h.2

theorem tmFiber71ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber71StateAt 5) (tmFiber71StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber71StateAt 5) (tmFiber71StateAt 13)
    (tmFiber71RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber71Key tmFiber71Expected
        (tmFiber71RowAt 13) (by decide) tmFiber71ReverseRow_13_ok
      simpa [tmFiber71StateAt, tmFiber71RowAt, tmFiber71Rows, listGetD, directRow] using h)

theorem tmFiber71ReverseRow_14_ok :
    tmRowReverseValid tmFiber71Key tmFiber71Expected (tmFiber71RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber71Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber71Chunk7] at h
  exact h.1

theorem tmFiber71ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber71StateAt 6) (tmFiber71StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber71StateAt 6) (tmFiber71StateAt 14)
    (tmFiber71RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber71Key tmFiber71Expected
        (tmFiber71RowAt 14) (by decide) tmFiber71ReverseRow_14_ok
      simpa [tmFiber71StateAt, tmFiber71RowAt, tmFiber71Rows, listGetD, directRow] using h)

theorem tmFiber71ReverseRow_15_ok :
    tmRowReverseValid tmFiber71Key tmFiber71Expected (tmFiber71RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber71Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber71Chunk7] at h
  exact h.2

theorem tmFiber71ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber71StateAt 7) (tmFiber71StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber71StateAt 7) (tmFiber71StateAt 15)
    (tmFiber71RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber71Key tmFiber71Expected
        (tmFiber71RowAt 15) (by decide) tmFiber71ReverseRow_15_ok
      simpa [tmFiber71StateAt, tmFiber71RowAt, tmFiber71Rows, listGetD, directRow] using h)

theorem tmFiber71State0_in_pass1_prefix :
    tmFiber71StateAt 0 ∈ chainClosureStep tmWord [tmFiber71StateAt 0] [tmFiber71StateAt 0] := by
  exact chainClosureStep_mem_of_seen tmWord [tmFiber71StateAt 0] [tmFiber71StateAt 0] (tmFiber71StateAt 0) (by simp)

theorem tmFiber71State1_in_pass1_prefix :
    tmFiber71StateAt 1 ∈ chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1] [tmFiber71StateAt 0] := by
  have hparentBefore :
      tmFiber71StateAt 0 ∈ chainClosureStep tmWord [tmFiber71StateAt 0] [tmFiber71StateAt 0] := by
    exact tmFiber71State0_in_pass1_prefix
  rw [show [tmFiber71StateAt 0, tmFiber71StateAt 1] = [tmFiber71StateAt 0] ++ [tmFiber71StateAt 1] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber71StateAt 1) []
    (chainClosureStep tmWord [tmFiber71StateAt 0] [tmFiber71StateAt 0]) (tmFiber71StateAt 0)
    hparentBefore tmFiber71ReverseSingleStep1

theorem tmFiber71State2_in_pass1_prefix :
    tmFiber71StateAt 2 ∈ chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2] [tmFiber71StateAt 0] := by
  have hparentBefore :
      tmFiber71StateAt 1 ∈ chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1] [tmFiber71StateAt 0] := by
    exact tmFiber71State1_in_pass1_prefix
  rw [show [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2] = [tmFiber71StateAt 0, tmFiber71StateAt 1] ++ [tmFiber71StateAt 2] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber71StateAt 2) []
    (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1] [tmFiber71StateAt 0]) (tmFiber71StateAt 1)
    hparentBefore tmFiber71ReverseSingleStep2

theorem tmFiber71State3_in_pass1_prefix :
    tmFiber71StateAt 3 ∈ chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3] [tmFiber71StateAt 0] := by
  have hparentBefore :
      tmFiber71StateAt 0 ∈ chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2] [tmFiber71StateAt 0] := by
    rw [show [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2] = [tmFiber71StateAt 0] ++ [tmFiber71StateAt 1, tmFiber71StateAt 2] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber71StateAt 1, tmFiber71StateAt 2]
      (chainClosureStep tmWord [tmFiber71StateAt 0] [tmFiber71StateAt 0]) (tmFiber71StateAt 0)
      tmFiber71State0_in_pass1_prefix
  rw [show [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3] = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2] ++ [tmFiber71StateAt 3] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber71StateAt 3) []
    (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2] [tmFiber71StateAt 0]) (tmFiber71StateAt 0)
    hparentBefore tmFiber71ReverseSingleStep3

theorem tmFiber71State4_in_pass1_prefix :
    tmFiber71StateAt 4 ∈ chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4] [tmFiber71StateAt 0] := by
  have hparentBefore :
      tmFiber71StateAt 0 ∈ chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3] [tmFiber71StateAt 0] := by
    rw [show [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3] = [tmFiber71StateAt 0] ++ [tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3]
      (chainClosureStep tmWord [tmFiber71StateAt 0] [tmFiber71StateAt 0]) (tmFiber71StateAt 0)
      tmFiber71State0_in_pass1_prefix
  rw [show [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4] = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3] ++ [tmFiber71StateAt 4] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber71StateAt 4) []
    (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3] [tmFiber71StateAt 0]) (tmFiber71StateAt 0)
    hparentBefore tmFiber71ReverseSingleStep4

theorem tmFiber71State5_in_pass1_prefix :
    tmFiber71StateAt 5 ∈ chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5] [tmFiber71StateAt 0] := by
  have hparentBefore :
      tmFiber71StateAt 1 ∈ chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4] [tmFiber71StateAt 0] := by
    rw [show [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4] = [tmFiber71StateAt 0, tmFiber71StateAt 1] ++ [tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4]
      (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1] [tmFiber71StateAt 0]) (tmFiber71StateAt 1)
      tmFiber71State1_in_pass1_prefix
  rw [show [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5] = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4] ++ [tmFiber71StateAt 5] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber71StateAt 5) []
    (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4] [tmFiber71StateAt 0]) (tmFiber71StateAt 1)
    hparentBefore tmFiber71ReverseSingleStep5

theorem tmFiber71State6_in_pass1_prefix :
    tmFiber71StateAt 6 ∈ chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6] [tmFiber71StateAt 0] := by
  have hparentBefore :
      tmFiber71StateAt 2 ∈ chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5] [tmFiber71StateAt 0] := by
    rw [show [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5] = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2] ++ [tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5]
      (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2] [tmFiber71StateAt 0]) (tmFiber71StateAt 2)
      tmFiber71State2_in_pass1_prefix
  rw [show [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6] = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5] ++ [tmFiber71StateAt 6] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber71StateAt 6) []
    (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5] [tmFiber71StateAt 0]) (tmFiber71StateAt 2)
    hparentBefore tmFiber71ReverseSingleStep6

theorem tmFiber71State7_in_pass1_prefix :
    tmFiber71StateAt 7 ∈ chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7] [tmFiber71StateAt 0] := by
  have hparentBefore :
      tmFiber71StateAt 3 ∈ chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6] [tmFiber71StateAt 0] := by
    rw [show [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6] = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3] ++ [tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6]
      (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3] [tmFiber71StateAt 0]) (tmFiber71StateAt 3)
      tmFiber71State3_in_pass1_prefix
  rw [show [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7] = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6] ++ [tmFiber71StateAt 7] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber71StateAt 7) []
    (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6] [tmFiber71StateAt 0]) (tmFiber71StateAt 3)
    hparentBefore tmFiber71ReverseSingleStep7

theorem tmFiber71State8_in_pass1_prefix :
    tmFiber71StateAt 8 ∈ chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8] [tmFiber71StateAt 0] := by
  have hparentBefore :
      tmFiber71StateAt 0 ∈ chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7] [tmFiber71StateAt 0] := by
    rw [show [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7] = [tmFiber71StateAt 0] ++ [tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7]
      (chainClosureStep tmWord [tmFiber71StateAt 0] [tmFiber71StateAt 0]) (tmFiber71StateAt 0)
      tmFiber71State0_in_pass1_prefix
  rw [show [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8] = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7] ++ [tmFiber71StateAt 8] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber71StateAt 8) []
    (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7] [tmFiber71StateAt 0]) (tmFiber71StateAt 0)
    hparentBefore tmFiber71ReverseSingleStep8

theorem tmFiber71State9_in_pass1_prefix :
    tmFiber71StateAt 9 ∈ chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9] [tmFiber71StateAt 0] := by
  have hparentBefore :
      tmFiber71StateAt 1 ∈ chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8] [tmFiber71StateAt 0] := by
    rw [show [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8] = [tmFiber71StateAt 0, tmFiber71StateAt 1] ++ [tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8]
      (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1] [tmFiber71StateAt 0]) (tmFiber71StateAt 1)
      tmFiber71State1_in_pass1_prefix
  rw [show [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9] = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8] ++ [tmFiber71StateAt 9] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber71StateAt 9) []
    (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8] [tmFiber71StateAt 0]) (tmFiber71StateAt 1)
    hparentBefore tmFiber71ReverseSingleStep9

theorem tmFiber71State10_in_pass1_prefix :
    tmFiber71StateAt 10 ∈ chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10] [tmFiber71StateAt 0] := by
  have hparentBefore :
      tmFiber71StateAt 2 ∈ chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9] [tmFiber71StateAt 0] := by
    rw [show [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9] = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2] ++ [tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9]
      (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2] [tmFiber71StateAt 0]) (tmFiber71StateAt 2)
      tmFiber71State2_in_pass1_prefix
  rw [show [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10] = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9] ++ [tmFiber71StateAt 10] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber71StateAt 10) []
    (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9] [tmFiber71StateAt 0]) (tmFiber71StateAt 2)
    hparentBefore tmFiber71ReverseSingleStep10

theorem tmFiber71State11_in_pass1_prefix :
    tmFiber71StateAt 11 ∈ chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11] [tmFiber71StateAt 0] := by
  have hparentBefore :
      tmFiber71StateAt 3 ∈ chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10] [tmFiber71StateAt 0] := by
    rw [show [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10] = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3] ++ [tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10]
      (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3] [tmFiber71StateAt 0]) (tmFiber71StateAt 3)
      tmFiber71State3_in_pass1_prefix
  rw [show [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11] = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10] ++ [tmFiber71StateAt 11] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber71StateAt 11) []
    (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10] [tmFiber71StateAt 0]) (tmFiber71StateAt 3)
    hparentBefore tmFiber71ReverseSingleStep11

theorem tmFiber71State12_in_pass1_prefix :
    tmFiber71StateAt 12 ∈ chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12] [tmFiber71StateAt 0] := by
  have hparentBefore :
      tmFiber71StateAt 4 ∈ chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11] [tmFiber71StateAt 0] := by
    rw [show [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11] = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4] ++ [tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11]
      (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4] [tmFiber71StateAt 0]) (tmFiber71StateAt 4)
      tmFiber71State4_in_pass1_prefix
  rw [show [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12] = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11] ++ [tmFiber71StateAt 12] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber71StateAt 12) []
    (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11] [tmFiber71StateAt 0]) (tmFiber71StateAt 4)
    hparentBefore tmFiber71ReverseSingleStep12

theorem tmFiber71State13_in_pass1_prefix :
    tmFiber71StateAt 13 ∈ chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13] [tmFiber71StateAt 0] := by
  have hparentBefore :
      tmFiber71StateAt 5 ∈ chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12] [tmFiber71StateAt 0] := by
    rw [show [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12] = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5] ++ [tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12]
      (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5] [tmFiber71StateAt 0]) (tmFiber71StateAt 5)
      tmFiber71State5_in_pass1_prefix
  rw [show [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13] = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12] ++ [tmFiber71StateAt 13] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber71StateAt 13) []
    (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12] [tmFiber71StateAt 0]) (tmFiber71StateAt 5)
    hparentBefore tmFiber71ReverseSingleStep13

theorem tmFiber71State14_in_pass1_prefix :
    tmFiber71StateAt 14 ∈ chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14] [tmFiber71StateAt 0] := by
  have hparentBefore :
      tmFiber71StateAt 6 ∈ chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13] [tmFiber71StateAt 0] := by
    rw [show [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13] = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6] ++ [tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13]
      (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6] [tmFiber71StateAt 0]) (tmFiber71StateAt 6)
      tmFiber71State6_in_pass1_prefix
  rw [show [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14] = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13] ++ [tmFiber71StateAt 14] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber71StateAt 14) []
    (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13] [tmFiber71StateAt 0]) (tmFiber71StateAt 6)
    hparentBefore tmFiber71ReverseSingleStep14

theorem tmFiber71State15_in_pass1_prefix :
    tmFiber71StateAt 15 ∈ chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14, tmFiber71StateAt 15] [tmFiber71StateAt 0] := by
  have hparentBefore :
      tmFiber71StateAt 7 ∈ chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14] [tmFiber71StateAt 0] := by
    rw [show [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14] = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7] ++ [tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14]
      (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7] [tmFiber71StateAt 0]) (tmFiber71StateAt 7)
      tmFiber71State7_in_pass1_prefix
  rw [show [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14, tmFiber71StateAt 15] = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14] ++ [tmFiber71StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber71StateAt 15) []
    (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14] [tmFiber71StateAt 0]) (tmFiber71StateAt 7)
    hparentBefore tmFiber71ReverseSingleStep15

theorem tmFiber71State0_in_pass1_full :
    tmFiber71StateAt 0 ∈ chainClosureStep tmWord tmFiber71DirectStates [tmFiber71StateAt 0] := by
  rw [show tmFiber71DirectStates = [tmFiber71StateAt 0] ++ [tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14, tmFiber71StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14, tmFiber71StateAt 15]
    (chainClosureStep tmWord [tmFiber71StateAt 0] [tmFiber71StateAt 0]) (tmFiber71StateAt 0)
    tmFiber71State0_in_pass1_prefix

theorem tmFiber71State1_in_pass1_full :
    tmFiber71StateAt 1 ∈ chainClosureStep tmWord tmFiber71DirectStates [tmFiber71StateAt 0] := by
  rw [show tmFiber71DirectStates = [tmFiber71StateAt 0, tmFiber71StateAt 1] ++ [tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14, tmFiber71StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14, tmFiber71StateAt 15]
    (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1] [tmFiber71StateAt 0]) (tmFiber71StateAt 1)
    tmFiber71State1_in_pass1_prefix

theorem tmFiber71State2_in_pass1_full :
    tmFiber71StateAt 2 ∈ chainClosureStep tmWord tmFiber71DirectStates [tmFiber71StateAt 0] := by
  rw [show tmFiber71DirectStates = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2] ++ [tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14, tmFiber71StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14, tmFiber71StateAt 15]
    (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2] [tmFiber71StateAt 0]) (tmFiber71StateAt 2)
    tmFiber71State2_in_pass1_prefix

theorem tmFiber71State3_in_pass1_full :
    tmFiber71StateAt 3 ∈ chainClosureStep tmWord tmFiber71DirectStates [tmFiber71StateAt 0] := by
  rw [show tmFiber71DirectStates = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3] ++ [tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14, tmFiber71StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14, tmFiber71StateAt 15]
    (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3] [tmFiber71StateAt 0]) (tmFiber71StateAt 3)
    tmFiber71State3_in_pass1_prefix

theorem tmFiber71State4_in_pass1_full :
    tmFiber71StateAt 4 ∈ chainClosureStep tmWord tmFiber71DirectStates [tmFiber71StateAt 0] := by
  rw [show tmFiber71DirectStates = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4] ++ [tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14, tmFiber71StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14, tmFiber71StateAt 15]
    (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4] [tmFiber71StateAt 0]) (tmFiber71StateAt 4)
    tmFiber71State4_in_pass1_prefix

theorem tmFiber71State5_in_pass1_full :
    tmFiber71StateAt 5 ∈ chainClosureStep tmWord tmFiber71DirectStates [tmFiber71StateAt 0] := by
  rw [show tmFiber71DirectStates = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5] ++ [tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14, tmFiber71StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14, tmFiber71StateAt 15]
    (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5] [tmFiber71StateAt 0]) (tmFiber71StateAt 5)
    tmFiber71State5_in_pass1_prefix

theorem tmFiber71State6_in_pass1_full :
    tmFiber71StateAt 6 ∈ chainClosureStep tmWord tmFiber71DirectStates [tmFiber71StateAt 0] := by
  rw [show tmFiber71DirectStates = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6] ++ [tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14, tmFiber71StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14, tmFiber71StateAt 15]
    (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6] [tmFiber71StateAt 0]) (tmFiber71StateAt 6)
    tmFiber71State6_in_pass1_prefix

theorem tmFiber71State7_in_pass1_full :
    tmFiber71StateAt 7 ∈ chainClosureStep tmWord tmFiber71DirectStates [tmFiber71StateAt 0] := by
  rw [show tmFiber71DirectStates = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7] ++ [tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14, tmFiber71StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14, tmFiber71StateAt 15]
    (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7] [tmFiber71StateAt 0]) (tmFiber71StateAt 7)
    tmFiber71State7_in_pass1_prefix

theorem tmFiber71State8_in_pass1_full :
    tmFiber71StateAt 8 ∈ chainClosureStep tmWord tmFiber71DirectStates [tmFiber71StateAt 0] := by
  rw [show tmFiber71DirectStates = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8] ++ [tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14, tmFiber71StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14, tmFiber71StateAt 15]
    (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8] [tmFiber71StateAt 0]) (tmFiber71StateAt 8)
    tmFiber71State8_in_pass1_prefix

theorem tmFiber71State9_in_pass1_full :
    tmFiber71StateAt 9 ∈ chainClosureStep tmWord tmFiber71DirectStates [tmFiber71StateAt 0] := by
  rw [show tmFiber71DirectStates = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9] ++ [tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14, tmFiber71StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14, tmFiber71StateAt 15]
    (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9] [tmFiber71StateAt 0]) (tmFiber71StateAt 9)
    tmFiber71State9_in_pass1_prefix

theorem tmFiber71State10_in_pass1_full :
    tmFiber71StateAt 10 ∈ chainClosureStep tmWord tmFiber71DirectStates [tmFiber71StateAt 0] := by
  rw [show tmFiber71DirectStates = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10] ++ [tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14, tmFiber71StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14, tmFiber71StateAt 15]
    (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10] [tmFiber71StateAt 0]) (tmFiber71StateAt 10)
    tmFiber71State10_in_pass1_prefix

theorem tmFiber71State11_in_pass1_full :
    tmFiber71StateAt 11 ∈ chainClosureStep tmWord tmFiber71DirectStates [tmFiber71StateAt 0] := by
  rw [show tmFiber71DirectStates = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11] ++ [tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14, tmFiber71StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14, tmFiber71StateAt 15]
    (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11] [tmFiber71StateAt 0]) (tmFiber71StateAt 11)
    tmFiber71State11_in_pass1_prefix

theorem tmFiber71State12_in_pass1_full :
    tmFiber71StateAt 12 ∈ chainClosureStep tmWord tmFiber71DirectStates [tmFiber71StateAt 0] := by
  rw [show tmFiber71DirectStates = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12] ++ [tmFiber71StateAt 13, tmFiber71StateAt 14, tmFiber71StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber71StateAt 13, tmFiber71StateAt 14, tmFiber71StateAt 15]
    (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12] [tmFiber71StateAt 0]) (tmFiber71StateAt 12)
    tmFiber71State12_in_pass1_prefix

theorem tmFiber71State13_in_pass1_full :
    tmFiber71StateAt 13 ∈ chainClosureStep tmWord tmFiber71DirectStates [tmFiber71StateAt 0] := by
  rw [show tmFiber71DirectStates = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13] ++ [tmFiber71StateAt 14, tmFiber71StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber71StateAt 14, tmFiber71StateAt 15]
    (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13] [tmFiber71StateAt 0]) (tmFiber71StateAt 13)
    tmFiber71State13_in_pass1_prefix

theorem tmFiber71State14_in_pass1_full :
    tmFiber71StateAt 14 ∈ chainClosureStep tmWord tmFiber71DirectStates [tmFiber71StateAt 0] := by
  rw [show tmFiber71DirectStates = [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14] ++ [tmFiber71StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber71StateAt 15]
    (chainClosureStep tmWord [tmFiber71StateAt 0, tmFiber71StateAt 1, tmFiber71StateAt 2, tmFiber71StateAt 3, tmFiber71StateAt 4, tmFiber71StateAt 5, tmFiber71StateAt 6, tmFiber71StateAt 7, tmFiber71StateAt 8, tmFiber71StateAt 9, tmFiber71StateAt 10, tmFiber71StateAt 11, tmFiber71StateAt 12, tmFiber71StateAt 13, tmFiber71StateAt 14] [tmFiber71StateAt 0]) (tmFiber71StateAt 14)
    tmFiber71State14_in_pass1_prefix

theorem tmFiber71State15_in_pass1_full :
    tmFiber71StateAt 15 ∈ chainClosureStep tmWord tmFiber71DirectStates [tmFiber71StateAt 0] := by
  simpa [tmFiber71DirectStates] using tmFiber71State15_in_pass1_prefix

theorem tmFiber71State0_in_close :
    tmFiber71StateAt 0 ∈ closeChainFiber tmWord tmFiber71DirectStates tmFiber71DirectStates.length [tmFiber71StateAt 0] := by
  change tmFiber71StateAt 0 ∈ closeChainFiber tmWord tmFiber71DirectStates (15 + 1) [tmFiber71StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber71DirectStates 15 [tmFiber71StateAt 0] (tmFiber71StateAt 0) tmFiber71State0_in_pass1_full

theorem tmFiber71State1_in_close :
    tmFiber71StateAt 1 ∈ closeChainFiber tmWord tmFiber71DirectStates tmFiber71DirectStates.length [tmFiber71StateAt 0] := by
  change tmFiber71StateAt 1 ∈ closeChainFiber tmWord tmFiber71DirectStates (15 + 1) [tmFiber71StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber71DirectStates 15 [tmFiber71StateAt 0] (tmFiber71StateAt 1) tmFiber71State1_in_pass1_full

theorem tmFiber71State2_in_close :
    tmFiber71StateAt 2 ∈ closeChainFiber tmWord tmFiber71DirectStates tmFiber71DirectStates.length [tmFiber71StateAt 0] := by
  change tmFiber71StateAt 2 ∈ closeChainFiber tmWord tmFiber71DirectStates (15 + 1) [tmFiber71StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber71DirectStates 15 [tmFiber71StateAt 0] (tmFiber71StateAt 2) tmFiber71State2_in_pass1_full

theorem tmFiber71State3_in_close :
    tmFiber71StateAt 3 ∈ closeChainFiber tmWord tmFiber71DirectStates tmFiber71DirectStates.length [tmFiber71StateAt 0] := by
  change tmFiber71StateAt 3 ∈ closeChainFiber tmWord tmFiber71DirectStates (15 + 1) [tmFiber71StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber71DirectStates 15 [tmFiber71StateAt 0] (tmFiber71StateAt 3) tmFiber71State3_in_pass1_full

theorem tmFiber71State4_in_close :
    tmFiber71StateAt 4 ∈ closeChainFiber tmWord tmFiber71DirectStates tmFiber71DirectStates.length [tmFiber71StateAt 0] := by
  change tmFiber71StateAt 4 ∈ closeChainFiber tmWord tmFiber71DirectStates (15 + 1) [tmFiber71StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber71DirectStates 15 [tmFiber71StateAt 0] (tmFiber71StateAt 4) tmFiber71State4_in_pass1_full

theorem tmFiber71State5_in_close :
    tmFiber71StateAt 5 ∈ closeChainFiber tmWord tmFiber71DirectStates tmFiber71DirectStates.length [tmFiber71StateAt 0] := by
  change tmFiber71StateAt 5 ∈ closeChainFiber tmWord tmFiber71DirectStates (15 + 1) [tmFiber71StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber71DirectStates 15 [tmFiber71StateAt 0] (tmFiber71StateAt 5) tmFiber71State5_in_pass1_full

theorem tmFiber71State6_in_close :
    tmFiber71StateAt 6 ∈ closeChainFiber tmWord tmFiber71DirectStates tmFiber71DirectStates.length [tmFiber71StateAt 0] := by
  change tmFiber71StateAt 6 ∈ closeChainFiber tmWord tmFiber71DirectStates (15 + 1) [tmFiber71StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber71DirectStates 15 [tmFiber71StateAt 0] (tmFiber71StateAt 6) tmFiber71State6_in_pass1_full

theorem tmFiber71State7_in_close :
    tmFiber71StateAt 7 ∈ closeChainFiber tmWord tmFiber71DirectStates tmFiber71DirectStates.length [tmFiber71StateAt 0] := by
  change tmFiber71StateAt 7 ∈ closeChainFiber tmWord tmFiber71DirectStates (15 + 1) [tmFiber71StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber71DirectStates 15 [tmFiber71StateAt 0] (tmFiber71StateAt 7) tmFiber71State7_in_pass1_full

theorem tmFiber71State8_in_close :
    tmFiber71StateAt 8 ∈ closeChainFiber tmWord tmFiber71DirectStates tmFiber71DirectStates.length [tmFiber71StateAt 0] := by
  change tmFiber71StateAt 8 ∈ closeChainFiber tmWord tmFiber71DirectStates (15 + 1) [tmFiber71StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber71DirectStates 15 [tmFiber71StateAt 0] (tmFiber71StateAt 8) tmFiber71State8_in_pass1_full

theorem tmFiber71State9_in_close :
    tmFiber71StateAt 9 ∈ closeChainFiber tmWord tmFiber71DirectStates tmFiber71DirectStates.length [tmFiber71StateAt 0] := by
  change tmFiber71StateAt 9 ∈ closeChainFiber tmWord tmFiber71DirectStates (15 + 1) [tmFiber71StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber71DirectStates 15 [tmFiber71StateAt 0] (tmFiber71StateAt 9) tmFiber71State9_in_pass1_full

theorem tmFiber71State10_in_close :
    tmFiber71StateAt 10 ∈ closeChainFiber tmWord tmFiber71DirectStates tmFiber71DirectStates.length [tmFiber71StateAt 0] := by
  change tmFiber71StateAt 10 ∈ closeChainFiber tmWord tmFiber71DirectStates (15 + 1) [tmFiber71StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber71DirectStates 15 [tmFiber71StateAt 0] (tmFiber71StateAt 10) tmFiber71State10_in_pass1_full

theorem tmFiber71State11_in_close :
    tmFiber71StateAt 11 ∈ closeChainFiber tmWord tmFiber71DirectStates tmFiber71DirectStates.length [tmFiber71StateAt 0] := by
  change tmFiber71StateAt 11 ∈ closeChainFiber tmWord tmFiber71DirectStates (15 + 1) [tmFiber71StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber71DirectStates 15 [tmFiber71StateAt 0] (tmFiber71StateAt 11) tmFiber71State11_in_pass1_full

theorem tmFiber71State12_in_close :
    tmFiber71StateAt 12 ∈ closeChainFiber tmWord tmFiber71DirectStates tmFiber71DirectStates.length [tmFiber71StateAt 0] := by
  change tmFiber71StateAt 12 ∈ closeChainFiber tmWord tmFiber71DirectStates (15 + 1) [tmFiber71StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber71DirectStates 15 [tmFiber71StateAt 0] (tmFiber71StateAt 12) tmFiber71State12_in_pass1_full

theorem tmFiber71State13_in_close :
    tmFiber71StateAt 13 ∈ closeChainFiber tmWord tmFiber71DirectStates tmFiber71DirectStates.length [tmFiber71StateAt 0] := by
  change tmFiber71StateAt 13 ∈ closeChainFiber tmWord tmFiber71DirectStates (15 + 1) [tmFiber71StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber71DirectStates 15 [tmFiber71StateAt 0] (tmFiber71StateAt 13) tmFiber71State13_in_pass1_full

theorem tmFiber71State14_in_close :
    tmFiber71StateAt 14 ∈ closeChainFiber tmWord tmFiber71DirectStates tmFiber71DirectStates.length [tmFiber71StateAt 0] := by
  change tmFiber71StateAt 14 ∈ closeChainFiber tmWord tmFiber71DirectStates (15 + 1) [tmFiber71StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber71DirectStates 15 [tmFiber71StateAt 0] (tmFiber71StateAt 14) tmFiber71State14_in_pass1_full

theorem tmFiber71State15_in_close :
    tmFiber71StateAt 15 ∈ closeChainFiber tmWord tmFiber71DirectStates tmFiber71DirectStates.length [tmFiber71StateAt 0] := by
  change tmFiber71StateAt 15 ∈ closeChainFiber tmWord tmFiber71DirectStates (15 + 1) [tmFiber71StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber71DirectStates 15 [tmFiber71StateAt 0] (tmFiber71StateAt 15) tmFiber71State15_in_pass1_full

theorem tmFiber71DirectConnected :
    chainFiberConnected tmWord tmFiber71DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber71DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber71State0_in_close
  · subst state
    exact tmFiber71State1_in_close
  · subst state
    exact tmFiber71State2_in_close
  · subst state
    exact tmFiber71State3_in_close
  · subst state
    exact tmFiber71State4_in_close
  · subst state
    exact tmFiber71State5_in_close
  · subst state
    exact tmFiber71State6_in_close
  · subst state
    exact tmFiber71State7_in_close
  · subst state
    exact tmFiber71State8_in_close
  · subst state
    exact tmFiber71State9_in_close
  · subst state
    exact tmFiber71State10_in_close
  · subst state
    exact tmFiber71State11_in_close
  · subst state
    exact tmFiber71State12_in_close
  · subst state
    exact tmFiber71State13_in_close
  · subst state
    exact tmFiber71State14_in_close
  · subst state
    exact tmFiber71State15_in_close
  · cases h

end GoertzelLemma818LengthTwoTMShape16Bridge

end Mettapedia.GraphTheory.FourColor
