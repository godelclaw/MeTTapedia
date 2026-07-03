import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for size-16 `normal,mirror` length-two fibers, group 2

This module proves direct connectedness for four generated `normal,mirror`
size-16 fibers from row-local reverse certificate chunks, keeping Lean on
default recursion limits.
-/

namespace GoertzelLemma818LengthTwoTMShape16Bridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818TauMirrorCertificate
open GoertzelLemma818TauMirrorReverseAudit

def tmFiber31StateAt (i : Nat) : List TauState :=
  directStates (tmFiber31RowAt i).sourceLeft (tmFiber31RowAt i).sourceRight

def tmFiber31DirectStates : List (List TauState) :=
  [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14, tmFiber31StateAt 15]

theorem tmFiber31ReverseRow_1_ok :
    tmRowReverseValid tmFiber31Key tmFiber31Expected (tmFiber31RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber31Chunk0_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber31Chunk0] at h
  exact h.2

theorem tmFiber31ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber31StateAt 0) (tmFiber31StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber31StateAt 0) (tmFiber31StateAt 1)
    (tmFiber31RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber31Key tmFiber31Expected
        (tmFiber31RowAt 1) (by decide) tmFiber31ReverseRow_1_ok
      simpa [tmFiber31StateAt, tmFiber31RowAt, tmFiber31Rows, listGetD, directRow] using h)

theorem tmFiber31ReverseRow_2_ok :
    tmRowReverseValid tmFiber31Key tmFiber31Expected (tmFiber31RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber31Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber31Chunk1] at h
  exact h.1

theorem tmFiber31ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber31StateAt 0) (tmFiber31StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber31StateAt 0) (tmFiber31StateAt 2)
    (tmFiber31RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber31Key tmFiber31Expected
        (tmFiber31RowAt 2) (by decide) tmFiber31ReverseRow_2_ok
      simpa [tmFiber31StateAt, tmFiber31RowAt, tmFiber31Rows, listGetD, directRow] using h)

theorem tmFiber31ReverseRow_3_ok :
    tmRowReverseValid tmFiber31Key tmFiber31Expected (tmFiber31RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber31Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber31Chunk1] at h
  exact h.2

theorem tmFiber31ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber31StateAt 1) (tmFiber31StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber31StateAt 1) (tmFiber31StateAt 3)
    (tmFiber31RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber31Key tmFiber31Expected
        (tmFiber31RowAt 3) (by decide) tmFiber31ReverseRow_3_ok
      simpa [tmFiber31StateAt, tmFiber31RowAt, tmFiber31Rows, listGetD, directRow] using h)

theorem tmFiber31ReverseRow_4_ok :
    tmRowReverseValid tmFiber31Key tmFiber31Expected (tmFiber31RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber31Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber31Chunk2] at h
  exact h.1

theorem tmFiber31ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber31StateAt 0) (tmFiber31StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber31StateAt 0) (tmFiber31StateAt 4)
    (tmFiber31RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber31Key tmFiber31Expected
        (tmFiber31RowAt 4) (by decide) tmFiber31ReverseRow_4_ok
      simpa [tmFiber31StateAt, tmFiber31RowAt, tmFiber31Rows, listGetD, directRow] using h)

theorem tmFiber31ReverseRow_5_ok :
    tmRowReverseValid tmFiber31Key tmFiber31Expected (tmFiber31RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber31Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber31Chunk2] at h
  exact h.2

theorem tmFiber31ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber31StateAt 1) (tmFiber31StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber31StateAt 1) (tmFiber31StateAt 5)
    (tmFiber31RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber31Key tmFiber31Expected
        (tmFiber31RowAt 5) (by decide) tmFiber31ReverseRow_5_ok
      simpa [tmFiber31StateAt, tmFiber31RowAt, tmFiber31Rows, listGetD, directRow] using h)

theorem tmFiber31ReverseRow_6_ok :
    tmRowReverseValid tmFiber31Key tmFiber31Expected (tmFiber31RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber31Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber31Chunk3] at h
  exact h.1

theorem tmFiber31ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber31StateAt 2) (tmFiber31StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber31StateAt 2) (tmFiber31StateAt 6)
    (tmFiber31RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber31Key tmFiber31Expected
        (tmFiber31RowAt 6) (by decide) tmFiber31ReverseRow_6_ok
      simpa [tmFiber31StateAt, tmFiber31RowAt, tmFiber31Rows, listGetD, directRow] using h)

theorem tmFiber31ReverseRow_7_ok :
    tmRowReverseValid tmFiber31Key tmFiber31Expected (tmFiber31RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber31Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber31Chunk3] at h
  exact h.2

theorem tmFiber31ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber31StateAt 3) (tmFiber31StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber31StateAt 3) (tmFiber31StateAt 7)
    (tmFiber31RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber31Key tmFiber31Expected
        (tmFiber31RowAt 7) (by decide) tmFiber31ReverseRow_7_ok
      simpa [tmFiber31StateAt, tmFiber31RowAt, tmFiber31Rows, listGetD, directRow] using h)

theorem tmFiber31ReverseRow_8_ok :
    tmRowReverseValid tmFiber31Key tmFiber31Expected (tmFiber31RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber31Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber31Chunk4] at h
  exact h.1

theorem tmFiber31ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber31StateAt 4) (tmFiber31StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber31StateAt 4) (tmFiber31StateAt 8)
    (tmFiber31RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber31Key tmFiber31Expected
        (tmFiber31RowAt 8) (by decide) tmFiber31ReverseRow_8_ok
      simpa [tmFiber31StateAt, tmFiber31RowAt, tmFiber31Rows, listGetD, directRow] using h)

theorem tmFiber31ReverseRow_9_ok :
    tmRowReverseValid tmFiber31Key tmFiber31Expected (tmFiber31RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber31Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber31Chunk4] at h
  exact h.2

theorem tmFiber31ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber31StateAt 5) (tmFiber31StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber31StateAt 5) (tmFiber31StateAt 9)
    (tmFiber31RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber31Key tmFiber31Expected
        (tmFiber31RowAt 9) (by decide) tmFiber31ReverseRow_9_ok
      simpa [tmFiber31StateAt, tmFiber31RowAt, tmFiber31Rows, listGetD, directRow] using h)

theorem tmFiber31ReverseRow_10_ok :
    tmRowReverseValid tmFiber31Key tmFiber31Expected (tmFiber31RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber31Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber31Chunk5] at h
  exact h.1

theorem tmFiber31ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber31StateAt 6) (tmFiber31StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber31StateAt 6) (tmFiber31StateAt 10)
    (tmFiber31RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber31Key tmFiber31Expected
        (tmFiber31RowAt 10) (by decide) tmFiber31ReverseRow_10_ok
      simpa [tmFiber31StateAt, tmFiber31RowAt, tmFiber31Rows, listGetD, directRow] using h)

theorem tmFiber31ReverseRow_11_ok :
    tmRowReverseValid tmFiber31Key tmFiber31Expected (tmFiber31RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber31Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber31Chunk5] at h
  exact h.2

theorem tmFiber31ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber31StateAt 7) (tmFiber31StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber31StateAt 7) (tmFiber31StateAt 11)
    (tmFiber31RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber31Key tmFiber31Expected
        (tmFiber31RowAt 11) (by decide) tmFiber31ReverseRow_11_ok
      simpa [tmFiber31StateAt, tmFiber31RowAt, tmFiber31Rows, listGetD, directRow] using h)

theorem tmFiber31ReverseRow_12_ok :
    tmRowReverseValid tmFiber31Key tmFiber31Expected (tmFiber31RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber31Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber31Chunk6] at h
  exact h.1

theorem tmFiber31ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber31StateAt 0) (tmFiber31StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber31StateAt 0) (tmFiber31StateAt 12)
    (tmFiber31RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber31Key tmFiber31Expected
        (tmFiber31RowAt 12) (by decide) tmFiber31ReverseRow_12_ok
      simpa [tmFiber31StateAt, tmFiber31RowAt, tmFiber31Rows, listGetD, directRow] using h)

theorem tmFiber31ReverseRow_13_ok :
    tmRowReverseValid tmFiber31Key tmFiber31Expected (tmFiber31RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber31Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber31Chunk6] at h
  exact h.2

theorem tmFiber31ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber31StateAt 1) (tmFiber31StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber31StateAt 1) (tmFiber31StateAt 13)
    (tmFiber31RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber31Key tmFiber31Expected
        (tmFiber31RowAt 13) (by decide) tmFiber31ReverseRow_13_ok
      simpa [tmFiber31StateAt, tmFiber31RowAt, tmFiber31Rows, listGetD, directRow] using h)

theorem tmFiber31ReverseRow_14_ok :
    tmRowReverseValid tmFiber31Key tmFiber31Expected (tmFiber31RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber31Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber31Chunk7] at h
  exact h.1

theorem tmFiber31ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber31StateAt 2) (tmFiber31StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber31StateAt 2) (tmFiber31StateAt 14)
    (tmFiber31RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber31Key tmFiber31Expected
        (tmFiber31RowAt 14) (by decide) tmFiber31ReverseRow_14_ok
      simpa [tmFiber31StateAt, tmFiber31RowAt, tmFiber31Rows, listGetD, directRow] using h)

theorem tmFiber31ReverseRow_15_ok :
    tmRowReverseValid tmFiber31Key tmFiber31Expected (tmFiber31RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber31Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber31Chunk7] at h
  exact h.2

theorem tmFiber31ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber31StateAt 3) (tmFiber31StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber31StateAt 3) (tmFiber31StateAt 15)
    (tmFiber31RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber31Key tmFiber31Expected
        (tmFiber31RowAt 15) (by decide) tmFiber31ReverseRow_15_ok
      simpa [tmFiber31StateAt, tmFiber31RowAt, tmFiber31Rows, listGetD, directRow] using h)

theorem tmFiber31State0_in_pass1_prefix :
    tmFiber31StateAt 0 ∈ chainClosureStep tmWord [tmFiber31StateAt 0] [tmFiber31StateAt 0] := by
  exact chainClosureStep_mem_of_seen tmWord [tmFiber31StateAt 0] [tmFiber31StateAt 0] (tmFiber31StateAt 0) (by simp)

theorem tmFiber31State1_in_pass1_prefix :
    tmFiber31StateAt 1 ∈ chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1] [tmFiber31StateAt 0] := by
  have hparentBefore :
      tmFiber31StateAt 0 ∈ chainClosureStep tmWord [tmFiber31StateAt 0] [tmFiber31StateAt 0] := by
    exact tmFiber31State0_in_pass1_prefix
  rw [show [tmFiber31StateAt 0, tmFiber31StateAt 1] = [tmFiber31StateAt 0] ++ [tmFiber31StateAt 1] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber31StateAt 1) []
    (chainClosureStep tmWord [tmFiber31StateAt 0] [tmFiber31StateAt 0]) (tmFiber31StateAt 0)
    hparentBefore tmFiber31ReverseSingleStep1

theorem tmFiber31State2_in_pass1_prefix :
    tmFiber31StateAt 2 ∈ chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2] [tmFiber31StateAt 0] := by
  have hparentBefore :
      tmFiber31StateAt 0 ∈ chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1] [tmFiber31StateAt 0] := by
    rw [show [tmFiber31StateAt 0, tmFiber31StateAt 1] = [tmFiber31StateAt 0] ++ [tmFiber31StateAt 1] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber31StateAt 1]
      (chainClosureStep tmWord [tmFiber31StateAt 0] [tmFiber31StateAt 0]) (tmFiber31StateAt 0)
      tmFiber31State0_in_pass1_prefix
  rw [show [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2] = [tmFiber31StateAt 0, tmFiber31StateAt 1] ++ [tmFiber31StateAt 2] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber31StateAt 2) []
    (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1] [tmFiber31StateAt 0]) (tmFiber31StateAt 0)
    hparentBefore tmFiber31ReverseSingleStep2

theorem tmFiber31State3_in_pass1_prefix :
    tmFiber31StateAt 3 ∈ chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3] [tmFiber31StateAt 0] := by
  have hparentBefore :
      tmFiber31StateAt 1 ∈ chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2] [tmFiber31StateAt 0] := by
    rw [show [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2] = [tmFiber31StateAt 0, tmFiber31StateAt 1] ++ [tmFiber31StateAt 2] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber31StateAt 2]
      (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1] [tmFiber31StateAt 0]) (tmFiber31StateAt 1)
      tmFiber31State1_in_pass1_prefix
  rw [show [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3] = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2] ++ [tmFiber31StateAt 3] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber31StateAt 3) []
    (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2] [tmFiber31StateAt 0]) (tmFiber31StateAt 1)
    hparentBefore tmFiber31ReverseSingleStep3

theorem tmFiber31State4_in_pass1_prefix :
    tmFiber31StateAt 4 ∈ chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4] [tmFiber31StateAt 0] := by
  have hparentBefore :
      tmFiber31StateAt 0 ∈ chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3] [tmFiber31StateAt 0] := by
    rw [show [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3] = [tmFiber31StateAt 0] ++ [tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3]
      (chainClosureStep tmWord [tmFiber31StateAt 0] [tmFiber31StateAt 0]) (tmFiber31StateAt 0)
      tmFiber31State0_in_pass1_prefix
  rw [show [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4] = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3] ++ [tmFiber31StateAt 4] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber31StateAt 4) []
    (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3] [tmFiber31StateAt 0]) (tmFiber31StateAt 0)
    hparentBefore tmFiber31ReverseSingleStep4

theorem tmFiber31State5_in_pass1_prefix :
    tmFiber31StateAt 5 ∈ chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5] [tmFiber31StateAt 0] := by
  have hparentBefore :
      tmFiber31StateAt 1 ∈ chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4] [tmFiber31StateAt 0] := by
    rw [show [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4] = [tmFiber31StateAt 0, tmFiber31StateAt 1] ++ [tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4]
      (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1] [tmFiber31StateAt 0]) (tmFiber31StateAt 1)
      tmFiber31State1_in_pass1_prefix
  rw [show [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5] = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4] ++ [tmFiber31StateAt 5] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber31StateAt 5) []
    (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4] [tmFiber31StateAt 0]) (tmFiber31StateAt 1)
    hparentBefore tmFiber31ReverseSingleStep5

theorem tmFiber31State6_in_pass1_prefix :
    tmFiber31StateAt 6 ∈ chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6] [tmFiber31StateAt 0] := by
  have hparentBefore :
      tmFiber31StateAt 2 ∈ chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5] [tmFiber31StateAt 0] := by
    rw [show [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5] = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2] ++ [tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5]
      (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2] [tmFiber31StateAt 0]) (tmFiber31StateAt 2)
      tmFiber31State2_in_pass1_prefix
  rw [show [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6] = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5] ++ [tmFiber31StateAt 6] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber31StateAt 6) []
    (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5] [tmFiber31StateAt 0]) (tmFiber31StateAt 2)
    hparentBefore tmFiber31ReverseSingleStep6

theorem tmFiber31State7_in_pass1_prefix :
    tmFiber31StateAt 7 ∈ chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7] [tmFiber31StateAt 0] := by
  have hparentBefore :
      tmFiber31StateAt 3 ∈ chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6] [tmFiber31StateAt 0] := by
    rw [show [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6] = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3] ++ [tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6]
      (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3] [tmFiber31StateAt 0]) (tmFiber31StateAt 3)
      tmFiber31State3_in_pass1_prefix
  rw [show [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7] = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6] ++ [tmFiber31StateAt 7] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber31StateAt 7) []
    (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6] [tmFiber31StateAt 0]) (tmFiber31StateAt 3)
    hparentBefore tmFiber31ReverseSingleStep7

theorem tmFiber31State8_in_pass1_prefix :
    tmFiber31StateAt 8 ∈ chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8] [tmFiber31StateAt 0] := by
  have hparentBefore :
      tmFiber31StateAt 4 ∈ chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7] [tmFiber31StateAt 0] := by
    rw [show [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7] = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4] ++ [tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7]
      (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4] [tmFiber31StateAt 0]) (tmFiber31StateAt 4)
      tmFiber31State4_in_pass1_prefix
  rw [show [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8] = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7] ++ [tmFiber31StateAt 8] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber31StateAt 8) []
    (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7] [tmFiber31StateAt 0]) (tmFiber31StateAt 4)
    hparentBefore tmFiber31ReverseSingleStep8

theorem tmFiber31State9_in_pass1_prefix :
    tmFiber31StateAt 9 ∈ chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9] [tmFiber31StateAt 0] := by
  have hparentBefore :
      tmFiber31StateAt 5 ∈ chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8] [tmFiber31StateAt 0] := by
    rw [show [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8] = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5] ++ [tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8]
      (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5] [tmFiber31StateAt 0]) (tmFiber31StateAt 5)
      tmFiber31State5_in_pass1_prefix
  rw [show [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9] = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8] ++ [tmFiber31StateAt 9] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber31StateAt 9) []
    (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8] [tmFiber31StateAt 0]) (tmFiber31StateAt 5)
    hparentBefore tmFiber31ReverseSingleStep9

theorem tmFiber31State10_in_pass1_prefix :
    tmFiber31StateAt 10 ∈ chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10] [tmFiber31StateAt 0] := by
  have hparentBefore :
      tmFiber31StateAt 6 ∈ chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9] [tmFiber31StateAt 0] := by
    rw [show [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9] = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6] ++ [tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9]
      (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6] [tmFiber31StateAt 0]) (tmFiber31StateAt 6)
      tmFiber31State6_in_pass1_prefix
  rw [show [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10] = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9] ++ [tmFiber31StateAt 10] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber31StateAt 10) []
    (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9] [tmFiber31StateAt 0]) (tmFiber31StateAt 6)
    hparentBefore tmFiber31ReverseSingleStep10

theorem tmFiber31State11_in_pass1_prefix :
    tmFiber31StateAt 11 ∈ chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11] [tmFiber31StateAt 0] := by
  have hparentBefore :
      tmFiber31StateAt 7 ∈ chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10] [tmFiber31StateAt 0] := by
    rw [show [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10] = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7] ++ [tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10]
      (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7] [tmFiber31StateAt 0]) (tmFiber31StateAt 7)
      tmFiber31State7_in_pass1_prefix
  rw [show [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11] = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10] ++ [tmFiber31StateAt 11] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber31StateAt 11) []
    (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10] [tmFiber31StateAt 0]) (tmFiber31StateAt 7)
    hparentBefore tmFiber31ReverseSingleStep11

theorem tmFiber31State12_in_pass1_prefix :
    tmFiber31StateAt 12 ∈ chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12] [tmFiber31StateAt 0] := by
  have hparentBefore :
      tmFiber31StateAt 0 ∈ chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11] [tmFiber31StateAt 0] := by
    rw [show [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11] = [tmFiber31StateAt 0] ++ [tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11]
      (chainClosureStep tmWord [tmFiber31StateAt 0] [tmFiber31StateAt 0]) (tmFiber31StateAt 0)
      tmFiber31State0_in_pass1_prefix
  rw [show [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12] = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11] ++ [tmFiber31StateAt 12] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber31StateAt 12) []
    (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11] [tmFiber31StateAt 0]) (tmFiber31StateAt 0)
    hparentBefore tmFiber31ReverseSingleStep12

theorem tmFiber31State13_in_pass1_prefix :
    tmFiber31StateAt 13 ∈ chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13] [tmFiber31StateAt 0] := by
  have hparentBefore :
      tmFiber31StateAt 1 ∈ chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12] [tmFiber31StateAt 0] := by
    rw [show [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12] = [tmFiber31StateAt 0, tmFiber31StateAt 1] ++ [tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12]
      (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1] [tmFiber31StateAt 0]) (tmFiber31StateAt 1)
      tmFiber31State1_in_pass1_prefix
  rw [show [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13] = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12] ++ [tmFiber31StateAt 13] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber31StateAt 13) []
    (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12] [tmFiber31StateAt 0]) (tmFiber31StateAt 1)
    hparentBefore tmFiber31ReverseSingleStep13

theorem tmFiber31State14_in_pass1_prefix :
    tmFiber31StateAt 14 ∈ chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14] [tmFiber31StateAt 0] := by
  have hparentBefore :
      tmFiber31StateAt 2 ∈ chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13] [tmFiber31StateAt 0] := by
    rw [show [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13] = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2] ++ [tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13]
      (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2] [tmFiber31StateAt 0]) (tmFiber31StateAt 2)
      tmFiber31State2_in_pass1_prefix
  rw [show [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14] = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13] ++ [tmFiber31StateAt 14] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber31StateAt 14) []
    (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13] [tmFiber31StateAt 0]) (tmFiber31StateAt 2)
    hparentBefore tmFiber31ReverseSingleStep14

theorem tmFiber31State15_in_pass1_prefix :
    tmFiber31StateAt 15 ∈ chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14, tmFiber31StateAt 15] [tmFiber31StateAt 0] := by
  have hparentBefore :
      tmFiber31StateAt 3 ∈ chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14] [tmFiber31StateAt 0] := by
    rw [show [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14] = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3] ++ [tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14]
      (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3] [tmFiber31StateAt 0]) (tmFiber31StateAt 3)
      tmFiber31State3_in_pass1_prefix
  rw [show [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14, tmFiber31StateAt 15] = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14] ++ [tmFiber31StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber31StateAt 15) []
    (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14] [tmFiber31StateAt 0]) (tmFiber31StateAt 3)
    hparentBefore tmFiber31ReverseSingleStep15

theorem tmFiber31State0_in_pass1_full :
    tmFiber31StateAt 0 ∈ chainClosureStep tmWord tmFiber31DirectStates [tmFiber31StateAt 0] := by
  rw [show tmFiber31DirectStates = [tmFiber31StateAt 0] ++ [tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14, tmFiber31StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14, tmFiber31StateAt 15]
    (chainClosureStep tmWord [tmFiber31StateAt 0] [tmFiber31StateAt 0]) (tmFiber31StateAt 0)
    tmFiber31State0_in_pass1_prefix

theorem tmFiber31State1_in_pass1_full :
    tmFiber31StateAt 1 ∈ chainClosureStep tmWord tmFiber31DirectStates [tmFiber31StateAt 0] := by
  rw [show tmFiber31DirectStates = [tmFiber31StateAt 0, tmFiber31StateAt 1] ++ [tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14, tmFiber31StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14, tmFiber31StateAt 15]
    (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1] [tmFiber31StateAt 0]) (tmFiber31StateAt 1)
    tmFiber31State1_in_pass1_prefix

theorem tmFiber31State2_in_pass1_full :
    tmFiber31StateAt 2 ∈ chainClosureStep tmWord tmFiber31DirectStates [tmFiber31StateAt 0] := by
  rw [show tmFiber31DirectStates = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2] ++ [tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14, tmFiber31StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14, tmFiber31StateAt 15]
    (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2] [tmFiber31StateAt 0]) (tmFiber31StateAt 2)
    tmFiber31State2_in_pass1_prefix

theorem tmFiber31State3_in_pass1_full :
    tmFiber31StateAt 3 ∈ chainClosureStep tmWord tmFiber31DirectStates [tmFiber31StateAt 0] := by
  rw [show tmFiber31DirectStates = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3] ++ [tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14, tmFiber31StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14, tmFiber31StateAt 15]
    (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3] [tmFiber31StateAt 0]) (tmFiber31StateAt 3)
    tmFiber31State3_in_pass1_prefix

theorem tmFiber31State4_in_pass1_full :
    tmFiber31StateAt 4 ∈ chainClosureStep tmWord tmFiber31DirectStates [tmFiber31StateAt 0] := by
  rw [show tmFiber31DirectStates = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4] ++ [tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14, tmFiber31StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14, tmFiber31StateAt 15]
    (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4] [tmFiber31StateAt 0]) (tmFiber31StateAt 4)
    tmFiber31State4_in_pass1_prefix

theorem tmFiber31State5_in_pass1_full :
    tmFiber31StateAt 5 ∈ chainClosureStep tmWord tmFiber31DirectStates [tmFiber31StateAt 0] := by
  rw [show tmFiber31DirectStates = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5] ++ [tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14, tmFiber31StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14, tmFiber31StateAt 15]
    (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5] [tmFiber31StateAt 0]) (tmFiber31StateAt 5)
    tmFiber31State5_in_pass1_prefix

theorem tmFiber31State6_in_pass1_full :
    tmFiber31StateAt 6 ∈ chainClosureStep tmWord tmFiber31DirectStates [tmFiber31StateAt 0] := by
  rw [show tmFiber31DirectStates = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6] ++ [tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14, tmFiber31StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14, tmFiber31StateAt 15]
    (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6] [tmFiber31StateAt 0]) (tmFiber31StateAt 6)
    tmFiber31State6_in_pass1_prefix

theorem tmFiber31State7_in_pass1_full :
    tmFiber31StateAt 7 ∈ chainClosureStep tmWord tmFiber31DirectStates [tmFiber31StateAt 0] := by
  rw [show tmFiber31DirectStates = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7] ++ [tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14, tmFiber31StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14, tmFiber31StateAt 15]
    (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7] [tmFiber31StateAt 0]) (tmFiber31StateAt 7)
    tmFiber31State7_in_pass1_prefix

theorem tmFiber31State8_in_pass1_full :
    tmFiber31StateAt 8 ∈ chainClosureStep tmWord tmFiber31DirectStates [tmFiber31StateAt 0] := by
  rw [show tmFiber31DirectStates = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8] ++ [tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14, tmFiber31StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14, tmFiber31StateAt 15]
    (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8] [tmFiber31StateAt 0]) (tmFiber31StateAt 8)
    tmFiber31State8_in_pass1_prefix

theorem tmFiber31State9_in_pass1_full :
    tmFiber31StateAt 9 ∈ chainClosureStep tmWord tmFiber31DirectStates [tmFiber31StateAt 0] := by
  rw [show tmFiber31DirectStates = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9] ++ [tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14, tmFiber31StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14, tmFiber31StateAt 15]
    (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9] [tmFiber31StateAt 0]) (tmFiber31StateAt 9)
    tmFiber31State9_in_pass1_prefix

theorem tmFiber31State10_in_pass1_full :
    tmFiber31StateAt 10 ∈ chainClosureStep tmWord tmFiber31DirectStates [tmFiber31StateAt 0] := by
  rw [show tmFiber31DirectStates = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10] ++ [tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14, tmFiber31StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14, tmFiber31StateAt 15]
    (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10] [tmFiber31StateAt 0]) (tmFiber31StateAt 10)
    tmFiber31State10_in_pass1_prefix

theorem tmFiber31State11_in_pass1_full :
    tmFiber31StateAt 11 ∈ chainClosureStep tmWord tmFiber31DirectStates [tmFiber31StateAt 0] := by
  rw [show tmFiber31DirectStates = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11] ++ [tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14, tmFiber31StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14, tmFiber31StateAt 15]
    (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11] [tmFiber31StateAt 0]) (tmFiber31StateAt 11)
    tmFiber31State11_in_pass1_prefix

theorem tmFiber31State12_in_pass1_full :
    tmFiber31StateAt 12 ∈ chainClosureStep tmWord tmFiber31DirectStates [tmFiber31StateAt 0] := by
  rw [show tmFiber31DirectStates = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12] ++ [tmFiber31StateAt 13, tmFiber31StateAt 14, tmFiber31StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber31StateAt 13, tmFiber31StateAt 14, tmFiber31StateAt 15]
    (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12] [tmFiber31StateAt 0]) (tmFiber31StateAt 12)
    tmFiber31State12_in_pass1_prefix

theorem tmFiber31State13_in_pass1_full :
    tmFiber31StateAt 13 ∈ chainClosureStep tmWord tmFiber31DirectStates [tmFiber31StateAt 0] := by
  rw [show tmFiber31DirectStates = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13] ++ [tmFiber31StateAt 14, tmFiber31StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber31StateAt 14, tmFiber31StateAt 15]
    (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13] [tmFiber31StateAt 0]) (tmFiber31StateAt 13)
    tmFiber31State13_in_pass1_prefix

theorem tmFiber31State14_in_pass1_full :
    tmFiber31StateAt 14 ∈ chainClosureStep tmWord tmFiber31DirectStates [tmFiber31StateAt 0] := by
  rw [show tmFiber31DirectStates = [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14] ++ [tmFiber31StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber31StateAt 15]
    (chainClosureStep tmWord [tmFiber31StateAt 0, tmFiber31StateAt 1, tmFiber31StateAt 2, tmFiber31StateAt 3, tmFiber31StateAt 4, tmFiber31StateAt 5, tmFiber31StateAt 6, tmFiber31StateAt 7, tmFiber31StateAt 8, tmFiber31StateAt 9, tmFiber31StateAt 10, tmFiber31StateAt 11, tmFiber31StateAt 12, tmFiber31StateAt 13, tmFiber31StateAt 14] [tmFiber31StateAt 0]) (tmFiber31StateAt 14)
    tmFiber31State14_in_pass1_prefix

theorem tmFiber31State15_in_pass1_full :
    tmFiber31StateAt 15 ∈ chainClosureStep tmWord tmFiber31DirectStates [tmFiber31StateAt 0] := by
  simpa [tmFiber31DirectStates] using tmFiber31State15_in_pass1_prefix

theorem tmFiber31State0_in_close :
    tmFiber31StateAt 0 ∈ closeChainFiber tmWord tmFiber31DirectStates tmFiber31DirectStates.length [tmFiber31StateAt 0] := by
  change tmFiber31StateAt 0 ∈ closeChainFiber tmWord tmFiber31DirectStates (15 + 1) [tmFiber31StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber31DirectStates 15 [tmFiber31StateAt 0] (tmFiber31StateAt 0) tmFiber31State0_in_pass1_full

theorem tmFiber31State1_in_close :
    tmFiber31StateAt 1 ∈ closeChainFiber tmWord tmFiber31DirectStates tmFiber31DirectStates.length [tmFiber31StateAt 0] := by
  change tmFiber31StateAt 1 ∈ closeChainFiber tmWord tmFiber31DirectStates (15 + 1) [tmFiber31StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber31DirectStates 15 [tmFiber31StateAt 0] (tmFiber31StateAt 1) tmFiber31State1_in_pass1_full

theorem tmFiber31State2_in_close :
    tmFiber31StateAt 2 ∈ closeChainFiber tmWord tmFiber31DirectStates tmFiber31DirectStates.length [tmFiber31StateAt 0] := by
  change tmFiber31StateAt 2 ∈ closeChainFiber tmWord tmFiber31DirectStates (15 + 1) [tmFiber31StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber31DirectStates 15 [tmFiber31StateAt 0] (tmFiber31StateAt 2) tmFiber31State2_in_pass1_full

theorem tmFiber31State3_in_close :
    tmFiber31StateAt 3 ∈ closeChainFiber tmWord tmFiber31DirectStates tmFiber31DirectStates.length [tmFiber31StateAt 0] := by
  change tmFiber31StateAt 3 ∈ closeChainFiber tmWord tmFiber31DirectStates (15 + 1) [tmFiber31StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber31DirectStates 15 [tmFiber31StateAt 0] (tmFiber31StateAt 3) tmFiber31State3_in_pass1_full

theorem tmFiber31State4_in_close :
    tmFiber31StateAt 4 ∈ closeChainFiber tmWord tmFiber31DirectStates tmFiber31DirectStates.length [tmFiber31StateAt 0] := by
  change tmFiber31StateAt 4 ∈ closeChainFiber tmWord tmFiber31DirectStates (15 + 1) [tmFiber31StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber31DirectStates 15 [tmFiber31StateAt 0] (tmFiber31StateAt 4) tmFiber31State4_in_pass1_full

theorem tmFiber31State5_in_close :
    tmFiber31StateAt 5 ∈ closeChainFiber tmWord tmFiber31DirectStates tmFiber31DirectStates.length [tmFiber31StateAt 0] := by
  change tmFiber31StateAt 5 ∈ closeChainFiber tmWord tmFiber31DirectStates (15 + 1) [tmFiber31StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber31DirectStates 15 [tmFiber31StateAt 0] (tmFiber31StateAt 5) tmFiber31State5_in_pass1_full

theorem tmFiber31State6_in_close :
    tmFiber31StateAt 6 ∈ closeChainFiber tmWord tmFiber31DirectStates tmFiber31DirectStates.length [tmFiber31StateAt 0] := by
  change tmFiber31StateAt 6 ∈ closeChainFiber tmWord tmFiber31DirectStates (15 + 1) [tmFiber31StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber31DirectStates 15 [tmFiber31StateAt 0] (tmFiber31StateAt 6) tmFiber31State6_in_pass1_full

theorem tmFiber31State7_in_close :
    tmFiber31StateAt 7 ∈ closeChainFiber tmWord tmFiber31DirectStates tmFiber31DirectStates.length [tmFiber31StateAt 0] := by
  change tmFiber31StateAt 7 ∈ closeChainFiber tmWord tmFiber31DirectStates (15 + 1) [tmFiber31StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber31DirectStates 15 [tmFiber31StateAt 0] (tmFiber31StateAt 7) tmFiber31State7_in_pass1_full

theorem tmFiber31State8_in_close :
    tmFiber31StateAt 8 ∈ closeChainFiber tmWord tmFiber31DirectStates tmFiber31DirectStates.length [tmFiber31StateAt 0] := by
  change tmFiber31StateAt 8 ∈ closeChainFiber tmWord tmFiber31DirectStates (15 + 1) [tmFiber31StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber31DirectStates 15 [tmFiber31StateAt 0] (tmFiber31StateAt 8) tmFiber31State8_in_pass1_full

theorem tmFiber31State9_in_close :
    tmFiber31StateAt 9 ∈ closeChainFiber tmWord tmFiber31DirectStates tmFiber31DirectStates.length [tmFiber31StateAt 0] := by
  change tmFiber31StateAt 9 ∈ closeChainFiber tmWord tmFiber31DirectStates (15 + 1) [tmFiber31StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber31DirectStates 15 [tmFiber31StateAt 0] (tmFiber31StateAt 9) tmFiber31State9_in_pass1_full

theorem tmFiber31State10_in_close :
    tmFiber31StateAt 10 ∈ closeChainFiber tmWord tmFiber31DirectStates tmFiber31DirectStates.length [tmFiber31StateAt 0] := by
  change tmFiber31StateAt 10 ∈ closeChainFiber tmWord tmFiber31DirectStates (15 + 1) [tmFiber31StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber31DirectStates 15 [tmFiber31StateAt 0] (tmFiber31StateAt 10) tmFiber31State10_in_pass1_full

theorem tmFiber31State11_in_close :
    tmFiber31StateAt 11 ∈ closeChainFiber tmWord tmFiber31DirectStates tmFiber31DirectStates.length [tmFiber31StateAt 0] := by
  change tmFiber31StateAt 11 ∈ closeChainFiber tmWord tmFiber31DirectStates (15 + 1) [tmFiber31StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber31DirectStates 15 [tmFiber31StateAt 0] (tmFiber31StateAt 11) tmFiber31State11_in_pass1_full

theorem tmFiber31State12_in_close :
    tmFiber31StateAt 12 ∈ closeChainFiber tmWord tmFiber31DirectStates tmFiber31DirectStates.length [tmFiber31StateAt 0] := by
  change tmFiber31StateAt 12 ∈ closeChainFiber tmWord tmFiber31DirectStates (15 + 1) [tmFiber31StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber31DirectStates 15 [tmFiber31StateAt 0] (tmFiber31StateAt 12) tmFiber31State12_in_pass1_full

theorem tmFiber31State13_in_close :
    tmFiber31StateAt 13 ∈ closeChainFiber tmWord tmFiber31DirectStates tmFiber31DirectStates.length [tmFiber31StateAt 0] := by
  change tmFiber31StateAt 13 ∈ closeChainFiber tmWord tmFiber31DirectStates (15 + 1) [tmFiber31StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber31DirectStates 15 [tmFiber31StateAt 0] (tmFiber31StateAt 13) tmFiber31State13_in_pass1_full

theorem tmFiber31State14_in_close :
    tmFiber31StateAt 14 ∈ closeChainFiber tmWord tmFiber31DirectStates tmFiber31DirectStates.length [tmFiber31StateAt 0] := by
  change tmFiber31StateAt 14 ∈ closeChainFiber tmWord tmFiber31DirectStates (15 + 1) [tmFiber31StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber31DirectStates 15 [tmFiber31StateAt 0] (tmFiber31StateAt 14) tmFiber31State14_in_pass1_full

theorem tmFiber31State15_in_close :
    tmFiber31StateAt 15 ∈ closeChainFiber tmWord tmFiber31DirectStates tmFiber31DirectStates.length [tmFiber31StateAt 0] := by
  change tmFiber31StateAt 15 ∈ closeChainFiber tmWord tmFiber31DirectStates (15 + 1) [tmFiber31StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber31DirectStates 15 [tmFiber31StateAt 0] (tmFiber31StateAt 15) tmFiber31State15_in_pass1_full

theorem tmFiber31DirectConnected :
    chainFiberConnected tmWord tmFiber31DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber31DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber31State0_in_close
  · subst state
    exact tmFiber31State1_in_close
  · subst state
    exact tmFiber31State2_in_close
  · subst state
    exact tmFiber31State3_in_close
  · subst state
    exact tmFiber31State4_in_close
  · subst state
    exact tmFiber31State5_in_close
  · subst state
    exact tmFiber31State6_in_close
  · subst state
    exact tmFiber31State7_in_close
  · subst state
    exact tmFiber31State8_in_close
  · subst state
    exact tmFiber31State9_in_close
  · subst state
    exact tmFiber31State10_in_close
  · subst state
    exact tmFiber31State11_in_close
  · subst state
    exact tmFiber31State12_in_close
  · subst state
    exact tmFiber31State13_in_close
  · subst state
    exact tmFiber31State14_in_close
  · subst state
    exact tmFiber31State15_in_close
  · cases h

def tmFiber32StateAt (i : Nat) : List TauState :=
  directStates (tmFiber32RowAt i).sourceLeft (tmFiber32RowAt i).sourceRight

def tmFiber32DirectStates : List (List TauState) :=
  [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14, tmFiber32StateAt 15]

theorem tmFiber32ReverseRow_1_ok :
    tmRowReverseValid tmFiber32Key tmFiber32Expected (tmFiber32RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber32Chunk0_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber32Chunk0] at h
  exact h.2

theorem tmFiber32ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber32StateAt 0) (tmFiber32StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber32StateAt 0) (tmFiber32StateAt 1)
    (tmFiber32RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber32Key tmFiber32Expected
        (tmFiber32RowAt 1) (by decide) tmFiber32ReverseRow_1_ok
      simpa [tmFiber32StateAt, tmFiber32RowAt, tmFiber32Rows, listGetD, directRow] using h)

theorem tmFiber32ReverseRow_2_ok :
    tmRowReverseValid tmFiber32Key tmFiber32Expected (tmFiber32RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber32Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber32Chunk1] at h
  exact h.1

theorem tmFiber32ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber32StateAt 0) (tmFiber32StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber32StateAt 0) (tmFiber32StateAt 2)
    (tmFiber32RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber32Key tmFiber32Expected
        (tmFiber32RowAt 2) (by decide) tmFiber32ReverseRow_2_ok
      simpa [tmFiber32StateAt, tmFiber32RowAt, tmFiber32Rows, listGetD, directRow] using h)

theorem tmFiber32ReverseRow_3_ok :
    tmRowReverseValid tmFiber32Key tmFiber32Expected (tmFiber32RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber32Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber32Chunk1] at h
  exact h.2

theorem tmFiber32ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber32StateAt 1) (tmFiber32StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber32StateAt 1) (tmFiber32StateAt 3)
    (tmFiber32RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber32Key tmFiber32Expected
        (tmFiber32RowAt 3) (by decide) tmFiber32ReverseRow_3_ok
      simpa [tmFiber32StateAt, tmFiber32RowAt, tmFiber32Rows, listGetD, directRow] using h)

theorem tmFiber32ReverseRow_4_ok :
    tmRowReverseValid tmFiber32Key tmFiber32Expected (tmFiber32RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber32Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber32Chunk2] at h
  exact h.1

theorem tmFiber32ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber32StateAt 0) (tmFiber32StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber32StateAt 0) (tmFiber32StateAt 4)
    (tmFiber32RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber32Key tmFiber32Expected
        (tmFiber32RowAt 4) (by decide) tmFiber32ReverseRow_4_ok
      simpa [tmFiber32StateAt, tmFiber32RowAt, tmFiber32Rows, listGetD, directRow] using h)

theorem tmFiber32ReverseRow_5_ok :
    tmRowReverseValid tmFiber32Key tmFiber32Expected (tmFiber32RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber32Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber32Chunk2] at h
  exact h.2

theorem tmFiber32ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber32StateAt 1) (tmFiber32StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber32StateAt 1) (tmFiber32StateAt 5)
    (tmFiber32RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber32Key tmFiber32Expected
        (tmFiber32RowAt 5) (by decide) tmFiber32ReverseRow_5_ok
      simpa [tmFiber32StateAt, tmFiber32RowAt, tmFiber32Rows, listGetD, directRow] using h)

theorem tmFiber32ReverseRow_6_ok :
    tmRowReverseValid tmFiber32Key tmFiber32Expected (tmFiber32RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber32Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber32Chunk3] at h
  exact h.1

theorem tmFiber32ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber32StateAt 2) (tmFiber32StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber32StateAt 2) (tmFiber32StateAt 6)
    (tmFiber32RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber32Key tmFiber32Expected
        (tmFiber32RowAt 6) (by decide) tmFiber32ReverseRow_6_ok
      simpa [tmFiber32StateAt, tmFiber32RowAt, tmFiber32Rows, listGetD, directRow] using h)

theorem tmFiber32ReverseRow_7_ok :
    tmRowReverseValid tmFiber32Key tmFiber32Expected (tmFiber32RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber32Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber32Chunk3] at h
  exact h.2

theorem tmFiber32ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber32StateAt 3) (tmFiber32StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber32StateAt 3) (tmFiber32StateAt 7)
    (tmFiber32RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber32Key tmFiber32Expected
        (tmFiber32RowAt 7) (by decide) tmFiber32ReverseRow_7_ok
      simpa [tmFiber32StateAt, tmFiber32RowAt, tmFiber32Rows, listGetD, directRow] using h)

theorem tmFiber32ReverseRow_8_ok :
    tmRowReverseValid tmFiber32Key tmFiber32Expected (tmFiber32RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber32Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber32Chunk4] at h
  exact h.1

theorem tmFiber32ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber32StateAt 0) (tmFiber32StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber32StateAt 0) (tmFiber32StateAt 8)
    (tmFiber32RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber32Key tmFiber32Expected
        (tmFiber32RowAt 8) (by decide) tmFiber32ReverseRow_8_ok
      simpa [tmFiber32StateAt, tmFiber32RowAt, tmFiber32Rows, listGetD, directRow] using h)

theorem tmFiber32ReverseRow_9_ok :
    tmRowReverseValid tmFiber32Key tmFiber32Expected (tmFiber32RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber32Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber32Chunk4] at h
  exact h.2

theorem tmFiber32ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber32StateAt 1) (tmFiber32StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber32StateAt 1) (tmFiber32StateAt 9)
    (tmFiber32RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber32Key tmFiber32Expected
        (tmFiber32RowAt 9) (by decide) tmFiber32ReverseRow_9_ok
      simpa [tmFiber32StateAt, tmFiber32RowAt, tmFiber32Rows, listGetD, directRow] using h)

theorem tmFiber32ReverseRow_10_ok :
    tmRowReverseValid tmFiber32Key tmFiber32Expected (tmFiber32RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber32Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber32Chunk5] at h
  exact h.1

theorem tmFiber32ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber32StateAt 2) (tmFiber32StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber32StateAt 2) (tmFiber32StateAt 10)
    (tmFiber32RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber32Key tmFiber32Expected
        (tmFiber32RowAt 10) (by decide) tmFiber32ReverseRow_10_ok
      simpa [tmFiber32StateAt, tmFiber32RowAt, tmFiber32Rows, listGetD, directRow] using h)

theorem tmFiber32ReverseRow_11_ok :
    tmRowReverseValid tmFiber32Key tmFiber32Expected (tmFiber32RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber32Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber32Chunk5] at h
  exact h.2

theorem tmFiber32ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber32StateAt 3) (tmFiber32StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber32StateAt 3) (tmFiber32StateAt 11)
    (tmFiber32RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber32Key tmFiber32Expected
        (tmFiber32RowAt 11) (by decide) tmFiber32ReverseRow_11_ok
      simpa [tmFiber32StateAt, tmFiber32RowAt, tmFiber32Rows, listGetD, directRow] using h)

theorem tmFiber32ReverseRow_12_ok :
    tmRowReverseValid tmFiber32Key tmFiber32Expected (tmFiber32RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber32Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber32Chunk6] at h
  exact h.1

theorem tmFiber32ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber32StateAt 4) (tmFiber32StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber32StateAt 4) (tmFiber32StateAt 12)
    (tmFiber32RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber32Key tmFiber32Expected
        (tmFiber32RowAt 12) (by decide) tmFiber32ReverseRow_12_ok
      simpa [tmFiber32StateAt, tmFiber32RowAt, tmFiber32Rows, listGetD, directRow] using h)

theorem tmFiber32ReverseRow_13_ok :
    tmRowReverseValid tmFiber32Key tmFiber32Expected (tmFiber32RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber32Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber32Chunk6] at h
  exact h.2

theorem tmFiber32ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber32StateAt 5) (tmFiber32StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber32StateAt 5) (tmFiber32StateAt 13)
    (tmFiber32RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber32Key tmFiber32Expected
        (tmFiber32RowAt 13) (by decide) tmFiber32ReverseRow_13_ok
      simpa [tmFiber32StateAt, tmFiber32RowAt, tmFiber32Rows, listGetD, directRow] using h)

theorem tmFiber32ReverseRow_14_ok :
    tmRowReverseValid tmFiber32Key tmFiber32Expected (tmFiber32RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber32Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber32Chunk7] at h
  exact h.1

theorem tmFiber32ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber32StateAt 6) (tmFiber32StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber32StateAt 6) (tmFiber32StateAt 14)
    (tmFiber32RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber32Key tmFiber32Expected
        (tmFiber32RowAt 14) (by decide) tmFiber32ReverseRow_14_ok
      simpa [tmFiber32StateAt, tmFiber32RowAt, tmFiber32Rows, listGetD, directRow] using h)

theorem tmFiber32ReverseRow_15_ok :
    tmRowReverseValid tmFiber32Key tmFiber32Expected (tmFiber32RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber32Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber32Chunk7] at h
  exact h.2

theorem tmFiber32ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber32StateAt 7) (tmFiber32StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber32StateAt 7) (tmFiber32StateAt 15)
    (tmFiber32RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber32Key tmFiber32Expected
        (tmFiber32RowAt 15) (by decide) tmFiber32ReverseRow_15_ok
      simpa [tmFiber32StateAt, tmFiber32RowAt, tmFiber32Rows, listGetD, directRow] using h)

theorem tmFiber32State0_in_pass1_prefix :
    tmFiber32StateAt 0 ∈ chainClosureStep tmWord [tmFiber32StateAt 0] [tmFiber32StateAt 0] := by
  exact chainClosureStep_mem_of_seen tmWord [tmFiber32StateAt 0] [tmFiber32StateAt 0] (tmFiber32StateAt 0) (by simp)

theorem tmFiber32State1_in_pass1_prefix :
    tmFiber32StateAt 1 ∈ chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1] [tmFiber32StateAt 0] := by
  have hparentBefore :
      tmFiber32StateAt 0 ∈ chainClosureStep tmWord [tmFiber32StateAt 0] [tmFiber32StateAt 0] := by
    exact tmFiber32State0_in_pass1_prefix
  rw [show [tmFiber32StateAt 0, tmFiber32StateAt 1] = [tmFiber32StateAt 0] ++ [tmFiber32StateAt 1] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber32StateAt 1) []
    (chainClosureStep tmWord [tmFiber32StateAt 0] [tmFiber32StateAt 0]) (tmFiber32StateAt 0)
    hparentBefore tmFiber32ReverseSingleStep1

theorem tmFiber32State2_in_pass1_prefix :
    tmFiber32StateAt 2 ∈ chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2] [tmFiber32StateAt 0] := by
  have hparentBefore :
      tmFiber32StateAt 0 ∈ chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1] [tmFiber32StateAt 0] := by
    rw [show [tmFiber32StateAt 0, tmFiber32StateAt 1] = [tmFiber32StateAt 0] ++ [tmFiber32StateAt 1] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber32StateAt 1]
      (chainClosureStep tmWord [tmFiber32StateAt 0] [tmFiber32StateAt 0]) (tmFiber32StateAt 0)
      tmFiber32State0_in_pass1_prefix
  rw [show [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2] = [tmFiber32StateAt 0, tmFiber32StateAt 1] ++ [tmFiber32StateAt 2] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber32StateAt 2) []
    (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1] [tmFiber32StateAt 0]) (tmFiber32StateAt 0)
    hparentBefore tmFiber32ReverseSingleStep2

theorem tmFiber32State3_in_pass1_prefix :
    tmFiber32StateAt 3 ∈ chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3] [tmFiber32StateAt 0] := by
  have hparentBefore :
      tmFiber32StateAt 1 ∈ chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2] [tmFiber32StateAt 0] := by
    rw [show [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2] = [tmFiber32StateAt 0, tmFiber32StateAt 1] ++ [tmFiber32StateAt 2] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber32StateAt 2]
      (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1] [tmFiber32StateAt 0]) (tmFiber32StateAt 1)
      tmFiber32State1_in_pass1_prefix
  rw [show [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3] = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2] ++ [tmFiber32StateAt 3] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber32StateAt 3) []
    (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2] [tmFiber32StateAt 0]) (tmFiber32StateAt 1)
    hparentBefore tmFiber32ReverseSingleStep3

theorem tmFiber32State4_in_pass1_prefix :
    tmFiber32StateAt 4 ∈ chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4] [tmFiber32StateAt 0] := by
  have hparentBefore :
      tmFiber32StateAt 0 ∈ chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3] [tmFiber32StateAt 0] := by
    rw [show [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3] = [tmFiber32StateAt 0] ++ [tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3]
      (chainClosureStep tmWord [tmFiber32StateAt 0] [tmFiber32StateAt 0]) (tmFiber32StateAt 0)
      tmFiber32State0_in_pass1_prefix
  rw [show [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4] = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3] ++ [tmFiber32StateAt 4] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber32StateAt 4) []
    (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3] [tmFiber32StateAt 0]) (tmFiber32StateAt 0)
    hparentBefore tmFiber32ReverseSingleStep4

theorem tmFiber32State5_in_pass1_prefix :
    tmFiber32StateAt 5 ∈ chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5] [tmFiber32StateAt 0] := by
  have hparentBefore :
      tmFiber32StateAt 1 ∈ chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4] [tmFiber32StateAt 0] := by
    rw [show [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4] = [tmFiber32StateAt 0, tmFiber32StateAt 1] ++ [tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4]
      (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1] [tmFiber32StateAt 0]) (tmFiber32StateAt 1)
      tmFiber32State1_in_pass1_prefix
  rw [show [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5] = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4] ++ [tmFiber32StateAt 5] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber32StateAt 5) []
    (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4] [tmFiber32StateAt 0]) (tmFiber32StateAt 1)
    hparentBefore tmFiber32ReverseSingleStep5

theorem tmFiber32State6_in_pass1_prefix :
    tmFiber32StateAt 6 ∈ chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6] [tmFiber32StateAt 0] := by
  have hparentBefore :
      tmFiber32StateAt 2 ∈ chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5] [tmFiber32StateAt 0] := by
    rw [show [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5] = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2] ++ [tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5]
      (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2] [tmFiber32StateAt 0]) (tmFiber32StateAt 2)
      tmFiber32State2_in_pass1_prefix
  rw [show [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6] = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5] ++ [tmFiber32StateAt 6] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber32StateAt 6) []
    (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5] [tmFiber32StateAt 0]) (tmFiber32StateAt 2)
    hparentBefore tmFiber32ReverseSingleStep6

theorem tmFiber32State7_in_pass1_prefix :
    tmFiber32StateAt 7 ∈ chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7] [tmFiber32StateAt 0] := by
  have hparentBefore :
      tmFiber32StateAt 3 ∈ chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6] [tmFiber32StateAt 0] := by
    rw [show [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6] = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3] ++ [tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6]
      (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3] [tmFiber32StateAt 0]) (tmFiber32StateAt 3)
      tmFiber32State3_in_pass1_prefix
  rw [show [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7] = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6] ++ [tmFiber32StateAt 7] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber32StateAt 7) []
    (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6] [tmFiber32StateAt 0]) (tmFiber32StateAt 3)
    hparentBefore tmFiber32ReverseSingleStep7

theorem tmFiber32State8_in_pass1_prefix :
    tmFiber32StateAt 8 ∈ chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8] [tmFiber32StateAt 0] := by
  have hparentBefore :
      tmFiber32StateAt 0 ∈ chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7] [tmFiber32StateAt 0] := by
    rw [show [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7] = [tmFiber32StateAt 0] ++ [tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7]
      (chainClosureStep tmWord [tmFiber32StateAt 0] [tmFiber32StateAt 0]) (tmFiber32StateAt 0)
      tmFiber32State0_in_pass1_prefix
  rw [show [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8] = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7] ++ [tmFiber32StateAt 8] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber32StateAt 8) []
    (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7] [tmFiber32StateAt 0]) (tmFiber32StateAt 0)
    hparentBefore tmFiber32ReverseSingleStep8

theorem tmFiber32State9_in_pass1_prefix :
    tmFiber32StateAt 9 ∈ chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9] [tmFiber32StateAt 0] := by
  have hparentBefore :
      tmFiber32StateAt 1 ∈ chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8] [tmFiber32StateAt 0] := by
    rw [show [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8] = [tmFiber32StateAt 0, tmFiber32StateAt 1] ++ [tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8]
      (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1] [tmFiber32StateAt 0]) (tmFiber32StateAt 1)
      tmFiber32State1_in_pass1_prefix
  rw [show [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9] = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8] ++ [tmFiber32StateAt 9] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber32StateAt 9) []
    (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8] [tmFiber32StateAt 0]) (tmFiber32StateAt 1)
    hparentBefore tmFiber32ReverseSingleStep9

theorem tmFiber32State10_in_pass1_prefix :
    tmFiber32StateAt 10 ∈ chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10] [tmFiber32StateAt 0] := by
  have hparentBefore :
      tmFiber32StateAt 2 ∈ chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9] [tmFiber32StateAt 0] := by
    rw [show [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9] = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2] ++ [tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9]
      (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2] [tmFiber32StateAt 0]) (tmFiber32StateAt 2)
      tmFiber32State2_in_pass1_prefix
  rw [show [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10] = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9] ++ [tmFiber32StateAt 10] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber32StateAt 10) []
    (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9] [tmFiber32StateAt 0]) (tmFiber32StateAt 2)
    hparentBefore tmFiber32ReverseSingleStep10

theorem tmFiber32State11_in_pass1_prefix :
    tmFiber32StateAt 11 ∈ chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11] [tmFiber32StateAt 0] := by
  have hparentBefore :
      tmFiber32StateAt 3 ∈ chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10] [tmFiber32StateAt 0] := by
    rw [show [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10] = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3] ++ [tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10]
      (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3] [tmFiber32StateAt 0]) (tmFiber32StateAt 3)
      tmFiber32State3_in_pass1_prefix
  rw [show [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11] = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10] ++ [tmFiber32StateAt 11] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber32StateAt 11) []
    (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10] [tmFiber32StateAt 0]) (tmFiber32StateAt 3)
    hparentBefore tmFiber32ReverseSingleStep11

theorem tmFiber32State12_in_pass1_prefix :
    tmFiber32StateAt 12 ∈ chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12] [tmFiber32StateAt 0] := by
  have hparentBefore :
      tmFiber32StateAt 4 ∈ chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11] [tmFiber32StateAt 0] := by
    rw [show [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11] = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4] ++ [tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11]
      (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4] [tmFiber32StateAt 0]) (tmFiber32StateAt 4)
      tmFiber32State4_in_pass1_prefix
  rw [show [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12] = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11] ++ [tmFiber32StateAt 12] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber32StateAt 12) []
    (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11] [tmFiber32StateAt 0]) (tmFiber32StateAt 4)
    hparentBefore tmFiber32ReverseSingleStep12

theorem tmFiber32State13_in_pass1_prefix :
    tmFiber32StateAt 13 ∈ chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13] [tmFiber32StateAt 0] := by
  have hparentBefore :
      tmFiber32StateAt 5 ∈ chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12] [tmFiber32StateAt 0] := by
    rw [show [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12] = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5] ++ [tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12]
      (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5] [tmFiber32StateAt 0]) (tmFiber32StateAt 5)
      tmFiber32State5_in_pass1_prefix
  rw [show [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13] = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12] ++ [tmFiber32StateAt 13] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber32StateAt 13) []
    (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12] [tmFiber32StateAt 0]) (tmFiber32StateAt 5)
    hparentBefore tmFiber32ReverseSingleStep13

theorem tmFiber32State14_in_pass1_prefix :
    tmFiber32StateAt 14 ∈ chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14] [tmFiber32StateAt 0] := by
  have hparentBefore :
      tmFiber32StateAt 6 ∈ chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13] [tmFiber32StateAt 0] := by
    rw [show [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13] = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6] ++ [tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13]
      (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6] [tmFiber32StateAt 0]) (tmFiber32StateAt 6)
      tmFiber32State6_in_pass1_prefix
  rw [show [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14] = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13] ++ [tmFiber32StateAt 14] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber32StateAt 14) []
    (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13] [tmFiber32StateAt 0]) (tmFiber32StateAt 6)
    hparentBefore tmFiber32ReverseSingleStep14

theorem tmFiber32State15_in_pass1_prefix :
    tmFiber32StateAt 15 ∈ chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14, tmFiber32StateAt 15] [tmFiber32StateAt 0] := by
  have hparentBefore :
      tmFiber32StateAt 7 ∈ chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14] [tmFiber32StateAt 0] := by
    rw [show [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14] = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7] ++ [tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14]
      (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7] [tmFiber32StateAt 0]) (tmFiber32StateAt 7)
      tmFiber32State7_in_pass1_prefix
  rw [show [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14, tmFiber32StateAt 15] = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14] ++ [tmFiber32StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber32StateAt 15) []
    (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14] [tmFiber32StateAt 0]) (tmFiber32StateAt 7)
    hparentBefore tmFiber32ReverseSingleStep15

theorem tmFiber32State0_in_pass1_full :
    tmFiber32StateAt 0 ∈ chainClosureStep tmWord tmFiber32DirectStates [tmFiber32StateAt 0] := by
  rw [show tmFiber32DirectStates = [tmFiber32StateAt 0] ++ [tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14, tmFiber32StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14, tmFiber32StateAt 15]
    (chainClosureStep tmWord [tmFiber32StateAt 0] [tmFiber32StateAt 0]) (tmFiber32StateAt 0)
    tmFiber32State0_in_pass1_prefix

theorem tmFiber32State1_in_pass1_full :
    tmFiber32StateAt 1 ∈ chainClosureStep tmWord tmFiber32DirectStates [tmFiber32StateAt 0] := by
  rw [show tmFiber32DirectStates = [tmFiber32StateAt 0, tmFiber32StateAt 1] ++ [tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14, tmFiber32StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14, tmFiber32StateAt 15]
    (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1] [tmFiber32StateAt 0]) (tmFiber32StateAt 1)
    tmFiber32State1_in_pass1_prefix

theorem tmFiber32State2_in_pass1_full :
    tmFiber32StateAt 2 ∈ chainClosureStep tmWord tmFiber32DirectStates [tmFiber32StateAt 0] := by
  rw [show tmFiber32DirectStates = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2] ++ [tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14, tmFiber32StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14, tmFiber32StateAt 15]
    (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2] [tmFiber32StateAt 0]) (tmFiber32StateAt 2)
    tmFiber32State2_in_pass1_prefix

theorem tmFiber32State3_in_pass1_full :
    tmFiber32StateAt 3 ∈ chainClosureStep tmWord tmFiber32DirectStates [tmFiber32StateAt 0] := by
  rw [show tmFiber32DirectStates = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3] ++ [tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14, tmFiber32StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14, tmFiber32StateAt 15]
    (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3] [tmFiber32StateAt 0]) (tmFiber32StateAt 3)
    tmFiber32State3_in_pass1_prefix

theorem tmFiber32State4_in_pass1_full :
    tmFiber32StateAt 4 ∈ chainClosureStep tmWord tmFiber32DirectStates [tmFiber32StateAt 0] := by
  rw [show tmFiber32DirectStates = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4] ++ [tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14, tmFiber32StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14, tmFiber32StateAt 15]
    (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4] [tmFiber32StateAt 0]) (tmFiber32StateAt 4)
    tmFiber32State4_in_pass1_prefix

theorem tmFiber32State5_in_pass1_full :
    tmFiber32StateAt 5 ∈ chainClosureStep tmWord tmFiber32DirectStates [tmFiber32StateAt 0] := by
  rw [show tmFiber32DirectStates = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5] ++ [tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14, tmFiber32StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14, tmFiber32StateAt 15]
    (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5] [tmFiber32StateAt 0]) (tmFiber32StateAt 5)
    tmFiber32State5_in_pass1_prefix

theorem tmFiber32State6_in_pass1_full :
    tmFiber32StateAt 6 ∈ chainClosureStep tmWord tmFiber32DirectStates [tmFiber32StateAt 0] := by
  rw [show tmFiber32DirectStates = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6] ++ [tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14, tmFiber32StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14, tmFiber32StateAt 15]
    (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6] [tmFiber32StateAt 0]) (tmFiber32StateAt 6)
    tmFiber32State6_in_pass1_prefix

theorem tmFiber32State7_in_pass1_full :
    tmFiber32StateAt 7 ∈ chainClosureStep tmWord tmFiber32DirectStates [tmFiber32StateAt 0] := by
  rw [show tmFiber32DirectStates = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7] ++ [tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14, tmFiber32StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14, tmFiber32StateAt 15]
    (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7] [tmFiber32StateAt 0]) (tmFiber32StateAt 7)
    tmFiber32State7_in_pass1_prefix

theorem tmFiber32State8_in_pass1_full :
    tmFiber32StateAt 8 ∈ chainClosureStep tmWord tmFiber32DirectStates [tmFiber32StateAt 0] := by
  rw [show tmFiber32DirectStates = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8] ++ [tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14, tmFiber32StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14, tmFiber32StateAt 15]
    (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8] [tmFiber32StateAt 0]) (tmFiber32StateAt 8)
    tmFiber32State8_in_pass1_prefix

theorem tmFiber32State9_in_pass1_full :
    tmFiber32StateAt 9 ∈ chainClosureStep tmWord tmFiber32DirectStates [tmFiber32StateAt 0] := by
  rw [show tmFiber32DirectStates = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9] ++ [tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14, tmFiber32StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14, tmFiber32StateAt 15]
    (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9] [tmFiber32StateAt 0]) (tmFiber32StateAt 9)
    tmFiber32State9_in_pass1_prefix

theorem tmFiber32State10_in_pass1_full :
    tmFiber32StateAt 10 ∈ chainClosureStep tmWord tmFiber32DirectStates [tmFiber32StateAt 0] := by
  rw [show tmFiber32DirectStates = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10] ++ [tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14, tmFiber32StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14, tmFiber32StateAt 15]
    (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10] [tmFiber32StateAt 0]) (tmFiber32StateAt 10)
    tmFiber32State10_in_pass1_prefix

theorem tmFiber32State11_in_pass1_full :
    tmFiber32StateAt 11 ∈ chainClosureStep tmWord tmFiber32DirectStates [tmFiber32StateAt 0] := by
  rw [show tmFiber32DirectStates = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11] ++ [tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14, tmFiber32StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14, tmFiber32StateAt 15]
    (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11] [tmFiber32StateAt 0]) (tmFiber32StateAt 11)
    tmFiber32State11_in_pass1_prefix

theorem tmFiber32State12_in_pass1_full :
    tmFiber32StateAt 12 ∈ chainClosureStep tmWord tmFiber32DirectStates [tmFiber32StateAt 0] := by
  rw [show tmFiber32DirectStates = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12] ++ [tmFiber32StateAt 13, tmFiber32StateAt 14, tmFiber32StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber32StateAt 13, tmFiber32StateAt 14, tmFiber32StateAt 15]
    (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12] [tmFiber32StateAt 0]) (tmFiber32StateAt 12)
    tmFiber32State12_in_pass1_prefix

theorem tmFiber32State13_in_pass1_full :
    tmFiber32StateAt 13 ∈ chainClosureStep tmWord tmFiber32DirectStates [tmFiber32StateAt 0] := by
  rw [show tmFiber32DirectStates = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13] ++ [tmFiber32StateAt 14, tmFiber32StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber32StateAt 14, tmFiber32StateAt 15]
    (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13] [tmFiber32StateAt 0]) (tmFiber32StateAt 13)
    tmFiber32State13_in_pass1_prefix

theorem tmFiber32State14_in_pass1_full :
    tmFiber32StateAt 14 ∈ chainClosureStep tmWord tmFiber32DirectStates [tmFiber32StateAt 0] := by
  rw [show tmFiber32DirectStates = [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14] ++ [tmFiber32StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber32StateAt 15]
    (chainClosureStep tmWord [tmFiber32StateAt 0, tmFiber32StateAt 1, tmFiber32StateAt 2, tmFiber32StateAt 3, tmFiber32StateAt 4, tmFiber32StateAt 5, tmFiber32StateAt 6, tmFiber32StateAt 7, tmFiber32StateAt 8, tmFiber32StateAt 9, tmFiber32StateAt 10, tmFiber32StateAt 11, tmFiber32StateAt 12, tmFiber32StateAt 13, tmFiber32StateAt 14] [tmFiber32StateAt 0]) (tmFiber32StateAt 14)
    tmFiber32State14_in_pass1_prefix

theorem tmFiber32State15_in_pass1_full :
    tmFiber32StateAt 15 ∈ chainClosureStep tmWord tmFiber32DirectStates [tmFiber32StateAt 0] := by
  simpa [tmFiber32DirectStates] using tmFiber32State15_in_pass1_prefix

theorem tmFiber32State0_in_close :
    tmFiber32StateAt 0 ∈ closeChainFiber tmWord tmFiber32DirectStates tmFiber32DirectStates.length [tmFiber32StateAt 0] := by
  change tmFiber32StateAt 0 ∈ closeChainFiber tmWord tmFiber32DirectStates (15 + 1) [tmFiber32StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber32DirectStates 15 [tmFiber32StateAt 0] (tmFiber32StateAt 0) tmFiber32State0_in_pass1_full

theorem tmFiber32State1_in_close :
    tmFiber32StateAt 1 ∈ closeChainFiber tmWord tmFiber32DirectStates tmFiber32DirectStates.length [tmFiber32StateAt 0] := by
  change tmFiber32StateAt 1 ∈ closeChainFiber tmWord tmFiber32DirectStates (15 + 1) [tmFiber32StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber32DirectStates 15 [tmFiber32StateAt 0] (tmFiber32StateAt 1) tmFiber32State1_in_pass1_full

theorem tmFiber32State2_in_close :
    tmFiber32StateAt 2 ∈ closeChainFiber tmWord tmFiber32DirectStates tmFiber32DirectStates.length [tmFiber32StateAt 0] := by
  change tmFiber32StateAt 2 ∈ closeChainFiber tmWord tmFiber32DirectStates (15 + 1) [tmFiber32StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber32DirectStates 15 [tmFiber32StateAt 0] (tmFiber32StateAt 2) tmFiber32State2_in_pass1_full

theorem tmFiber32State3_in_close :
    tmFiber32StateAt 3 ∈ closeChainFiber tmWord tmFiber32DirectStates tmFiber32DirectStates.length [tmFiber32StateAt 0] := by
  change tmFiber32StateAt 3 ∈ closeChainFiber tmWord tmFiber32DirectStates (15 + 1) [tmFiber32StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber32DirectStates 15 [tmFiber32StateAt 0] (tmFiber32StateAt 3) tmFiber32State3_in_pass1_full

theorem tmFiber32State4_in_close :
    tmFiber32StateAt 4 ∈ closeChainFiber tmWord tmFiber32DirectStates tmFiber32DirectStates.length [tmFiber32StateAt 0] := by
  change tmFiber32StateAt 4 ∈ closeChainFiber tmWord tmFiber32DirectStates (15 + 1) [tmFiber32StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber32DirectStates 15 [tmFiber32StateAt 0] (tmFiber32StateAt 4) tmFiber32State4_in_pass1_full

theorem tmFiber32State5_in_close :
    tmFiber32StateAt 5 ∈ closeChainFiber tmWord tmFiber32DirectStates tmFiber32DirectStates.length [tmFiber32StateAt 0] := by
  change tmFiber32StateAt 5 ∈ closeChainFiber tmWord tmFiber32DirectStates (15 + 1) [tmFiber32StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber32DirectStates 15 [tmFiber32StateAt 0] (tmFiber32StateAt 5) tmFiber32State5_in_pass1_full

theorem tmFiber32State6_in_close :
    tmFiber32StateAt 6 ∈ closeChainFiber tmWord tmFiber32DirectStates tmFiber32DirectStates.length [tmFiber32StateAt 0] := by
  change tmFiber32StateAt 6 ∈ closeChainFiber tmWord tmFiber32DirectStates (15 + 1) [tmFiber32StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber32DirectStates 15 [tmFiber32StateAt 0] (tmFiber32StateAt 6) tmFiber32State6_in_pass1_full

theorem tmFiber32State7_in_close :
    tmFiber32StateAt 7 ∈ closeChainFiber tmWord tmFiber32DirectStates tmFiber32DirectStates.length [tmFiber32StateAt 0] := by
  change tmFiber32StateAt 7 ∈ closeChainFiber tmWord tmFiber32DirectStates (15 + 1) [tmFiber32StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber32DirectStates 15 [tmFiber32StateAt 0] (tmFiber32StateAt 7) tmFiber32State7_in_pass1_full

theorem tmFiber32State8_in_close :
    tmFiber32StateAt 8 ∈ closeChainFiber tmWord tmFiber32DirectStates tmFiber32DirectStates.length [tmFiber32StateAt 0] := by
  change tmFiber32StateAt 8 ∈ closeChainFiber tmWord tmFiber32DirectStates (15 + 1) [tmFiber32StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber32DirectStates 15 [tmFiber32StateAt 0] (tmFiber32StateAt 8) tmFiber32State8_in_pass1_full

theorem tmFiber32State9_in_close :
    tmFiber32StateAt 9 ∈ closeChainFiber tmWord tmFiber32DirectStates tmFiber32DirectStates.length [tmFiber32StateAt 0] := by
  change tmFiber32StateAt 9 ∈ closeChainFiber tmWord tmFiber32DirectStates (15 + 1) [tmFiber32StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber32DirectStates 15 [tmFiber32StateAt 0] (tmFiber32StateAt 9) tmFiber32State9_in_pass1_full

theorem tmFiber32State10_in_close :
    tmFiber32StateAt 10 ∈ closeChainFiber tmWord tmFiber32DirectStates tmFiber32DirectStates.length [tmFiber32StateAt 0] := by
  change tmFiber32StateAt 10 ∈ closeChainFiber tmWord tmFiber32DirectStates (15 + 1) [tmFiber32StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber32DirectStates 15 [tmFiber32StateAt 0] (tmFiber32StateAt 10) tmFiber32State10_in_pass1_full

theorem tmFiber32State11_in_close :
    tmFiber32StateAt 11 ∈ closeChainFiber tmWord tmFiber32DirectStates tmFiber32DirectStates.length [tmFiber32StateAt 0] := by
  change tmFiber32StateAt 11 ∈ closeChainFiber tmWord tmFiber32DirectStates (15 + 1) [tmFiber32StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber32DirectStates 15 [tmFiber32StateAt 0] (tmFiber32StateAt 11) tmFiber32State11_in_pass1_full

theorem tmFiber32State12_in_close :
    tmFiber32StateAt 12 ∈ closeChainFiber tmWord tmFiber32DirectStates tmFiber32DirectStates.length [tmFiber32StateAt 0] := by
  change tmFiber32StateAt 12 ∈ closeChainFiber tmWord tmFiber32DirectStates (15 + 1) [tmFiber32StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber32DirectStates 15 [tmFiber32StateAt 0] (tmFiber32StateAt 12) tmFiber32State12_in_pass1_full

theorem tmFiber32State13_in_close :
    tmFiber32StateAt 13 ∈ closeChainFiber tmWord tmFiber32DirectStates tmFiber32DirectStates.length [tmFiber32StateAt 0] := by
  change tmFiber32StateAt 13 ∈ closeChainFiber tmWord tmFiber32DirectStates (15 + 1) [tmFiber32StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber32DirectStates 15 [tmFiber32StateAt 0] (tmFiber32StateAt 13) tmFiber32State13_in_pass1_full

theorem tmFiber32State14_in_close :
    tmFiber32StateAt 14 ∈ closeChainFiber tmWord tmFiber32DirectStates tmFiber32DirectStates.length [tmFiber32StateAt 0] := by
  change tmFiber32StateAt 14 ∈ closeChainFiber tmWord tmFiber32DirectStates (15 + 1) [tmFiber32StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber32DirectStates 15 [tmFiber32StateAt 0] (tmFiber32StateAt 14) tmFiber32State14_in_pass1_full

theorem tmFiber32State15_in_close :
    tmFiber32StateAt 15 ∈ closeChainFiber tmWord tmFiber32DirectStates tmFiber32DirectStates.length [tmFiber32StateAt 0] := by
  change tmFiber32StateAt 15 ∈ closeChainFiber tmWord tmFiber32DirectStates (15 + 1) [tmFiber32StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber32DirectStates 15 [tmFiber32StateAt 0] (tmFiber32StateAt 15) tmFiber32State15_in_pass1_full

theorem tmFiber32DirectConnected :
    chainFiberConnected tmWord tmFiber32DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber32DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber32State0_in_close
  · subst state
    exact tmFiber32State1_in_close
  · subst state
    exact tmFiber32State2_in_close
  · subst state
    exact tmFiber32State3_in_close
  · subst state
    exact tmFiber32State4_in_close
  · subst state
    exact tmFiber32State5_in_close
  · subst state
    exact tmFiber32State6_in_close
  · subst state
    exact tmFiber32State7_in_close
  · subst state
    exact tmFiber32State8_in_close
  · subst state
    exact tmFiber32State9_in_close
  · subst state
    exact tmFiber32State10_in_close
  · subst state
    exact tmFiber32State11_in_close
  · subst state
    exact tmFiber32State12_in_close
  · subst state
    exact tmFiber32State13_in_close
  · subst state
    exact tmFiber32State14_in_close
  · subst state
    exact tmFiber32State15_in_close
  · cases h

def tmFiber37StateAt (i : Nat) : List TauState :=
  directStates (tmFiber37RowAt i).sourceLeft (tmFiber37RowAt i).sourceRight

def tmFiber37DirectStates : List (List TauState) :=
  [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14, tmFiber37StateAt 15]

theorem tmFiber37ReverseRow_1_ok :
    tmRowReverseValid tmFiber37Key tmFiber37Expected (tmFiber37RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber37Chunk0_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber37Chunk0] at h
  exact h.2

theorem tmFiber37ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber37StateAt 0) (tmFiber37StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber37StateAt 0) (tmFiber37StateAt 1)
    (tmFiber37RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber37Key tmFiber37Expected
        (tmFiber37RowAt 1) (by decide) tmFiber37ReverseRow_1_ok
      simpa [tmFiber37StateAt, tmFiber37RowAt, tmFiber37Rows, listGetD, directRow] using h)

theorem tmFiber37ReverseRow_2_ok :
    tmRowReverseValid tmFiber37Key tmFiber37Expected (tmFiber37RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber37Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber37Chunk1] at h
  exact h.1

theorem tmFiber37ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber37StateAt 0) (tmFiber37StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber37StateAt 0) (tmFiber37StateAt 2)
    (tmFiber37RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber37Key tmFiber37Expected
        (tmFiber37RowAt 2) (by decide) tmFiber37ReverseRow_2_ok
      simpa [tmFiber37StateAt, tmFiber37RowAt, tmFiber37Rows, listGetD, directRow] using h)

theorem tmFiber37ReverseRow_3_ok :
    tmRowReverseValid tmFiber37Key tmFiber37Expected (tmFiber37RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber37Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber37Chunk1] at h
  exact h.2

theorem tmFiber37ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber37StateAt 1) (tmFiber37StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber37StateAt 1) (tmFiber37StateAt 3)
    (tmFiber37RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber37Key tmFiber37Expected
        (tmFiber37RowAt 3) (by decide) tmFiber37ReverseRow_3_ok
      simpa [tmFiber37StateAt, tmFiber37RowAt, tmFiber37Rows, listGetD, directRow] using h)

theorem tmFiber37ReverseRow_4_ok :
    tmRowReverseValid tmFiber37Key tmFiber37Expected (tmFiber37RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber37Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber37Chunk2] at h
  exact h.1

theorem tmFiber37ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber37StateAt 0) (tmFiber37StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber37StateAt 0) (tmFiber37StateAt 4)
    (tmFiber37RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber37Key tmFiber37Expected
        (tmFiber37RowAt 4) (by decide) tmFiber37ReverseRow_4_ok
      simpa [tmFiber37StateAt, tmFiber37RowAt, tmFiber37Rows, listGetD, directRow] using h)

theorem tmFiber37ReverseRow_5_ok :
    tmRowReverseValid tmFiber37Key tmFiber37Expected (tmFiber37RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber37Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber37Chunk2] at h
  exact h.2

theorem tmFiber37ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber37StateAt 1) (tmFiber37StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber37StateAt 1) (tmFiber37StateAt 5)
    (tmFiber37RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber37Key tmFiber37Expected
        (tmFiber37RowAt 5) (by decide) tmFiber37ReverseRow_5_ok
      simpa [tmFiber37StateAt, tmFiber37RowAt, tmFiber37Rows, listGetD, directRow] using h)

theorem tmFiber37ReverseRow_6_ok :
    tmRowReverseValid tmFiber37Key tmFiber37Expected (tmFiber37RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber37Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber37Chunk3] at h
  exact h.1

theorem tmFiber37ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber37StateAt 2) (tmFiber37StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber37StateAt 2) (tmFiber37StateAt 6)
    (tmFiber37RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber37Key tmFiber37Expected
        (tmFiber37RowAt 6) (by decide) tmFiber37ReverseRow_6_ok
      simpa [tmFiber37StateAt, tmFiber37RowAt, tmFiber37Rows, listGetD, directRow] using h)

theorem tmFiber37ReverseRow_7_ok :
    tmRowReverseValid tmFiber37Key tmFiber37Expected (tmFiber37RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber37Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber37Chunk3] at h
  exact h.2

theorem tmFiber37ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber37StateAt 3) (tmFiber37StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber37StateAt 3) (tmFiber37StateAt 7)
    (tmFiber37RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber37Key tmFiber37Expected
        (tmFiber37RowAt 7) (by decide) tmFiber37ReverseRow_7_ok
      simpa [tmFiber37StateAt, tmFiber37RowAt, tmFiber37Rows, listGetD, directRow] using h)

theorem tmFiber37ReverseRow_8_ok :
    tmRowReverseValid tmFiber37Key tmFiber37Expected (tmFiber37RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber37Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber37Chunk4] at h
  exact h.1

theorem tmFiber37ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber37StateAt 4) (tmFiber37StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber37StateAt 4) (tmFiber37StateAt 8)
    (tmFiber37RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber37Key tmFiber37Expected
        (tmFiber37RowAt 8) (by decide) tmFiber37ReverseRow_8_ok
      simpa [tmFiber37StateAt, tmFiber37RowAt, tmFiber37Rows, listGetD, directRow] using h)

theorem tmFiber37ReverseRow_9_ok :
    tmRowReverseValid tmFiber37Key tmFiber37Expected (tmFiber37RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber37Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber37Chunk4] at h
  exact h.2

theorem tmFiber37ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber37StateAt 5) (tmFiber37StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber37StateAt 5) (tmFiber37StateAt 9)
    (tmFiber37RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber37Key tmFiber37Expected
        (tmFiber37RowAt 9) (by decide) tmFiber37ReverseRow_9_ok
      simpa [tmFiber37StateAt, tmFiber37RowAt, tmFiber37Rows, listGetD, directRow] using h)

theorem tmFiber37ReverseRow_10_ok :
    tmRowReverseValid tmFiber37Key tmFiber37Expected (tmFiber37RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber37Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber37Chunk5] at h
  exact h.1

theorem tmFiber37ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber37StateAt 6) (tmFiber37StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber37StateAt 6) (tmFiber37StateAt 10)
    (tmFiber37RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber37Key tmFiber37Expected
        (tmFiber37RowAt 10) (by decide) tmFiber37ReverseRow_10_ok
      simpa [tmFiber37StateAt, tmFiber37RowAt, tmFiber37Rows, listGetD, directRow] using h)

theorem tmFiber37ReverseRow_11_ok :
    tmRowReverseValid tmFiber37Key tmFiber37Expected (tmFiber37RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber37Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber37Chunk5] at h
  exact h.2

theorem tmFiber37ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber37StateAt 7) (tmFiber37StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber37StateAt 7) (tmFiber37StateAt 11)
    (tmFiber37RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber37Key tmFiber37Expected
        (tmFiber37RowAt 11) (by decide) tmFiber37ReverseRow_11_ok
      simpa [tmFiber37StateAt, tmFiber37RowAt, tmFiber37Rows, listGetD, directRow] using h)

theorem tmFiber37ReverseRow_12_ok :
    tmRowReverseValid tmFiber37Key tmFiber37Expected (tmFiber37RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber37Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber37Chunk6] at h
  exact h.1

theorem tmFiber37ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber37StateAt 0) (tmFiber37StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber37StateAt 0) (tmFiber37StateAt 12)
    (tmFiber37RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber37Key tmFiber37Expected
        (tmFiber37RowAt 12) (by decide) tmFiber37ReverseRow_12_ok
      simpa [tmFiber37StateAt, tmFiber37RowAt, tmFiber37Rows, listGetD, directRow] using h)

theorem tmFiber37ReverseRow_13_ok :
    tmRowReverseValid tmFiber37Key tmFiber37Expected (tmFiber37RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber37Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber37Chunk6] at h
  exact h.2

theorem tmFiber37ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber37StateAt 1) (tmFiber37StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber37StateAt 1) (tmFiber37StateAt 13)
    (tmFiber37RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber37Key tmFiber37Expected
        (tmFiber37RowAt 13) (by decide) tmFiber37ReverseRow_13_ok
      simpa [tmFiber37StateAt, tmFiber37RowAt, tmFiber37Rows, listGetD, directRow] using h)

theorem tmFiber37ReverseRow_14_ok :
    tmRowReverseValid tmFiber37Key tmFiber37Expected (tmFiber37RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber37Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber37Chunk7] at h
  exact h.1

theorem tmFiber37ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber37StateAt 2) (tmFiber37StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber37StateAt 2) (tmFiber37StateAt 14)
    (tmFiber37RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber37Key tmFiber37Expected
        (tmFiber37RowAt 14) (by decide) tmFiber37ReverseRow_14_ok
      simpa [tmFiber37StateAt, tmFiber37RowAt, tmFiber37Rows, listGetD, directRow] using h)

theorem tmFiber37ReverseRow_15_ok :
    tmRowReverseValid tmFiber37Key tmFiber37Expected (tmFiber37RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber37Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber37Chunk7] at h
  exact h.2

theorem tmFiber37ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber37StateAt 3) (tmFiber37StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber37StateAt 3) (tmFiber37StateAt 15)
    (tmFiber37RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber37Key tmFiber37Expected
        (tmFiber37RowAt 15) (by decide) tmFiber37ReverseRow_15_ok
      simpa [tmFiber37StateAt, tmFiber37RowAt, tmFiber37Rows, listGetD, directRow] using h)

theorem tmFiber37State0_in_pass1_prefix :
    tmFiber37StateAt 0 ∈ chainClosureStep tmWord [tmFiber37StateAt 0] [tmFiber37StateAt 0] := by
  exact chainClosureStep_mem_of_seen tmWord [tmFiber37StateAt 0] [tmFiber37StateAt 0] (tmFiber37StateAt 0) (by simp)

theorem tmFiber37State1_in_pass1_prefix :
    tmFiber37StateAt 1 ∈ chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1] [tmFiber37StateAt 0] := by
  have hparentBefore :
      tmFiber37StateAt 0 ∈ chainClosureStep tmWord [tmFiber37StateAt 0] [tmFiber37StateAt 0] := by
    exact tmFiber37State0_in_pass1_prefix
  rw [show [tmFiber37StateAt 0, tmFiber37StateAt 1] = [tmFiber37StateAt 0] ++ [tmFiber37StateAt 1] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber37StateAt 1) []
    (chainClosureStep tmWord [tmFiber37StateAt 0] [tmFiber37StateAt 0]) (tmFiber37StateAt 0)
    hparentBefore tmFiber37ReverseSingleStep1

theorem tmFiber37State2_in_pass1_prefix :
    tmFiber37StateAt 2 ∈ chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2] [tmFiber37StateAt 0] := by
  have hparentBefore :
      tmFiber37StateAt 0 ∈ chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1] [tmFiber37StateAt 0] := by
    rw [show [tmFiber37StateAt 0, tmFiber37StateAt 1] = [tmFiber37StateAt 0] ++ [tmFiber37StateAt 1] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber37StateAt 1]
      (chainClosureStep tmWord [tmFiber37StateAt 0] [tmFiber37StateAt 0]) (tmFiber37StateAt 0)
      tmFiber37State0_in_pass1_prefix
  rw [show [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2] = [tmFiber37StateAt 0, tmFiber37StateAt 1] ++ [tmFiber37StateAt 2] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber37StateAt 2) []
    (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1] [tmFiber37StateAt 0]) (tmFiber37StateAt 0)
    hparentBefore tmFiber37ReverseSingleStep2

theorem tmFiber37State3_in_pass1_prefix :
    tmFiber37StateAt 3 ∈ chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3] [tmFiber37StateAt 0] := by
  have hparentBefore :
      tmFiber37StateAt 1 ∈ chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2] [tmFiber37StateAt 0] := by
    rw [show [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2] = [tmFiber37StateAt 0, tmFiber37StateAt 1] ++ [tmFiber37StateAt 2] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber37StateAt 2]
      (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1] [tmFiber37StateAt 0]) (tmFiber37StateAt 1)
      tmFiber37State1_in_pass1_prefix
  rw [show [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3] = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2] ++ [tmFiber37StateAt 3] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber37StateAt 3) []
    (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2] [tmFiber37StateAt 0]) (tmFiber37StateAt 1)
    hparentBefore tmFiber37ReverseSingleStep3

theorem tmFiber37State4_in_pass1_prefix :
    tmFiber37StateAt 4 ∈ chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4] [tmFiber37StateAt 0] := by
  have hparentBefore :
      tmFiber37StateAt 0 ∈ chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3] [tmFiber37StateAt 0] := by
    rw [show [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3] = [tmFiber37StateAt 0] ++ [tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3]
      (chainClosureStep tmWord [tmFiber37StateAt 0] [tmFiber37StateAt 0]) (tmFiber37StateAt 0)
      tmFiber37State0_in_pass1_prefix
  rw [show [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4] = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3] ++ [tmFiber37StateAt 4] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber37StateAt 4) []
    (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3] [tmFiber37StateAt 0]) (tmFiber37StateAt 0)
    hparentBefore tmFiber37ReverseSingleStep4

theorem tmFiber37State5_in_pass1_prefix :
    tmFiber37StateAt 5 ∈ chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5] [tmFiber37StateAt 0] := by
  have hparentBefore :
      tmFiber37StateAt 1 ∈ chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4] [tmFiber37StateAt 0] := by
    rw [show [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4] = [tmFiber37StateAt 0, tmFiber37StateAt 1] ++ [tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4]
      (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1] [tmFiber37StateAt 0]) (tmFiber37StateAt 1)
      tmFiber37State1_in_pass1_prefix
  rw [show [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5] = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4] ++ [tmFiber37StateAt 5] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber37StateAt 5) []
    (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4] [tmFiber37StateAt 0]) (tmFiber37StateAt 1)
    hparentBefore tmFiber37ReverseSingleStep5

theorem tmFiber37State6_in_pass1_prefix :
    tmFiber37StateAt 6 ∈ chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6] [tmFiber37StateAt 0] := by
  have hparentBefore :
      tmFiber37StateAt 2 ∈ chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5] [tmFiber37StateAt 0] := by
    rw [show [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5] = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2] ++ [tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5]
      (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2] [tmFiber37StateAt 0]) (tmFiber37StateAt 2)
      tmFiber37State2_in_pass1_prefix
  rw [show [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6] = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5] ++ [tmFiber37StateAt 6] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber37StateAt 6) []
    (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5] [tmFiber37StateAt 0]) (tmFiber37StateAt 2)
    hparentBefore tmFiber37ReverseSingleStep6

theorem tmFiber37State7_in_pass1_prefix :
    tmFiber37StateAt 7 ∈ chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7] [tmFiber37StateAt 0] := by
  have hparentBefore :
      tmFiber37StateAt 3 ∈ chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6] [tmFiber37StateAt 0] := by
    rw [show [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6] = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3] ++ [tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6]
      (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3] [tmFiber37StateAt 0]) (tmFiber37StateAt 3)
      tmFiber37State3_in_pass1_prefix
  rw [show [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7] = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6] ++ [tmFiber37StateAt 7] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber37StateAt 7) []
    (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6] [tmFiber37StateAt 0]) (tmFiber37StateAt 3)
    hparentBefore tmFiber37ReverseSingleStep7

theorem tmFiber37State8_in_pass1_prefix :
    tmFiber37StateAt 8 ∈ chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8] [tmFiber37StateAt 0] := by
  have hparentBefore :
      tmFiber37StateAt 4 ∈ chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7] [tmFiber37StateAt 0] := by
    rw [show [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7] = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4] ++ [tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7]
      (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4] [tmFiber37StateAt 0]) (tmFiber37StateAt 4)
      tmFiber37State4_in_pass1_prefix
  rw [show [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8] = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7] ++ [tmFiber37StateAt 8] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber37StateAt 8) []
    (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7] [tmFiber37StateAt 0]) (tmFiber37StateAt 4)
    hparentBefore tmFiber37ReverseSingleStep8

theorem tmFiber37State9_in_pass1_prefix :
    tmFiber37StateAt 9 ∈ chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9] [tmFiber37StateAt 0] := by
  have hparentBefore :
      tmFiber37StateAt 5 ∈ chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8] [tmFiber37StateAt 0] := by
    rw [show [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8] = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5] ++ [tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8]
      (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5] [tmFiber37StateAt 0]) (tmFiber37StateAt 5)
      tmFiber37State5_in_pass1_prefix
  rw [show [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9] = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8] ++ [tmFiber37StateAt 9] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber37StateAt 9) []
    (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8] [tmFiber37StateAt 0]) (tmFiber37StateAt 5)
    hparentBefore tmFiber37ReverseSingleStep9

theorem tmFiber37State10_in_pass1_prefix :
    tmFiber37StateAt 10 ∈ chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10] [tmFiber37StateAt 0] := by
  have hparentBefore :
      tmFiber37StateAt 6 ∈ chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9] [tmFiber37StateAt 0] := by
    rw [show [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9] = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6] ++ [tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9]
      (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6] [tmFiber37StateAt 0]) (tmFiber37StateAt 6)
      tmFiber37State6_in_pass1_prefix
  rw [show [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10] = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9] ++ [tmFiber37StateAt 10] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber37StateAt 10) []
    (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9] [tmFiber37StateAt 0]) (tmFiber37StateAt 6)
    hparentBefore tmFiber37ReverseSingleStep10

theorem tmFiber37State11_in_pass1_prefix :
    tmFiber37StateAt 11 ∈ chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11] [tmFiber37StateAt 0] := by
  have hparentBefore :
      tmFiber37StateAt 7 ∈ chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10] [tmFiber37StateAt 0] := by
    rw [show [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10] = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7] ++ [tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10]
      (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7] [tmFiber37StateAt 0]) (tmFiber37StateAt 7)
      tmFiber37State7_in_pass1_prefix
  rw [show [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11] = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10] ++ [tmFiber37StateAt 11] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber37StateAt 11) []
    (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10] [tmFiber37StateAt 0]) (tmFiber37StateAt 7)
    hparentBefore tmFiber37ReverseSingleStep11

theorem tmFiber37State12_in_pass1_prefix :
    tmFiber37StateAt 12 ∈ chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12] [tmFiber37StateAt 0] := by
  have hparentBefore :
      tmFiber37StateAt 0 ∈ chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11] [tmFiber37StateAt 0] := by
    rw [show [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11] = [tmFiber37StateAt 0] ++ [tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11]
      (chainClosureStep tmWord [tmFiber37StateAt 0] [tmFiber37StateAt 0]) (tmFiber37StateAt 0)
      tmFiber37State0_in_pass1_prefix
  rw [show [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12] = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11] ++ [tmFiber37StateAt 12] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber37StateAt 12) []
    (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11] [tmFiber37StateAt 0]) (tmFiber37StateAt 0)
    hparentBefore tmFiber37ReverseSingleStep12

theorem tmFiber37State13_in_pass1_prefix :
    tmFiber37StateAt 13 ∈ chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13] [tmFiber37StateAt 0] := by
  have hparentBefore :
      tmFiber37StateAt 1 ∈ chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12] [tmFiber37StateAt 0] := by
    rw [show [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12] = [tmFiber37StateAt 0, tmFiber37StateAt 1] ++ [tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12]
      (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1] [tmFiber37StateAt 0]) (tmFiber37StateAt 1)
      tmFiber37State1_in_pass1_prefix
  rw [show [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13] = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12] ++ [tmFiber37StateAt 13] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber37StateAt 13) []
    (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12] [tmFiber37StateAt 0]) (tmFiber37StateAt 1)
    hparentBefore tmFiber37ReverseSingleStep13

theorem tmFiber37State14_in_pass1_prefix :
    tmFiber37StateAt 14 ∈ chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14] [tmFiber37StateAt 0] := by
  have hparentBefore :
      tmFiber37StateAt 2 ∈ chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13] [tmFiber37StateAt 0] := by
    rw [show [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13] = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2] ++ [tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13]
      (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2] [tmFiber37StateAt 0]) (tmFiber37StateAt 2)
      tmFiber37State2_in_pass1_prefix
  rw [show [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14] = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13] ++ [tmFiber37StateAt 14] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber37StateAt 14) []
    (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13] [tmFiber37StateAt 0]) (tmFiber37StateAt 2)
    hparentBefore tmFiber37ReverseSingleStep14

theorem tmFiber37State15_in_pass1_prefix :
    tmFiber37StateAt 15 ∈ chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14, tmFiber37StateAt 15] [tmFiber37StateAt 0] := by
  have hparentBefore :
      tmFiber37StateAt 3 ∈ chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14] [tmFiber37StateAt 0] := by
    rw [show [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14] = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3] ++ [tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14]
      (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3] [tmFiber37StateAt 0]) (tmFiber37StateAt 3)
      tmFiber37State3_in_pass1_prefix
  rw [show [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14, tmFiber37StateAt 15] = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14] ++ [tmFiber37StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber37StateAt 15) []
    (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14] [tmFiber37StateAt 0]) (tmFiber37StateAt 3)
    hparentBefore tmFiber37ReverseSingleStep15

theorem tmFiber37State0_in_pass1_full :
    tmFiber37StateAt 0 ∈ chainClosureStep tmWord tmFiber37DirectStates [tmFiber37StateAt 0] := by
  rw [show tmFiber37DirectStates = [tmFiber37StateAt 0] ++ [tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14, tmFiber37StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14, tmFiber37StateAt 15]
    (chainClosureStep tmWord [tmFiber37StateAt 0] [tmFiber37StateAt 0]) (tmFiber37StateAt 0)
    tmFiber37State0_in_pass1_prefix

theorem tmFiber37State1_in_pass1_full :
    tmFiber37StateAt 1 ∈ chainClosureStep tmWord tmFiber37DirectStates [tmFiber37StateAt 0] := by
  rw [show tmFiber37DirectStates = [tmFiber37StateAt 0, tmFiber37StateAt 1] ++ [tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14, tmFiber37StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14, tmFiber37StateAt 15]
    (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1] [tmFiber37StateAt 0]) (tmFiber37StateAt 1)
    tmFiber37State1_in_pass1_prefix

theorem tmFiber37State2_in_pass1_full :
    tmFiber37StateAt 2 ∈ chainClosureStep tmWord tmFiber37DirectStates [tmFiber37StateAt 0] := by
  rw [show tmFiber37DirectStates = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2] ++ [tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14, tmFiber37StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14, tmFiber37StateAt 15]
    (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2] [tmFiber37StateAt 0]) (tmFiber37StateAt 2)
    tmFiber37State2_in_pass1_prefix

theorem tmFiber37State3_in_pass1_full :
    tmFiber37StateAt 3 ∈ chainClosureStep tmWord tmFiber37DirectStates [tmFiber37StateAt 0] := by
  rw [show tmFiber37DirectStates = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3] ++ [tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14, tmFiber37StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14, tmFiber37StateAt 15]
    (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3] [tmFiber37StateAt 0]) (tmFiber37StateAt 3)
    tmFiber37State3_in_pass1_prefix

theorem tmFiber37State4_in_pass1_full :
    tmFiber37StateAt 4 ∈ chainClosureStep tmWord tmFiber37DirectStates [tmFiber37StateAt 0] := by
  rw [show tmFiber37DirectStates = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4] ++ [tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14, tmFiber37StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14, tmFiber37StateAt 15]
    (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4] [tmFiber37StateAt 0]) (tmFiber37StateAt 4)
    tmFiber37State4_in_pass1_prefix

theorem tmFiber37State5_in_pass1_full :
    tmFiber37StateAt 5 ∈ chainClosureStep tmWord tmFiber37DirectStates [tmFiber37StateAt 0] := by
  rw [show tmFiber37DirectStates = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5] ++ [tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14, tmFiber37StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14, tmFiber37StateAt 15]
    (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5] [tmFiber37StateAt 0]) (tmFiber37StateAt 5)
    tmFiber37State5_in_pass1_prefix

theorem tmFiber37State6_in_pass1_full :
    tmFiber37StateAt 6 ∈ chainClosureStep tmWord tmFiber37DirectStates [tmFiber37StateAt 0] := by
  rw [show tmFiber37DirectStates = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6] ++ [tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14, tmFiber37StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14, tmFiber37StateAt 15]
    (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6] [tmFiber37StateAt 0]) (tmFiber37StateAt 6)
    tmFiber37State6_in_pass1_prefix

theorem tmFiber37State7_in_pass1_full :
    tmFiber37StateAt 7 ∈ chainClosureStep tmWord tmFiber37DirectStates [tmFiber37StateAt 0] := by
  rw [show tmFiber37DirectStates = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7] ++ [tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14, tmFiber37StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14, tmFiber37StateAt 15]
    (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7] [tmFiber37StateAt 0]) (tmFiber37StateAt 7)
    tmFiber37State7_in_pass1_prefix

theorem tmFiber37State8_in_pass1_full :
    tmFiber37StateAt 8 ∈ chainClosureStep tmWord tmFiber37DirectStates [tmFiber37StateAt 0] := by
  rw [show tmFiber37DirectStates = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8] ++ [tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14, tmFiber37StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14, tmFiber37StateAt 15]
    (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8] [tmFiber37StateAt 0]) (tmFiber37StateAt 8)
    tmFiber37State8_in_pass1_prefix

theorem tmFiber37State9_in_pass1_full :
    tmFiber37StateAt 9 ∈ chainClosureStep tmWord tmFiber37DirectStates [tmFiber37StateAt 0] := by
  rw [show tmFiber37DirectStates = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9] ++ [tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14, tmFiber37StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14, tmFiber37StateAt 15]
    (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9] [tmFiber37StateAt 0]) (tmFiber37StateAt 9)
    tmFiber37State9_in_pass1_prefix

theorem tmFiber37State10_in_pass1_full :
    tmFiber37StateAt 10 ∈ chainClosureStep tmWord tmFiber37DirectStates [tmFiber37StateAt 0] := by
  rw [show tmFiber37DirectStates = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10] ++ [tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14, tmFiber37StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14, tmFiber37StateAt 15]
    (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10] [tmFiber37StateAt 0]) (tmFiber37StateAt 10)
    tmFiber37State10_in_pass1_prefix

theorem tmFiber37State11_in_pass1_full :
    tmFiber37StateAt 11 ∈ chainClosureStep tmWord tmFiber37DirectStates [tmFiber37StateAt 0] := by
  rw [show tmFiber37DirectStates = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11] ++ [tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14, tmFiber37StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14, tmFiber37StateAt 15]
    (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11] [tmFiber37StateAt 0]) (tmFiber37StateAt 11)
    tmFiber37State11_in_pass1_prefix

theorem tmFiber37State12_in_pass1_full :
    tmFiber37StateAt 12 ∈ chainClosureStep tmWord tmFiber37DirectStates [tmFiber37StateAt 0] := by
  rw [show tmFiber37DirectStates = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12] ++ [tmFiber37StateAt 13, tmFiber37StateAt 14, tmFiber37StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber37StateAt 13, tmFiber37StateAt 14, tmFiber37StateAt 15]
    (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12] [tmFiber37StateAt 0]) (tmFiber37StateAt 12)
    tmFiber37State12_in_pass1_prefix

theorem tmFiber37State13_in_pass1_full :
    tmFiber37StateAt 13 ∈ chainClosureStep tmWord tmFiber37DirectStates [tmFiber37StateAt 0] := by
  rw [show tmFiber37DirectStates = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13] ++ [tmFiber37StateAt 14, tmFiber37StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber37StateAt 14, tmFiber37StateAt 15]
    (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13] [tmFiber37StateAt 0]) (tmFiber37StateAt 13)
    tmFiber37State13_in_pass1_prefix

theorem tmFiber37State14_in_pass1_full :
    tmFiber37StateAt 14 ∈ chainClosureStep tmWord tmFiber37DirectStates [tmFiber37StateAt 0] := by
  rw [show tmFiber37DirectStates = [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14] ++ [tmFiber37StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber37StateAt 15]
    (chainClosureStep tmWord [tmFiber37StateAt 0, tmFiber37StateAt 1, tmFiber37StateAt 2, tmFiber37StateAt 3, tmFiber37StateAt 4, tmFiber37StateAt 5, tmFiber37StateAt 6, tmFiber37StateAt 7, tmFiber37StateAt 8, tmFiber37StateAt 9, tmFiber37StateAt 10, tmFiber37StateAt 11, tmFiber37StateAt 12, tmFiber37StateAt 13, tmFiber37StateAt 14] [tmFiber37StateAt 0]) (tmFiber37StateAt 14)
    tmFiber37State14_in_pass1_prefix

theorem tmFiber37State15_in_pass1_full :
    tmFiber37StateAt 15 ∈ chainClosureStep tmWord tmFiber37DirectStates [tmFiber37StateAt 0] := by
  simpa [tmFiber37DirectStates] using tmFiber37State15_in_pass1_prefix

theorem tmFiber37State0_in_close :
    tmFiber37StateAt 0 ∈ closeChainFiber tmWord tmFiber37DirectStates tmFiber37DirectStates.length [tmFiber37StateAt 0] := by
  change tmFiber37StateAt 0 ∈ closeChainFiber tmWord tmFiber37DirectStates (15 + 1) [tmFiber37StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber37DirectStates 15 [tmFiber37StateAt 0] (tmFiber37StateAt 0) tmFiber37State0_in_pass1_full

theorem tmFiber37State1_in_close :
    tmFiber37StateAt 1 ∈ closeChainFiber tmWord tmFiber37DirectStates tmFiber37DirectStates.length [tmFiber37StateAt 0] := by
  change tmFiber37StateAt 1 ∈ closeChainFiber tmWord tmFiber37DirectStates (15 + 1) [tmFiber37StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber37DirectStates 15 [tmFiber37StateAt 0] (tmFiber37StateAt 1) tmFiber37State1_in_pass1_full

theorem tmFiber37State2_in_close :
    tmFiber37StateAt 2 ∈ closeChainFiber tmWord tmFiber37DirectStates tmFiber37DirectStates.length [tmFiber37StateAt 0] := by
  change tmFiber37StateAt 2 ∈ closeChainFiber tmWord tmFiber37DirectStates (15 + 1) [tmFiber37StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber37DirectStates 15 [tmFiber37StateAt 0] (tmFiber37StateAt 2) tmFiber37State2_in_pass1_full

theorem tmFiber37State3_in_close :
    tmFiber37StateAt 3 ∈ closeChainFiber tmWord tmFiber37DirectStates tmFiber37DirectStates.length [tmFiber37StateAt 0] := by
  change tmFiber37StateAt 3 ∈ closeChainFiber tmWord tmFiber37DirectStates (15 + 1) [tmFiber37StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber37DirectStates 15 [tmFiber37StateAt 0] (tmFiber37StateAt 3) tmFiber37State3_in_pass1_full

theorem tmFiber37State4_in_close :
    tmFiber37StateAt 4 ∈ closeChainFiber tmWord tmFiber37DirectStates tmFiber37DirectStates.length [tmFiber37StateAt 0] := by
  change tmFiber37StateAt 4 ∈ closeChainFiber tmWord tmFiber37DirectStates (15 + 1) [tmFiber37StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber37DirectStates 15 [tmFiber37StateAt 0] (tmFiber37StateAt 4) tmFiber37State4_in_pass1_full

theorem tmFiber37State5_in_close :
    tmFiber37StateAt 5 ∈ closeChainFiber tmWord tmFiber37DirectStates tmFiber37DirectStates.length [tmFiber37StateAt 0] := by
  change tmFiber37StateAt 5 ∈ closeChainFiber tmWord tmFiber37DirectStates (15 + 1) [tmFiber37StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber37DirectStates 15 [tmFiber37StateAt 0] (tmFiber37StateAt 5) tmFiber37State5_in_pass1_full

theorem tmFiber37State6_in_close :
    tmFiber37StateAt 6 ∈ closeChainFiber tmWord tmFiber37DirectStates tmFiber37DirectStates.length [tmFiber37StateAt 0] := by
  change tmFiber37StateAt 6 ∈ closeChainFiber tmWord tmFiber37DirectStates (15 + 1) [tmFiber37StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber37DirectStates 15 [tmFiber37StateAt 0] (tmFiber37StateAt 6) tmFiber37State6_in_pass1_full

theorem tmFiber37State7_in_close :
    tmFiber37StateAt 7 ∈ closeChainFiber tmWord tmFiber37DirectStates tmFiber37DirectStates.length [tmFiber37StateAt 0] := by
  change tmFiber37StateAt 7 ∈ closeChainFiber tmWord tmFiber37DirectStates (15 + 1) [tmFiber37StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber37DirectStates 15 [tmFiber37StateAt 0] (tmFiber37StateAt 7) tmFiber37State7_in_pass1_full

theorem tmFiber37State8_in_close :
    tmFiber37StateAt 8 ∈ closeChainFiber tmWord tmFiber37DirectStates tmFiber37DirectStates.length [tmFiber37StateAt 0] := by
  change tmFiber37StateAt 8 ∈ closeChainFiber tmWord tmFiber37DirectStates (15 + 1) [tmFiber37StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber37DirectStates 15 [tmFiber37StateAt 0] (tmFiber37StateAt 8) tmFiber37State8_in_pass1_full

theorem tmFiber37State9_in_close :
    tmFiber37StateAt 9 ∈ closeChainFiber tmWord tmFiber37DirectStates tmFiber37DirectStates.length [tmFiber37StateAt 0] := by
  change tmFiber37StateAt 9 ∈ closeChainFiber tmWord tmFiber37DirectStates (15 + 1) [tmFiber37StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber37DirectStates 15 [tmFiber37StateAt 0] (tmFiber37StateAt 9) tmFiber37State9_in_pass1_full

theorem tmFiber37State10_in_close :
    tmFiber37StateAt 10 ∈ closeChainFiber tmWord tmFiber37DirectStates tmFiber37DirectStates.length [tmFiber37StateAt 0] := by
  change tmFiber37StateAt 10 ∈ closeChainFiber tmWord tmFiber37DirectStates (15 + 1) [tmFiber37StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber37DirectStates 15 [tmFiber37StateAt 0] (tmFiber37StateAt 10) tmFiber37State10_in_pass1_full

theorem tmFiber37State11_in_close :
    tmFiber37StateAt 11 ∈ closeChainFiber tmWord tmFiber37DirectStates tmFiber37DirectStates.length [tmFiber37StateAt 0] := by
  change tmFiber37StateAt 11 ∈ closeChainFiber tmWord tmFiber37DirectStates (15 + 1) [tmFiber37StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber37DirectStates 15 [tmFiber37StateAt 0] (tmFiber37StateAt 11) tmFiber37State11_in_pass1_full

theorem tmFiber37State12_in_close :
    tmFiber37StateAt 12 ∈ closeChainFiber tmWord tmFiber37DirectStates tmFiber37DirectStates.length [tmFiber37StateAt 0] := by
  change tmFiber37StateAt 12 ∈ closeChainFiber tmWord tmFiber37DirectStates (15 + 1) [tmFiber37StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber37DirectStates 15 [tmFiber37StateAt 0] (tmFiber37StateAt 12) tmFiber37State12_in_pass1_full

theorem tmFiber37State13_in_close :
    tmFiber37StateAt 13 ∈ closeChainFiber tmWord tmFiber37DirectStates tmFiber37DirectStates.length [tmFiber37StateAt 0] := by
  change tmFiber37StateAt 13 ∈ closeChainFiber tmWord tmFiber37DirectStates (15 + 1) [tmFiber37StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber37DirectStates 15 [tmFiber37StateAt 0] (tmFiber37StateAt 13) tmFiber37State13_in_pass1_full

theorem tmFiber37State14_in_close :
    tmFiber37StateAt 14 ∈ closeChainFiber tmWord tmFiber37DirectStates tmFiber37DirectStates.length [tmFiber37StateAt 0] := by
  change tmFiber37StateAt 14 ∈ closeChainFiber tmWord tmFiber37DirectStates (15 + 1) [tmFiber37StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber37DirectStates 15 [tmFiber37StateAt 0] (tmFiber37StateAt 14) tmFiber37State14_in_pass1_full

theorem tmFiber37State15_in_close :
    tmFiber37StateAt 15 ∈ closeChainFiber tmWord tmFiber37DirectStates tmFiber37DirectStates.length [tmFiber37StateAt 0] := by
  change tmFiber37StateAt 15 ∈ closeChainFiber tmWord tmFiber37DirectStates (15 + 1) [tmFiber37StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber37DirectStates 15 [tmFiber37StateAt 0] (tmFiber37StateAt 15) tmFiber37State15_in_pass1_full

theorem tmFiber37DirectConnected :
    chainFiberConnected tmWord tmFiber37DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber37DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber37State0_in_close
  · subst state
    exact tmFiber37State1_in_close
  · subst state
    exact tmFiber37State2_in_close
  · subst state
    exact tmFiber37State3_in_close
  · subst state
    exact tmFiber37State4_in_close
  · subst state
    exact tmFiber37State5_in_close
  · subst state
    exact tmFiber37State6_in_close
  · subst state
    exact tmFiber37State7_in_close
  · subst state
    exact tmFiber37State8_in_close
  · subst state
    exact tmFiber37State9_in_close
  · subst state
    exact tmFiber37State10_in_close
  · subst state
    exact tmFiber37State11_in_close
  · subst state
    exact tmFiber37State12_in_close
  · subst state
    exact tmFiber37State13_in_close
  · subst state
    exact tmFiber37State14_in_close
  · subst state
    exact tmFiber37State15_in_close
  · cases h

def tmFiber38StateAt (i : Nat) : List TauState :=
  directStates (tmFiber38RowAt i).sourceLeft (tmFiber38RowAt i).sourceRight

def tmFiber38DirectStates : List (List TauState) :=
  [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14, tmFiber38StateAt 15]

theorem tmFiber38ReverseRow_1_ok :
    tmRowReverseValid tmFiber38Key tmFiber38Expected (tmFiber38RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber38Chunk0_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber38Chunk0] at h
  exact h.2

theorem tmFiber38ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber38StateAt 0) (tmFiber38StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber38StateAt 0) (tmFiber38StateAt 1)
    (tmFiber38RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber38Key tmFiber38Expected
        (tmFiber38RowAt 1) (by decide) tmFiber38ReverseRow_1_ok
      simpa [tmFiber38StateAt, tmFiber38RowAt, tmFiber38Rows, listGetD, directRow] using h)

theorem tmFiber38ReverseRow_2_ok :
    tmRowReverseValid tmFiber38Key tmFiber38Expected (tmFiber38RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber38Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber38Chunk1] at h
  exact h.1

theorem tmFiber38ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber38StateAt 0) (tmFiber38StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber38StateAt 0) (tmFiber38StateAt 2)
    (tmFiber38RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber38Key tmFiber38Expected
        (tmFiber38RowAt 2) (by decide) tmFiber38ReverseRow_2_ok
      simpa [tmFiber38StateAt, tmFiber38RowAt, tmFiber38Rows, listGetD, directRow] using h)

theorem tmFiber38ReverseRow_3_ok :
    tmRowReverseValid tmFiber38Key tmFiber38Expected (tmFiber38RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber38Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber38Chunk1] at h
  exact h.2

theorem tmFiber38ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber38StateAt 1) (tmFiber38StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber38StateAt 1) (tmFiber38StateAt 3)
    (tmFiber38RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber38Key tmFiber38Expected
        (tmFiber38RowAt 3) (by decide) tmFiber38ReverseRow_3_ok
      simpa [tmFiber38StateAt, tmFiber38RowAt, tmFiber38Rows, listGetD, directRow] using h)

theorem tmFiber38ReverseRow_4_ok :
    tmRowReverseValid tmFiber38Key tmFiber38Expected (tmFiber38RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber38Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber38Chunk2] at h
  exact h.1

theorem tmFiber38ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber38StateAt 0) (tmFiber38StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber38StateAt 0) (tmFiber38StateAt 4)
    (tmFiber38RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber38Key tmFiber38Expected
        (tmFiber38RowAt 4) (by decide) tmFiber38ReverseRow_4_ok
      simpa [tmFiber38StateAt, tmFiber38RowAt, tmFiber38Rows, listGetD, directRow] using h)

theorem tmFiber38ReverseRow_5_ok :
    tmRowReverseValid tmFiber38Key tmFiber38Expected (tmFiber38RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber38Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber38Chunk2] at h
  exact h.2

theorem tmFiber38ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber38StateAt 1) (tmFiber38StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber38StateAt 1) (tmFiber38StateAt 5)
    (tmFiber38RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber38Key tmFiber38Expected
        (tmFiber38RowAt 5) (by decide) tmFiber38ReverseRow_5_ok
      simpa [tmFiber38StateAt, tmFiber38RowAt, tmFiber38Rows, listGetD, directRow] using h)

theorem tmFiber38ReverseRow_6_ok :
    tmRowReverseValid tmFiber38Key tmFiber38Expected (tmFiber38RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber38Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber38Chunk3] at h
  exact h.1

theorem tmFiber38ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber38StateAt 2) (tmFiber38StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber38StateAt 2) (tmFiber38StateAt 6)
    (tmFiber38RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber38Key tmFiber38Expected
        (tmFiber38RowAt 6) (by decide) tmFiber38ReverseRow_6_ok
      simpa [tmFiber38StateAt, tmFiber38RowAt, tmFiber38Rows, listGetD, directRow] using h)

theorem tmFiber38ReverseRow_7_ok :
    tmRowReverseValid tmFiber38Key tmFiber38Expected (tmFiber38RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber38Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber38Chunk3] at h
  exact h.2

theorem tmFiber38ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber38StateAt 3) (tmFiber38StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber38StateAt 3) (tmFiber38StateAt 7)
    (tmFiber38RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber38Key tmFiber38Expected
        (tmFiber38RowAt 7) (by decide) tmFiber38ReverseRow_7_ok
      simpa [tmFiber38StateAt, tmFiber38RowAt, tmFiber38Rows, listGetD, directRow] using h)

theorem tmFiber38ReverseRow_8_ok :
    tmRowReverseValid tmFiber38Key tmFiber38Expected (tmFiber38RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber38Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber38Chunk4] at h
  exact h.1

theorem tmFiber38ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber38StateAt 0) (tmFiber38StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber38StateAt 0) (tmFiber38StateAt 8)
    (tmFiber38RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber38Key tmFiber38Expected
        (tmFiber38RowAt 8) (by decide) tmFiber38ReverseRow_8_ok
      simpa [tmFiber38StateAt, tmFiber38RowAt, tmFiber38Rows, listGetD, directRow] using h)

theorem tmFiber38ReverseRow_9_ok :
    tmRowReverseValid tmFiber38Key tmFiber38Expected (tmFiber38RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber38Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber38Chunk4] at h
  exact h.2

theorem tmFiber38ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber38StateAt 1) (tmFiber38StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber38StateAt 1) (tmFiber38StateAt 9)
    (tmFiber38RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber38Key tmFiber38Expected
        (tmFiber38RowAt 9) (by decide) tmFiber38ReverseRow_9_ok
      simpa [tmFiber38StateAt, tmFiber38RowAt, tmFiber38Rows, listGetD, directRow] using h)

theorem tmFiber38ReverseRow_10_ok :
    tmRowReverseValid tmFiber38Key tmFiber38Expected (tmFiber38RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber38Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber38Chunk5] at h
  exact h.1

theorem tmFiber38ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber38StateAt 2) (tmFiber38StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber38StateAt 2) (tmFiber38StateAt 10)
    (tmFiber38RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber38Key tmFiber38Expected
        (tmFiber38RowAt 10) (by decide) tmFiber38ReverseRow_10_ok
      simpa [tmFiber38StateAt, tmFiber38RowAt, tmFiber38Rows, listGetD, directRow] using h)

theorem tmFiber38ReverseRow_11_ok :
    tmRowReverseValid tmFiber38Key tmFiber38Expected (tmFiber38RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber38Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber38Chunk5] at h
  exact h.2

theorem tmFiber38ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber38StateAt 3) (tmFiber38StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber38StateAt 3) (tmFiber38StateAt 11)
    (tmFiber38RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber38Key tmFiber38Expected
        (tmFiber38RowAt 11) (by decide) tmFiber38ReverseRow_11_ok
      simpa [tmFiber38StateAt, tmFiber38RowAt, tmFiber38Rows, listGetD, directRow] using h)

theorem tmFiber38ReverseRow_12_ok :
    tmRowReverseValid tmFiber38Key tmFiber38Expected (tmFiber38RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber38Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber38Chunk6] at h
  exact h.1

theorem tmFiber38ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber38StateAt 4) (tmFiber38StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber38StateAt 4) (tmFiber38StateAt 12)
    (tmFiber38RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber38Key tmFiber38Expected
        (tmFiber38RowAt 12) (by decide) tmFiber38ReverseRow_12_ok
      simpa [tmFiber38StateAt, tmFiber38RowAt, tmFiber38Rows, listGetD, directRow] using h)

theorem tmFiber38ReverseRow_13_ok :
    tmRowReverseValid tmFiber38Key tmFiber38Expected (tmFiber38RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber38Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber38Chunk6] at h
  exact h.2

theorem tmFiber38ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber38StateAt 5) (tmFiber38StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber38StateAt 5) (tmFiber38StateAt 13)
    (tmFiber38RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber38Key tmFiber38Expected
        (tmFiber38RowAt 13) (by decide) tmFiber38ReverseRow_13_ok
      simpa [tmFiber38StateAt, tmFiber38RowAt, tmFiber38Rows, listGetD, directRow] using h)

theorem tmFiber38ReverseRow_14_ok :
    tmRowReverseValid tmFiber38Key tmFiber38Expected (tmFiber38RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber38Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber38Chunk7] at h
  exact h.1

theorem tmFiber38ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber38StateAt 6) (tmFiber38StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber38StateAt 6) (tmFiber38StateAt 14)
    (tmFiber38RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber38Key tmFiber38Expected
        (tmFiber38RowAt 14) (by decide) tmFiber38ReverseRow_14_ok
      simpa [tmFiber38StateAt, tmFiber38RowAt, tmFiber38Rows, listGetD, directRow] using h)

theorem tmFiber38ReverseRow_15_ok :
    tmRowReverseValid tmFiber38Key tmFiber38Expected (tmFiber38RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber38Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber38Chunk7] at h
  exact h.2

theorem tmFiber38ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber38StateAt 7) (tmFiber38StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber38StateAt 7) (tmFiber38StateAt 15)
    (tmFiber38RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber38Key tmFiber38Expected
        (tmFiber38RowAt 15) (by decide) tmFiber38ReverseRow_15_ok
      simpa [tmFiber38StateAt, tmFiber38RowAt, tmFiber38Rows, listGetD, directRow] using h)

theorem tmFiber38State0_in_pass1_prefix :
    tmFiber38StateAt 0 ∈ chainClosureStep tmWord [tmFiber38StateAt 0] [tmFiber38StateAt 0] := by
  exact chainClosureStep_mem_of_seen tmWord [tmFiber38StateAt 0] [tmFiber38StateAt 0] (tmFiber38StateAt 0) (by simp)

theorem tmFiber38State1_in_pass1_prefix :
    tmFiber38StateAt 1 ∈ chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1] [tmFiber38StateAt 0] := by
  have hparentBefore :
      tmFiber38StateAt 0 ∈ chainClosureStep tmWord [tmFiber38StateAt 0] [tmFiber38StateAt 0] := by
    exact tmFiber38State0_in_pass1_prefix
  rw [show [tmFiber38StateAt 0, tmFiber38StateAt 1] = [tmFiber38StateAt 0] ++ [tmFiber38StateAt 1] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber38StateAt 1) []
    (chainClosureStep tmWord [tmFiber38StateAt 0] [tmFiber38StateAt 0]) (tmFiber38StateAt 0)
    hparentBefore tmFiber38ReverseSingleStep1

theorem tmFiber38State2_in_pass1_prefix :
    tmFiber38StateAt 2 ∈ chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2] [tmFiber38StateAt 0] := by
  have hparentBefore :
      tmFiber38StateAt 0 ∈ chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1] [tmFiber38StateAt 0] := by
    rw [show [tmFiber38StateAt 0, tmFiber38StateAt 1] = [tmFiber38StateAt 0] ++ [tmFiber38StateAt 1] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber38StateAt 1]
      (chainClosureStep tmWord [tmFiber38StateAt 0] [tmFiber38StateAt 0]) (tmFiber38StateAt 0)
      tmFiber38State0_in_pass1_prefix
  rw [show [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2] = [tmFiber38StateAt 0, tmFiber38StateAt 1] ++ [tmFiber38StateAt 2] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber38StateAt 2) []
    (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1] [tmFiber38StateAt 0]) (tmFiber38StateAt 0)
    hparentBefore tmFiber38ReverseSingleStep2

theorem tmFiber38State3_in_pass1_prefix :
    tmFiber38StateAt 3 ∈ chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3] [tmFiber38StateAt 0] := by
  have hparentBefore :
      tmFiber38StateAt 1 ∈ chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2] [tmFiber38StateAt 0] := by
    rw [show [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2] = [tmFiber38StateAt 0, tmFiber38StateAt 1] ++ [tmFiber38StateAt 2] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber38StateAt 2]
      (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1] [tmFiber38StateAt 0]) (tmFiber38StateAt 1)
      tmFiber38State1_in_pass1_prefix
  rw [show [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3] = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2] ++ [tmFiber38StateAt 3] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber38StateAt 3) []
    (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2] [tmFiber38StateAt 0]) (tmFiber38StateAt 1)
    hparentBefore tmFiber38ReverseSingleStep3

theorem tmFiber38State4_in_pass1_prefix :
    tmFiber38StateAt 4 ∈ chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4] [tmFiber38StateAt 0] := by
  have hparentBefore :
      tmFiber38StateAt 0 ∈ chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3] [tmFiber38StateAt 0] := by
    rw [show [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3] = [tmFiber38StateAt 0] ++ [tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3]
      (chainClosureStep tmWord [tmFiber38StateAt 0] [tmFiber38StateAt 0]) (tmFiber38StateAt 0)
      tmFiber38State0_in_pass1_prefix
  rw [show [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4] = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3] ++ [tmFiber38StateAt 4] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber38StateAt 4) []
    (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3] [tmFiber38StateAt 0]) (tmFiber38StateAt 0)
    hparentBefore tmFiber38ReverseSingleStep4

theorem tmFiber38State5_in_pass1_prefix :
    tmFiber38StateAt 5 ∈ chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5] [tmFiber38StateAt 0] := by
  have hparentBefore :
      tmFiber38StateAt 1 ∈ chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4] [tmFiber38StateAt 0] := by
    rw [show [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4] = [tmFiber38StateAt 0, tmFiber38StateAt 1] ++ [tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4]
      (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1] [tmFiber38StateAt 0]) (tmFiber38StateAt 1)
      tmFiber38State1_in_pass1_prefix
  rw [show [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5] = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4] ++ [tmFiber38StateAt 5] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber38StateAt 5) []
    (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4] [tmFiber38StateAt 0]) (tmFiber38StateAt 1)
    hparentBefore tmFiber38ReverseSingleStep5

theorem tmFiber38State6_in_pass1_prefix :
    tmFiber38StateAt 6 ∈ chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6] [tmFiber38StateAt 0] := by
  have hparentBefore :
      tmFiber38StateAt 2 ∈ chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5] [tmFiber38StateAt 0] := by
    rw [show [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5] = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2] ++ [tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5]
      (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2] [tmFiber38StateAt 0]) (tmFiber38StateAt 2)
      tmFiber38State2_in_pass1_prefix
  rw [show [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6] = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5] ++ [tmFiber38StateAt 6] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber38StateAt 6) []
    (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5] [tmFiber38StateAt 0]) (tmFiber38StateAt 2)
    hparentBefore tmFiber38ReverseSingleStep6

theorem tmFiber38State7_in_pass1_prefix :
    tmFiber38StateAt 7 ∈ chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7] [tmFiber38StateAt 0] := by
  have hparentBefore :
      tmFiber38StateAt 3 ∈ chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6] [tmFiber38StateAt 0] := by
    rw [show [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6] = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3] ++ [tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6]
      (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3] [tmFiber38StateAt 0]) (tmFiber38StateAt 3)
      tmFiber38State3_in_pass1_prefix
  rw [show [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7] = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6] ++ [tmFiber38StateAt 7] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber38StateAt 7) []
    (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6] [tmFiber38StateAt 0]) (tmFiber38StateAt 3)
    hparentBefore tmFiber38ReverseSingleStep7

theorem tmFiber38State8_in_pass1_prefix :
    tmFiber38StateAt 8 ∈ chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8] [tmFiber38StateAt 0] := by
  have hparentBefore :
      tmFiber38StateAt 0 ∈ chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7] [tmFiber38StateAt 0] := by
    rw [show [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7] = [tmFiber38StateAt 0] ++ [tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7]
      (chainClosureStep tmWord [tmFiber38StateAt 0] [tmFiber38StateAt 0]) (tmFiber38StateAt 0)
      tmFiber38State0_in_pass1_prefix
  rw [show [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8] = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7] ++ [tmFiber38StateAt 8] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber38StateAt 8) []
    (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7] [tmFiber38StateAt 0]) (tmFiber38StateAt 0)
    hparentBefore tmFiber38ReverseSingleStep8

theorem tmFiber38State9_in_pass1_prefix :
    tmFiber38StateAt 9 ∈ chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9] [tmFiber38StateAt 0] := by
  have hparentBefore :
      tmFiber38StateAt 1 ∈ chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8] [tmFiber38StateAt 0] := by
    rw [show [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8] = [tmFiber38StateAt 0, tmFiber38StateAt 1] ++ [tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8]
      (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1] [tmFiber38StateAt 0]) (tmFiber38StateAt 1)
      tmFiber38State1_in_pass1_prefix
  rw [show [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9] = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8] ++ [tmFiber38StateAt 9] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber38StateAt 9) []
    (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8] [tmFiber38StateAt 0]) (tmFiber38StateAt 1)
    hparentBefore tmFiber38ReverseSingleStep9

theorem tmFiber38State10_in_pass1_prefix :
    tmFiber38StateAt 10 ∈ chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10] [tmFiber38StateAt 0] := by
  have hparentBefore :
      tmFiber38StateAt 2 ∈ chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9] [tmFiber38StateAt 0] := by
    rw [show [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9] = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2] ++ [tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9]
      (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2] [tmFiber38StateAt 0]) (tmFiber38StateAt 2)
      tmFiber38State2_in_pass1_prefix
  rw [show [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10] = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9] ++ [tmFiber38StateAt 10] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber38StateAt 10) []
    (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9] [tmFiber38StateAt 0]) (tmFiber38StateAt 2)
    hparentBefore tmFiber38ReverseSingleStep10

theorem tmFiber38State11_in_pass1_prefix :
    tmFiber38StateAt 11 ∈ chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11] [tmFiber38StateAt 0] := by
  have hparentBefore :
      tmFiber38StateAt 3 ∈ chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10] [tmFiber38StateAt 0] := by
    rw [show [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10] = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3] ++ [tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10]
      (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3] [tmFiber38StateAt 0]) (tmFiber38StateAt 3)
      tmFiber38State3_in_pass1_prefix
  rw [show [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11] = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10] ++ [tmFiber38StateAt 11] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber38StateAt 11) []
    (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10] [tmFiber38StateAt 0]) (tmFiber38StateAt 3)
    hparentBefore tmFiber38ReverseSingleStep11

theorem tmFiber38State12_in_pass1_prefix :
    tmFiber38StateAt 12 ∈ chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12] [tmFiber38StateAt 0] := by
  have hparentBefore :
      tmFiber38StateAt 4 ∈ chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11] [tmFiber38StateAt 0] := by
    rw [show [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11] = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4] ++ [tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11]
      (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4] [tmFiber38StateAt 0]) (tmFiber38StateAt 4)
      tmFiber38State4_in_pass1_prefix
  rw [show [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12] = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11] ++ [tmFiber38StateAt 12] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber38StateAt 12) []
    (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11] [tmFiber38StateAt 0]) (tmFiber38StateAt 4)
    hparentBefore tmFiber38ReverseSingleStep12

theorem tmFiber38State13_in_pass1_prefix :
    tmFiber38StateAt 13 ∈ chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13] [tmFiber38StateAt 0] := by
  have hparentBefore :
      tmFiber38StateAt 5 ∈ chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12] [tmFiber38StateAt 0] := by
    rw [show [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12] = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5] ++ [tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12]
      (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5] [tmFiber38StateAt 0]) (tmFiber38StateAt 5)
      tmFiber38State5_in_pass1_prefix
  rw [show [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13] = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12] ++ [tmFiber38StateAt 13] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber38StateAt 13) []
    (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12] [tmFiber38StateAt 0]) (tmFiber38StateAt 5)
    hparentBefore tmFiber38ReverseSingleStep13

theorem tmFiber38State14_in_pass1_prefix :
    tmFiber38StateAt 14 ∈ chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14] [tmFiber38StateAt 0] := by
  have hparentBefore :
      tmFiber38StateAt 6 ∈ chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13] [tmFiber38StateAt 0] := by
    rw [show [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13] = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6] ++ [tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13]
      (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6] [tmFiber38StateAt 0]) (tmFiber38StateAt 6)
      tmFiber38State6_in_pass1_prefix
  rw [show [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14] = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13] ++ [tmFiber38StateAt 14] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber38StateAt 14) []
    (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13] [tmFiber38StateAt 0]) (tmFiber38StateAt 6)
    hparentBefore tmFiber38ReverseSingleStep14

theorem tmFiber38State15_in_pass1_prefix :
    tmFiber38StateAt 15 ∈ chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14, tmFiber38StateAt 15] [tmFiber38StateAt 0] := by
  have hparentBefore :
      tmFiber38StateAt 7 ∈ chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14] [tmFiber38StateAt 0] := by
    rw [show [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14] = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7] ++ [tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14]
      (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7] [tmFiber38StateAt 0]) (tmFiber38StateAt 7)
      tmFiber38State7_in_pass1_prefix
  rw [show [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14, tmFiber38StateAt 15] = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14] ++ [tmFiber38StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber38StateAt 15) []
    (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14] [tmFiber38StateAt 0]) (tmFiber38StateAt 7)
    hparentBefore tmFiber38ReverseSingleStep15

theorem tmFiber38State0_in_pass1_full :
    tmFiber38StateAt 0 ∈ chainClosureStep tmWord tmFiber38DirectStates [tmFiber38StateAt 0] := by
  rw [show tmFiber38DirectStates = [tmFiber38StateAt 0] ++ [tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14, tmFiber38StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14, tmFiber38StateAt 15]
    (chainClosureStep tmWord [tmFiber38StateAt 0] [tmFiber38StateAt 0]) (tmFiber38StateAt 0)
    tmFiber38State0_in_pass1_prefix

theorem tmFiber38State1_in_pass1_full :
    tmFiber38StateAt 1 ∈ chainClosureStep tmWord tmFiber38DirectStates [tmFiber38StateAt 0] := by
  rw [show tmFiber38DirectStates = [tmFiber38StateAt 0, tmFiber38StateAt 1] ++ [tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14, tmFiber38StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14, tmFiber38StateAt 15]
    (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1] [tmFiber38StateAt 0]) (tmFiber38StateAt 1)
    tmFiber38State1_in_pass1_prefix

theorem tmFiber38State2_in_pass1_full :
    tmFiber38StateAt 2 ∈ chainClosureStep tmWord tmFiber38DirectStates [tmFiber38StateAt 0] := by
  rw [show tmFiber38DirectStates = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2] ++ [tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14, tmFiber38StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14, tmFiber38StateAt 15]
    (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2] [tmFiber38StateAt 0]) (tmFiber38StateAt 2)
    tmFiber38State2_in_pass1_prefix

theorem tmFiber38State3_in_pass1_full :
    tmFiber38StateAt 3 ∈ chainClosureStep tmWord tmFiber38DirectStates [tmFiber38StateAt 0] := by
  rw [show tmFiber38DirectStates = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3] ++ [tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14, tmFiber38StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14, tmFiber38StateAt 15]
    (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3] [tmFiber38StateAt 0]) (tmFiber38StateAt 3)
    tmFiber38State3_in_pass1_prefix

theorem tmFiber38State4_in_pass1_full :
    tmFiber38StateAt 4 ∈ chainClosureStep tmWord tmFiber38DirectStates [tmFiber38StateAt 0] := by
  rw [show tmFiber38DirectStates = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4] ++ [tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14, tmFiber38StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14, tmFiber38StateAt 15]
    (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4] [tmFiber38StateAt 0]) (tmFiber38StateAt 4)
    tmFiber38State4_in_pass1_prefix

theorem tmFiber38State5_in_pass1_full :
    tmFiber38StateAt 5 ∈ chainClosureStep tmWord tmFiber38DirectStates [tmFiber38StateAt 0] := by
  rw [show tmFiber38DirectStates = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5] ++ [tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14, tmFiber38StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14, tmFiber38StateAt 15]
    (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5] [tmFiber38StateAt 0]) (tmFiber38StateAt 5)
    tmFiber38State5_in_pass1_prefix

theorem tmFiber38State6_in_pass1_full :
    tmFiber38StateAt 6 ∈ chainClosureStep tmWord tmFiber38DirectStates [tmFiber38StateAt 0] := by
  rw [show tmFiber38DirectStates = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6] ++ [tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14, tmFiber38StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14, tmFiber38StateAt 15]
    (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6] [tmFiber38StateAt 0]) (tmFiber38StateAt 6)
    tmFiber38State6_in_pass1_prefix

theorem tmFiber38State7_in_pass1_full :
    tmFiber38StateAt 7 ∈ chainClosureStep tmWord tmFiber38DirectStates [tmFiber38StateAt 0] := by
  rw [show tmFiber38DirectStates = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7] ++ [tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14, tmFiber38StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14, tmFiber38StateAt 15]
    (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7] [tmFiber38StateAt 0]) (tmFiber38StateAt 7)
    tmFiber38State7_in_pass1_prefix

theorem tmFiber38State8_in_pass1_full :
    tmFiber38StateAt 8 ∈ chainClosureStep tmWord tmFiber38DirectStates [tmFiber38StateAt 0] := by
  rw [show tmFiber38DirectStates = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8] ++ [tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14, tmFiber38StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14, tmFiber38StateAt 15]
    (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8] [tmFiber38StateAt 0]) (tmFiber38StateAt 8)
    tmFiber38State8_in_pass1_prefix

theorem tmFiber38State9_in_pass1_full :
    tmFiber38StateAt 9 ∈ chainClosureStep tmWord tmFiber38DirectStates [tmFiber38StateAt 0] := by
  rw [show tmFiber38DirectStates = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9] ++ [tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14, tmFiber38StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14, tmFiber38StateAt 15]
    (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9] [tmFiber38StateAt 0]) (tmFiber38StateAt 9)
    tmFiber38State9_in_pass1_prefix

theorem tmFiber38State10_in_pass1_full :
    tmFiber38StateAt 10 ∈ chainClosureStep tmWord tmFiber38DirectStates [tmFiber38StateAt 0] := by
  rw [show tmFiber38DirectStates = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10] ++ [tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14, tmFiber38StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14, tmFiber38StateAt 15]
    (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10] [tmFiber38StateAt 0]) (tmFiber38StateAt 10)
    tmFiber38State10_in_pass1_prefix

theorem tmFiber38State11_in_pass1_full :
    tmFiber38StateAt 11 ∈ chainClosureStep tmWord tmFiber38DirectStates [tmFiber38StateAt 0] := by
  rw [show tmFiber38DirectStates = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11] ++ [tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14, tmFiber38StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14, tmFiber38StateAt 15]
    (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11] [tmFiber38StateAt 0]) (tmFiber38StateAt 11)
    tmFiber38State11_in_pass1_prefix

theorem tmFiber38State12_in_pass1_full :
    tmFiber38StateAt 12 ∈ chainClosureStep tmWord tmFiber38DirectStates [tmFiber38StateAt 0] := by
  rw [show tmFiber38DirectStates = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12] ++ [tmFiber38StateAt 13, tmFiber38StateAt 14, tmFiber38StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber38StateAt 13, tmFiber38StateAt 14, tmFiber38StateAt 15]
    (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12] [tmFiber38StateAt 0]) (tmFiber38StateAt 12)
    tmFiber38State12_in_pass1_prefix

theorem tmFiber38State13_in_pass1_full :
    tmFiber38StateAt 13 ∈ chainClosureStep tmWord tmFiber38DirectStates [tmFiber38StateAt 0] := by
  rw [show tmFiber38DirectStates = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13] ++ [tmFiber38StateAt 14, tmFiber38StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber38StateAt 14, tmFiber38StateAt 15]
    (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13] [tmFiber38StateAt 0]) (tmFiber38StateAt 13)
    tmFiber38State13_in_pass1_prefix

theorem tmFiber38State14_in_pass1_full :
    tmFiber38StateAt 14 ∈ chainClosureStep tmWord tmFiber38DirectStates [tmFiber38StateAt 0] := by
  rw [show tmFiber38DirectStates = [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14] ++ [tmFiber38StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber38StateAt 15]
    (chainClosureStep tmWord [tmFiber38StateAt 0, tmFiber38StateAt 1, tmFiber38StateAt 2, tmFiber38StateAt 3, tmFiber38StateAt 4, tmFiber38StateAt 5, tmFiber38StateAt 6, tmFiber38StateAt 7, tmFiber38StateAt 8, tmFiber38StateAt 9, tmFiber38StateAt 10, tmFiber38StateAt 11, tmFiber38StateAt 12, tmFiber38StateAt 13, tmFiber38StateAt 14] [tmFiber38StateAt 0]) (tmFiber38StateAt 14)
    tmFiber38State14_in_pass1_prefix

theorem tmFiber38State15_in_pass1_full :
    tmFiber38StateAt 15 ∈ chainClosureStep tmWord tmFiber38DirectStates [tmFiber38StateAt 0] := by
  simpa [tmFiber38DirectStates] using tmFiber38State15_in_pass1_prefix

theorem tmFiber38State0_in_close :
    tmFiber38StateAt 0 ∈ closeChainFiber tmWord tmFiber38DirectStates tmFiber38DirectStates.length [tmFiber38StateAt 0] := by
  change tmFiber38StateAt 0 ∈ closeChainFiber tmWord tmFiber38DirectStates (15 + 1) [tmFiber38StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber38DirectStates 15 [tmFiber38StateAt 0] (tmFiber38StateAt 0) tmFiber38State0_in_pass1_full

theorem tmFiber38State1_in_close :
    tmFiber38StateAt 1 ∈ closeChainFiber tmWord tmFiber38DirectStates tmFiber38DirectStates.length [tmFiber38StateAt 0] := by
  change tmFiber38StateAt 1 ∈ closeChainFiber tmWord tmFiber38DirectStates (15 + 1) [tmFiber38StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber38DirectStates 15 [tmFiber38StateAt 0] (tmFiber38StateAt 1) tmFiber38State1_in_pass1_full

theorem tmFiber38State2_in_close :
    tmFiber38StateAt 2 ∈ closeChainFiber tmWord tmFiber38DirectStates tmFiber38DirectStates.length [tmFiber38StateAt 0] := by
  change tmFiber38StateAt 2 ∈ closeChainFiber tmWord tmFiber38DirectStates (15 + 1) [tmFiber38StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber38DirectStates 15 [tmFiber38StateAt 0] (tmFiber38StateAt 2) tmFiber38State2_in_pass1_full

theorem tmFiber38State3_in_close :
    tmFiber38StateAt 3 ∈ closeChainFiber tmWord tmFiber38DirectStates tmFiber38DirectStates.length [tmFiber38StateAt 0] := by
  change tmFiber38StateAt 3 ∈ closeChainFiber tmWord tmFiber38DirectStates (15 + 1) [tmFiber38StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber38DirectStates 15 [tmFiber38StateAt 0] (tmFiber38StateAt 3) tmFiber38State3_in_pass1_full

theorem tmFiber38State4_in_close :
    tmFiber38StateAt 4 ∈ closeChainFiber tmWord tmFiber38DirectStates tmFiber38DirectStates.length [tmFiber38StateAt 0] := by
  change tmFiber38StateAt 4 ∈ closeChainFiber tmWord tmFiber38DirectStates (15 + 1) [tmFiber38StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber38DirectStates 15 [tmFiber38StateAt 0] (tmFiber38StateAt 4) tmFiber38State4_in_pass1_full

theorem tmFiber38State5_in_close :
    tmFiber38StateAt 5 ∈ closeChainFiber tmWord tmFiber38DirectStates tmFiber38DirectStates.length [tmFiber38StateAt 0] := by
  change tmFiber38StateAt 5 ∈ closeChainFiber tmWord tmFiber38DirectStates (15 + 1) [tmFiber38StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber38DirectStates 15 [tmFiber38StateAt 0] (tmFiber38StateAt 5) tmFiber38State5_in_pass1_full

theorem tmFiber38State6_in_close :
    tmFiber38StateAt 6 ∈ closeChainFiber tmWord tmFiber38DirectStates tmFiber38DirectStates.length [tmFiber38StateAt 0] := by
  change tmFiber38StateAt 6 ∈ closeChainFiber tmWord tmFiber38DirectStates (15 + 1) [tmFiber38StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber38DirectStates 15 [tmFiber38StateAt 0] (tmFiber38StateAt 6) tmFiber38State6_in_pass1_full

theorem tmFiber38State7_in_close :
    tmFiber38StateAt 7 ∈ closeChainFiber tmWord tmFiber38DirectStates tmFiber38DirectStates.length [tmFiber38StateAt 0] := by
  change tmFiber38StateAt 7 ∈ closeChainFiber tmWord tmFiber38DirectStates (15 + 1) [tmFiber38StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber38DirectStates 15 [tmFiber38StateAt 0] (tmFiber38StateAt 7) tmFiber38State7_in_pass1_full

theorem tmFiber38State8_in_close :
    tmFiber38StateAt 8 ∈ closeChainFiber tmWord tmFiber38DirectStates tmFiber38DirectStates.length [tmFiber38StateAt 0] := by
  change tmFiber38StateAt 8 ∈ closeChainFiber tmWord tmFiber38DirectStates (15 + 1) [tmFiber38StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber38DirectStates 15 [tmFiber38StateAt 0] (tmFiber38StateAt 8) tmFiber38State8_in_pass1_full

theorem tmFiber38State9_in_close :
    tmFiber38StateAt 9 ∈ closeChainFiber tmWord tmFiber38DirectStates tmFiber38DirectStates.length [tmFiber38StateAt 0] := by
  change tmFiber38StateAt 9 ∈ closeChainFiber tmWord tmFiber38DirectStates (15 + 1) [tmFiber38StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber38DirectStates 15 [tmFiber38StateAt 0] (tmFiber38StateAt 9) tmFiber38State9_in_pass1_full

theorem tmFiber38State10_in_close :
    tmFiber38StateAt 10 ∈ closeChainFiber tmWord tmFiber38DirectStates tmFiber38DirectStates.length [tmFiber38StateAt 0] := by
  change tmFiber38StateAt 10 ∈ closeChainFiber tmWord tmFiber38DirectStates (15 + 1) [tmFiber38StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber38DirectStates 15 [tmFiber38StateAt 0] (tmFiber38StateAt 10) tmFiber38State10_in_pass1_full

theorem tmFiber38State11_in_close :
    tmFiber38StateAt 11 ∈ closeChainFiber tmWord tmFiber38DirectStates tmFiber38DirectStates.length [tmFiber38StateAt 0] := by
  change tmFiber38StateAt 11 ∈ closeChainFiber tmWord tmFiber38DirectStates (15 + 1) [tmFiber38StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber38DirectStates 15 [tmFiber38StateAt 0] (tmFiber38StateAt 11) tmFiber38State11_in_pass1_full

theorem tmFiber38State12_in_close :
    tmFiber38StateAt 12 ∈ closeChainFiber tmWord tmFiber38DirectStates tmFiber38DirectStates.length [tmFiber38StateAt 0] := by
  change tmFiber38StateAt 12 ∈ closeChainFiber tmWord tmFiber38DirectStates (15 + 1) [tmFiber38StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber38DirectStates 15 [tmFiber38StateAt 0] (tmFiber38StateAt 12) tmFiber38State12_in_pass1_full

theorem tmFiber38State13_in_close :
    tmFiber38StateAt 13 ∈ closeChainFiber tmWord tmFiber38DirectStates tmFiber38DirectStates.length [tmFiber38StateAt 0] := by
  change tmFiber38StateAt 13 ∈ closeChainFiber tmWord tmFiber38DirectStates (15 + 1) [tmFiber38StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber38DirectStates 15 [tmFiber38StateAt 0] (tmFiber38StateAt 13) tmFiber38State13_in_pass1_full

theorem tmFiber38State14_in_close :
    tmFiber38StateAt 14 ∈ closeChainFiber tmWord tmFiber38DirectStates tmFiber38DirectStates.length [tmFiber38StateAt 0] := by
  change tmFiber38StateAt 14 ∈ closeChainFiber tmWord tmFiber38DirectStates (15 + 1) [tmFiber38StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber38DirectStates 15 [tmFiber38StateAt 0] (tmFiber38StateAt 14) tmFiber38State14_in_pass1_full

theorem tmFiber38State15_in_close :
    tmFiber38StateAt 15 ∈ closeChainFiber tmWord tmFiber38DirectStates tmFiber38DirectStates.length [tmFiber38StateAt 0] := by
  change tmFiber38StateAt 15 ∈ closeChainFiber tmWord tmFiber38DirectStates (15 + 1) [tmFiber38StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber38DirectStates 15 [tmFiber38StateAt 0] (tmFiber38StateAt 15) tmFiber38State15_in_pass1_full

theorem tmFiber38DirectConnected :
    chainFiberConnected tmWord tmFiber38DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber38DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber38State0_in_close
  · subst state
    exact tmFiber38State1_in_close
  · subst state
    exact tmFiber38State2_in_close
  · subst state
    exact tmFiber38State3_in_close
  · subst state
    exact tmFiber38State4_in_close
  · subst state
    exact tmFiber38State5_in_close
  · subst state
    exact tmFiber38State6_in_close
  · subst state
    exact tmFiber38State7_in_close
  · subst state
    exact tmFiber38State8_in_close
  · subst state
    exact tmFiber38State9_in_close
  · subst state
    exact tmFiber38State10_in_close
  · subst state
    exact tmFiber38State11_in_close
  · subst state
    exact tmFiber38State12_in_close
  · subst state
    exact tmFiber38State13_in_close
  · subst state
    exact tmFiber38State14_in_close
  · subst state
    exact tmFiber38State15_in_close
  · cases h

end GoertzelLemma818LengthTwoTMShape16Bridge

end Mettapedia.GraphTheory.FourColor
