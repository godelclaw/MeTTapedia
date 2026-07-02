import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for size-16 `normal,mirror` length-two fibers, group 5

This module proves direct connectedness for four generated `normal,mirror`
size-16 fibers from row-local reverse certificate chunks, keeping Lean on
default recursion limits.
-/

namespace GoertzelLemma818LengthTwoTMShape16Bridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818TauMirrorCertificate
open GoertzelLemma818TauMirrorReverseAudit

def tmFiber73StateAt (i : Nat) : List TauState :=
  directStates (tmFiber73RowAt i).sourceLeft (tmFiber73RowAt i).sourceRight

def tmFiber73DirectStates : List (List TauState) :=
  [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14, tmFiber73StateAt 15]

theorem tmFiber73ReverseRow_1_ok :
    tmRowReverseValid tmFiber73Key tmFiber73Expected (tmFiber73RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber73Chunk0_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber73Chunk0] at h
  exact h.2

theorem tmFiber73ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber73StateAt 0) (tmFiber73StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber73StateAt 0) (tmFiber73StateAt 1)
    (tmFiber73RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber73Key tmFiber73Expected
        (tmFiber73RowAt 1) (by decide) tmFiber73ReverseRow_1_ok
      simpa [tmFiber73StateAt, tmFiber73RowAt, tmFiber73Rows, listGetD, directRow] using h)

theorem tmFiber73ReverseRow_2_ok :
    tmRowReverseValid tmFiber73Key tmFiber73Expected (tmFiber73RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber73Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber73Chunk1] at h
  exact h.1

theorem tmFiber73ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber73StateAt 0) (tmFiber73StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber73StateAt 0) (tmFiber73StateAt 2)
    (tmFiber73RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber73Key tmFiber73Expected
        (tmFiber73RowAt 2) (by decide) tmFiber73ReverseRow_2_ok
      simpa [tmFiber73StateAt, tmFiber73RowAt, tmFiber73Rows, listGetD, directRow] using h)

theorem tmFiber73ReverseRow_3_ok :
    tmRowReverseValid tmFiber73Key tmFiber73Expected (tmFiber73RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber73Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber73Chunk1] at h
  exact h.2

theorem tmFiber73ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber73StateAt 1) (tmFiber73StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber73StateAt 1) (tmFiber73StateAt 3)
    (tmFiber73RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber73Key tmFiber73Expected
        (tmFiber73RowAt 3) (by decide) tmFiber73ReverseRow_3_ok
      simpa [tmFiber73StateAt, tmFiber73RowAt, tmFiber73Rows, listGetD, directRow] using h)

theorem tmFiber73ReverseRow_4_ok :
    tmRowReverseValid tmFiber73Key tmFiber73Expected (tmFiber73RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber73Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber73Chunk2] at h
  exact h.1

theorem tmFiber73ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber73StateAt 0) (tmFiber73StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber73StateAt 0) (tmFiber73StateAt 4)
    (tmFiber73RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber73Key tmFiber73Expected
        (tmFiber73RowAt 4) (by decide) tmFiber73ReverseRow_4_ok
      simpa [tmFiber73StateAt, tmFiber73RowAt, tmFiber73Rows, listGetD, directRow] using h)

theorem tmFiber73ReverseRow_5_ok :
    tmRowReverseValid tmFiber73Key tmFiber73Expected (tmFiber73RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber73Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber73Chunk2] at h
  exact h.2

theorem tmFiber73ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber73StateAt 1) (tmFiber73StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber73StateAt 1) (tmFiber73StateAt 5)
    (tmFiber73RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber73Key tmFiber73Expected
        (tmFiber73RowAt 5) (by decide) tmFiber73ReverseRow_5_ok
      simpa [tmFiber73StateAt, tmFiber73RowAt, tmFiber73Rows, listGetD, directRow] using h)

theorem tmFiber73ReverseRow_6_ok :
    tmRowReverseValid tmFiber73Key tmFiber73Expected (tmFiber73RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber73Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber73Chunk3] at h
  exact h.1

theorem tmFiber73ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber73StateAt 2) (tmFiber73StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber73StateAt 2) (tmFiber73StateAt 6)
    (tmFiber73RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber73Key tmFiber73Expected
        (tmFiber73RowAt 6) (by decide) tmFiber73ReverseRow_6_ok
      simpa [tmFiber73StateAt, tmFiber73RowAt, tmFiber73Rows, listGetD, directRow] using h)

theorem tmFiber73ReverseRow_7_ok :
    tmRowReverseValid tmFiber73Key tmFiber73Expected (tmFiber73RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber73Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber73Chunk3] at h
  exact h.2

theorem tmFiber73ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber73StateAt 3) (tmFiber73StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber73StateAt 3) (tmFiber73StateAt 7)
    (tmFiber73RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber73Key tmFiber73Expected
        (tmFiber73RowAt 7) (by decide) tmFiber73ReverseRow_7_ok
      simpa [tmFiber73StateAt, tmFiber73RowAt, tmFiber73Rows, listGetD, directRow] using h)

theorem tmFiber73ReverseRow_8_ok :
    tmRowReverseValid tmFiber73Key tmFiber73Expected (tmFiber73RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber73Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber73Chunk4] at h
  exact h.1

theorem tmFiber73ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber73StateAt 4) (tmFiber73StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber73StateAt 4) (tmFiber73StateAt 8)
    (tmFiber73RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber73Key tmFiber73Expected
        (tmFiber73RowAt 8) (by decide) tmFiber73ReverseRow_8_ok
      simpa [tmFiber73StateAt, tmFiber73RowAt, tmFiber73Rows, listGetD, directRow] using h)

theorem tmFiber73ReverseRow_9_ok :
    tmRowReverseValid tmFiber73Key tmFiber73Expected (tmFiber73RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber73Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber73Chunk4] at h
  exact h.2

theorem tmFiber73ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber73StateAt 5) (tmFiber73StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber73StateAt 5) (tmFiber73StateAt 9)
    (tmFiber73RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber73Key tmFiber73Expected
        (tmFiber73RowAt 9) (by decide) tmFiber73ReverseRow_9_ok
      simpa [tmFiber73StateAt, tmFiber73RowAt, tmFiber73Rows, listGetD, directRow] using h)

theorem tmFiber73ReverseRow_10_ok :
    tmRowReverseValid tmFiber73Key tmFiber73Expected (tmFiber73RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber73Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber73Chunk5] at h
  exact h.1

theorem tmFiber73ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber73StateAt 6) (tmFiber73StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber73StateAt 6) (tmFiber73StateAt 10)
    (tmFiber73RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber73Key tmFiber73Expected
        (tmFiber73RowAt 10) (by decide) tmFiber73ReverseRow_10_ok
      simpa [tmFiber73StateAt, tmFiber73RowAt, tmFiber73Rows, listGetD, directRow] using h)

theorem tmFiber73ReverseRow_11_ok :
    tmRowReverseValid tmFiber73Key tmFiber73Expected (tmFiber73RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber73Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber73Chunk5] at h
  exact h.2

theorem tmFiber73ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber73StateAt 7) (tmFiber73StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber73StateAt 7) (tmFiber73StateAt 11)
    (tmFiber73RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber73Key tmFiber73Expected
        (tmFiber73RowAt 11) (by decide) tmFiber73ReverseRow_11_ok
      simpa [tmFiber73StateAt, tmFiber73RowAt, tmFiber73Rows, listGetD, directRow] using h)

theorem tmFiber73ReverseRow_12_ok :
    tmRowReverseValid tmFiber73Key tmFiber73Expected (tmFiber73RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber73Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber73Chunk6] at h
  exact h.1

theorem tmFiber73ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber73StateAt 0) (tmFiber73StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber73StateAt 0) (tmFiber73StateAt 12)
    (tmFiber73RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber73Key tmFiber73Expected
        (tmFiber73RowAt 12) (by decide) tmFiber73ReverseRow_12_ok
      simpa [tmFiber73StateAt, tmFiber73RowAt, tmFiber73Rows, listGetD, directRow] using h)

theorem tmFiber73ReverseRow_13_ok :
    tmRowReverseValid tmFiber73Key tmFiber73Expected (tmFiber73RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber73Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber73Chunk6] at h
  exact h.2

theorem tmFiber73ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber73StateAt 1) (tmFiber73StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber73StateAt 1) (tmFiber73StateAt 13)
    (tmFiber73RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber73Key tmFiber73Expected
        (tmFiber73RowAt 13) (by decide) tmFiber73ReverseRow_13_ok
      simpa [tmFiber73StateAt, tmFiber73RowAt, tmFiber73Rows, listGetD, directRow] using h)

theorem tmFiber73ReverseRow_14_ok :
    tmRowReverseValid tmFiber73Key tmFiber73Expected (tmFiber73RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber73Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber73Chunk7] at h
  exact h.1

theorem tmFiber73ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber73StateAt 2) (tmFiber73StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber73StateAt 2) (tmFiber73StateAt 14)
    (tmFiber73RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber73Key tmFiber73Expected
        (tmFiber73RowAt 14) (by decide) tmFiber73ReverseRow_14_ok
      simpa [tmFiber73StateAt, tmFiber73RowAt, tmFiber73Rows, listGetD, directRow] using h)

theorem tmFiber73ReverseRow_15_ok :
    tmRowReverseValid tmFiber73Key tmFiber73Expected (tmFiber73RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber73Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber73Chunk7] at h
  exact h.2

theorem tmFiber73ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber73StateAt 3) (tmFiber73StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber73StateAt 3) (tmFiber73StateAt 15)
    (tmFiber73RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber73Key tmFiber73Expected
        (tmFiber73RowAt 15) (by decide) tmFiber73ReverseRow_15_ok
      simpa [tmFiber73StateAt, tmFiber73RowAt, tmFiber73Rows, listGetD, directRow] using h)

theorem tmFiber73State0_in_pass1_prefix :
    tmFiber73StateAt 0 ∈ chainClosureStep tmWord [tmFiber73StateAt 0] [tmFiber73StateAt 0] := by
  exact chainClosureStep_mem_of_seen tmWord [tmFiber73StateAt 0] [tmFiber73StateAt 0] (tmFiber73StateAt 0) (by simp)

theorem tmFiber73State1_in_pass1_prefix :
    tmFiber73StateAt 1 ∈ chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1] [tmFiber73StateAt 0] := by
  have hparentBefore :
      tmFiber73StateAt 0 ∈ chainClosureStep tmWord [tmFiber73StateAt 0] [tmFiber73StateAt 0] := by
    exact tmFiber73State0_in_pass1_prefix
  rw [show [tmFiber73StateAt 0, tmFiber73StateAt 1] = [tmFiber73StateAt 0] ++ [tmFiber73StateAt 1] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber73StateAt 1) []
    (chainClosureStep tmWord [tmFiber73StateAt 0] [tmFiber73StateAt 0]) (tmFiber73StateAt 0)
    hparentBefore tmFiber73ReverseSingleStep1

theorem tmFiber73State2_in_pass1_prefix :
    tmFiber73StateAt 2 ∈ chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2] [tmFiber73StateAt 0] := by
  have hparentBefore :
      tmFiber73StateAt 0 ∈ chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1] [tmFiber73StateAt 0] := by
    rw [show [tmFiber73StateAt 0, tmFiber73StateAt 1] = [tmFiber73StateAt 0] ++ [tmFiber73StateAt 1] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber73StateAt 1]
      (chainClosureStep tmWord [tmFiber73StateAt 0] [tmFiber73StateAt 0]) (tmFiber73StateAt 0)
      tmFiber73State0_in_pass1_prefix
  rw [show [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2] = [tmFiber73StateAt 0, tmFiber73StateAt 1] ++ [tmFiber73StateAt 2] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber73StateAt 2) []
    (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1] [tmFiber73StateAt 0]) (tmFiber73StateAt 0)
    hparentBefore tmFiber73ReverseSingleStep2

theorem tmFiber73State3_in_pass1_prefix :
    tmFiber73StateAt 3 ∈ chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3] [tmFiber73StateAt 0] := by
  have hparentBefore :
      tmFiber73StateAt 1 ∈ chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2] [tmFiber73StateAt 0] := by
    rw [show [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2] = [tmFiber73StateAt 0, tmFiber73StateAt 1] ++ [tmFiber73StateAt 2] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber73StateAt 2]
      (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1] [tmFiber73StateAt 0]) (tmFiber73StateAt 1)
      tmFiber73State1_in_pass1_prefix
  rw [show [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3] = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2] ++ [tmFiber73StateAt 3] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber73StateAt 3) []
    (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2] [tmFiber73StateAt 0]) (tmFiber73StateAt 1)
    hparentBefore tmFiber73ReverseSingleStep3

theorem tmFiber73State4_in_pass1_prefix :
    tmFiber73StateAt 4 ∈ chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4] [tmFiber73StateAt 0] := by
  have hparentBefore :
      tmFiber73StateAt 0 ∈ chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3] [tmFiber73StateAt 0] := by
    rw [show [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3] = [tmFiber73StateAt 0] ++ [tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3]
      (chainClosureStep tmWord [tmFiber73StateAt 0] [tmFiber73StateAt 0]) (tmFiber73StateAt 0)
      tmFiber73State0_in_pass1_prefix
  rw [show [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4] = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3] ++ [tmFiber73StateAt 4] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber73StateAt 4) []
    (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3] [tmFiber73StateAt 0]) (tmFiber73StateAt 0)
    hparentBefore tmFiber73ReverseSingleStep4

theorem tmFiber73State5_in_pass1_prefix :
    tmFiber73StateAt 5 ∈ chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5] [tmFiber73StateAt 0] := by
  have hparentBefore :
      tmFiber73StateAt 1 ∈ chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4] [tmFiber73StateAt 0] := by
    rw [show [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4] = [tmFiber73StateAt 0, tmFiber73StateAt 1] ++ [tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4]
      (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1] [tmFiber73StateAt 0]) (tmFiber73StateAt 1)
      tmFiber73State1_in_pass1_prefix
  rw [show [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5] = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4] ++ [tmFiber73StateAt 5] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber73StateAt 5) []
    (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4] [tmFiber73StateAt 0]) (tmFiber73StateAt 1)
    hparentBefore tmFiber73ReverseSingleStep5

theorem tmFiber73State6_in_pass1_prefix :
    tmFiber73StateAt 6 ∈ chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6] [tmFiber73StateAt 0] := by
  have hparentBefore :
      tmFiber73StateAt 2 ∈ chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5] [tmFiber73StateAt 0] := by
    rw [show [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5] = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2] ++ [tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5]
      (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2] [tmFiber73StateAt 0]) (tmFiber73StateAt 2)
      tmFiber73State2_in_pass1_prefix
  rw [show [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6] = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5] ++ [tmFiber73StateAt 6] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber73StateAt 6) []
    (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5] [tmFiber73StateAt 0]) (tmFiber73StateAt 2)
    hparentBefore tmFiber73ReverseSingleStep6

theorem tmFiber73State7_in_pass1_prefix :
    tmFiber73StateAt 7 ∈ chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7] [tmFiber73StateAt 0] := by
  have hparentBefore :
      tmFiber73StateAt 3 ∈ chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6] [tmFiber73StateAt 0] := by
    rw [show [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6] = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3] ++ [tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6]
      (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3] [tmFiber73StateAt 0]) (tmFiber73StateAt 3)
      tmFiber73State3_in_pass1_prefix
  rw [show [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7] = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6] ++ [tmFiber73StateAt 7] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber73StateAt 7) []
    (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6] [tmFiber73StateAt 0]) (tmFiber73StateAt 3)
    hparentBefore tmFiber73ReverseSingleStep7

theorem tmFiber73State8_in_pass1_prefix :
    tmFiber73StateAt 8 ∈ chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8] [tmFiber73StateAt 0] := by
  have hparentBefore :
      tmFiber73StateAt 4 ∈ chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7] [tmFiber73StateAt 0] := by
    rw [show [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7] = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4] ++ [tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7]
      (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4] [tmFiber73StateAt 0]) (tmFiber73StateAt 4)
      tmFiber73State4_in_pass1_prefix
  rw [show [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8] = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7] ++ [tmFiber73StateAt 8] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber73StateAt 8) []
    (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7] [tmFiber73StateAt 0]) (tmFiber73StateAt 4)
    hparentBefore tmFiber73ReverseSingleStep8

theorem tmFiber73State9_in_pass1_prefix :
    tmFiber73StateAt 9 ∈ chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9] [tmFiber73StateAt 0] := by
  have hparentBefore :
      tmFiber73StateAt 5 ∈ chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8] [tmFiber73StateAt 0] := by
    rw [show [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8] = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5] ++ [tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8]
      (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5] [tmFiber73StateAt 0]) (tmFiber73StateAt 5)
      tmFiber73State5_in_pass1_prefix
  rw [show [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9] = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8] ++ [tmFiber73StateAt 9] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber73StateAt 9) []
    (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8] [tmFiber73StateAt 0]) (tmFiber73StateAt 5)
    hparentBefore tmFiber73ReverseSingleStep9

theorem tmFiber73State10_in_pass1_prefix :
    tmFiber73StateAt 10 ∈ chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10] [tmFiber73StateAt 0] := by
  have hparentBefore :
      tmFiber73StateAt 6 ∈ chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9] [tmFiber73StateAt 0] := by
    rw [show [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9] = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6] ++ [tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9]
      (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6] [tmFiber73StateAt 0]) (tmFiber73StateAt 6)
      tmFiber73State6_in_pass1_prefix
  rw [show [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10] = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9] ++ [tmFiber73StateAt 10] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber73StateAt 10) []
    (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9] [tmFiber73StateAt 0]) (tmFiber73StateAt 6)
    hparentBefore tmFiber73ReverseSingleStep10

theorem tmFiber73State11_in_pass1_prefix :
    tmFiber73StateAt 11 ∈ chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11] [tmFiber73StateAt 0] := by
  have hparentBefore :
      tmFiber73StateAt 7 ∈ chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10] [tmFiber73StateAt 0] := by
    rw [show [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10] = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7] ++ [tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10]
      (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7] [tmFiber73StateAt 0]) (tmFiber73StateAt 7)
      tmFiber73State7_in_pass1_prefix
  rw [show [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11] = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10] ++ [tmFiber73StateAt 11] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber73StateAt 11) []
    (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10] [tmFiber73StateAt 0]) (tmFiber73StateAt 7)
    hparentBefore tmFiber73ReverseSingleStep11

theorem tmFiber73State12_in_pass1_prefix :
    tmFiber73StateAt 12 ∈ chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12] [tmFiber73StateAt 0] := by
  have hparentBefore :
      tmFiber73StateAt 0 ∈ chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11] [tmFiber73StateAt 0] := by
    rw [show [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11] = [tmFiber73StateAt 0] ++ [tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11]
      (chainClosureStep tmWord [tmFiber73StateAt 0] [tmFiber73StateAt 0]) (tmFiber73StateAt 0)
      tmFiber73State0_in_pass1_prefix
  rw [show [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12] = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11] ++ [tmFiber73StateAt 12] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber73StateAt 12) []
    (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11] [tmFiber73StateAt 0]) (tmFiber73StateAt 0)
    hparentBefore tmFiber73ReverseSingleStep12

theorem tmFiber73State13_in_pass1_prefix :
    tmFiber73StateAt 13 ∈ chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13] [tmFiber73StateAt 0] := by
  have hparentBefore :
      tmFiber73StateAt 1 ∈ chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12] [tmFiber73StateAt 0] := by
    rw [show [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12] = [tmFiber73StateAt 0, tmFiber73StateAt 1] ++ [tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12]
      (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1] [tmFiber73StateAt 0]) (tmFiber73StateAt 1)
      tmFiber73State1_in_pass1_prefix
  rw [show [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13] = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12] ++ [tmFiber73StateAt 13] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber73StateAt 13) []
    (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12] [tmFiber73StateAt 0]) (tmFiber73StateAt 1)
    hparentBefore tmFiber73ReverseSingleStep13

theorem tmFiber73State14_in_pass1_prefix :
    tmFiber73StateAt 14 ∈ chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14] [tmFiber73StateAt 0] := by
  have hparentBefore :
      tmFiber73StateAt 2 ∈ chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13] [tmFiber73StateAt 0] := by
    rw [show [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13] = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2] ++ [tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13]
      (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2] [tmFiber73StateAt 0]) (tmFiber73StateAt 2)
      tmFiber73State2_in_pass1_prefix
  rw [show [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14] = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13] ++ [tmFiber73StateAt 14] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber73StateAt 14) []
    (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13] [tmFiber73StateAt 0]) (tmFiber73StateAt 2)
    hparentBefore tmFiber73ReverseSingleStep14

theorem tmFiber73State15_in_pass1_prefix :
    tmFiber73StateAt 15 ∈ chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14, tmFiber73StateAt 15] [tmFiber73StateAt 0] := by
  have hparentBefore :
      tmFiber73StateAt 3 ∈ chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14] [tmFiber73StateAt 0] := by
    rw [show [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14] = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3] ++ [tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14]
      (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3] [tmFiber73StateAt 0]) (tmFiber73StateAt 3)
      tmFiber73State3_in_pass1_prefix
  rw [show [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14, tmFiber73StateAt 15] = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14] ++ [tmFiber73StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber73StateAt 15) []
    (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14] [tmFiber73StateAt 0]) (tmFiber73StateAt 3)
    hparentBefore tmFiber73ReverseSingleStep15

theorem tmFiber73State0_in_pass1_full :
    tmFiber73StateAt 0 ∈ chainClosureStep tmWord tmFiber73DirectStates [tmFiber73StateAt 0] := by
  rw [show tmFiber73DirectStates = [tmFiber73StateAt 0] ++ [tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14, tmFiber73StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14, tmFiber73StateAt 15]
    (chainClosureStep tmWord [tmFiber73StateAt 0] [tmFiber73StateAt 0]) (tmFiber73StateAt 0)
    tmFiber73State0_in_pass1_prefix

theorem tmFiber73State1_in_pass1_full :
    tmFiber73StateAt 1 ∈ chainClosureStep tmWord tmFiber73DirectStates [tmFiber73StateAt 0] := by
  rw [show tmFiber73DirectStates = [tmFiber73StateAt 0, tmFiber73StateAt 1] ++ [tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14, tmFiber73StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14, tmFiber73StateAt 15]
    (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1] [tmFiber73StateAt 0]) (tmFiber73StateAt 1)
    tmFiber73State1_in_pass1_prefix

theorem tmFiber73State2_in_pass1_full :
    tmFiber73StateAt 2 ∈ chainClosureStep tmWord tmFiber73DirectStates [tmFiber73StateAt 0] := by
  rw [show tmFiber73DirectStates = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2] ++ [tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14, tmFiber73StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14, tmFiber73StateAt 15]
    (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2] [tmFiber73StateAt 0]) (tmFiber73StateAt 2)
    tmFiber73State2_in_pass1_prefix

theorem tmFiber73State3_in_pass1_full :
    tmFiber73StateAt 3 ∈ chainClosureStep tmWord tmFiber73DirectStates [tmFiber73StateAt 0] := by
  rw [show tmFiber73DirectStates = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3] ++ [tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14, tmFiber73StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14, tmFiber73StateAt 15]
    (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3] [tmFiber73StateAt 0]) (tmFiber73StateAt 3)
    tmFiber73State3_in_pass1_prefix

theorem tmFiber73State4_in_pass1_full :
    tmFiber73StateAt 4 ∈ chainClosureStep tmWord tmFiber73DirectStates [tmFiber73StateAt 0] := by
  rw [show tmFiber73DirectStates = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4] ++ [tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14, tmFiber73StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14, tmFiber73StateAt 15]
    (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4] [tmFiber73StateAt 0]) (tmFiber73StateAt 4)
    tmFiber73State4_in_pass1_prefix

theorem tmFiber73State5_in_pass1_full :
    tmFiber73StateAt 5 ∈ chainClosureStep tmWord tmFiber73DirectStates [tmFiber73StateAt 0] := by
  rw [show tmFiber73DirectStates = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5] ++ [tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14, tmFiber73StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14, tmFiber73StateAt 15]
    (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5] [tmFiber73StateAt 0]) (tmFiber73StateAt 5)
    tmFiber73State5_in_pass1_prefix

theorem tmFiber73State6_in_pass1_full :
    tmFiber73StateAt 6 ∈ chainClosureStep tmWord tmFiber73DirectStates [tmFiber73StateAt 0] := by
  rw [show tmFiber73DirectStates = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6] ++ [tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14, tmFiber73StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14, tmFiber73StateAt 15]
    (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6] [tmFiber73StateAt 0]) (tmFiber73StateAt 6)
    tmFiber73State6_in_pass1_prefix

theorem tmFiber73State7_in_pass1_full :
    tmFiber73StateAt 7 ∈ chainClosureStep tmWord tmFiber73DirectStates [tmFiber73StateAt 0] := by
  rw [show tmFiber73DirectStates = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7] ++ [tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14, tmFiber73StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14, tmFiber73StateAt 15]
    (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7] [tmFiber73StateAt 0]) (tmFiber73StateAt 7)
    tmFiber73State7_in_pass1_prefix

theorem tmFiber73State8_in_pass1_full :
    tmFiber73StateAt 8 ∈ chainClosureStep tmWord tmFiber73DirectStates [tmFiber73StateAt 0] := by
  rw [show tmFiber73DirectStates = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8] ++ [tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14, tmFiber73StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14, tmFiber73StateAt 15]
    (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8] [tmFiber73StateAt 0]) (tmFiber73StateAt 8)
    tmFiber73State8_in_pass1_prefix

theorem tmFiber73State9_in_pass1_full :
    tmFiber73StateAt 9 ∈ chainClosureStep tmWord tmFiber73DirectStates [tmFiber73StateAt 0] := by
  rw [show tmFiber73DirectStates = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9] ++ [tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14, tmFiber73StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14, tmFiber73StateAt 15]
    (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9] [tmFiber73StateAt 0]) (tmFiber73StateAt 9)
    tmFiber73State9_in_pass1_prefix

theorem tmFiber73State10_in_pass1_full :
    tmFiber73StateAt 10 ∈ chainClosureStep tmWord tmFiber73DirectStates [tmFiber73StateAt 0] := by
  rw [show tmFiber73DirectStates = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10] ++ [tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14, tmFiber73StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14, tmFiber73StateAt 15]
    (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10] [tmFiber73StateAt 0]) (tmFiber73StateAt 10)
    tmFiber73State10_in_pass1_prefix

theorem tmFiber73State11_in_pass1_full :
    tmFiber73StateAt 11 ∈ chainClosureStep tmWord tmFiber73DirectStates [tmFiber73StateAt 0] := by
  rw [show tmFiber73DirectStates = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11] ++ [tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14, tmFiber73StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14, tmFiber73StateAt 15]
    (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11] [tmFiber73StateAt 0]) (tmFiber73StateAt 11)
    tmFiber73State11_in_pass1_prefix

theorem tmFiber73State12_in_pass1_full :
    tmFiber73StateAt 12 ∈ chainClosureStep tmWord tmFiber73DirectStates [tmFiber73StateAt 0] := by
  rw [show tmFiber73DirectStates = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12] ++ [tmFiber73StateAt 13, tmFiber73StateAt 14, tmFiber73StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber73StateAt 13, tmFiber73StateAt 14, tmFiber73StateAt 15]
    (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12] [tmFiber73StateAt 0]) (tmFiber73StateAt 12)
    tmFiber73State12_in_pass1_prefix

theorem tmFiber73State13_in_pass1_full :
    tmFiber73StateAt 13 ∈ chainClosureStep tmWord tmFiber73DirectStates [tmFiber73StateAt 0] := by
  rw [show tmFiber73DirectStates = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13] ++ [tmFiber73StateAt 14, tmFiber73StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber73StateAt 14, tmFiber73StateAt 15]
    (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13] [tmFiber73StateAt 0]) (tmFiber73StateAt 13)
    tmFiber73State13_in_pass1_prefix

theorem tmFiber73State14_in_pass1_full :
    tmFiber73StateAt 14 ∈ chainClosureStep tmWord tmFiber73DirectStates [tmFiber73StateAt 0] := by
  rw [show tmFiber73DirectStates = [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14] ++ [tmFiber73StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber73StateAt 15]
    (chainClosureStep tmWord [tmFiber73StateAt 0, tmFiber73StateAt 1, tmFiber73StateAt 2, tmFiber73StateAt 3, tmFiber73StateAt 4, tmFiber73StateAt 5, tmFiber73StateAt 6, tmFiber73StateAt 7, tmFiber73StateAt 8, tmFiber73StateAt 9, tmFiber73StateAt 10, tmFiber73StateAt 11, tmFiber73StateAt 12, tmFiber73StateAt 13, tmFiber73StateAt 14] [tmFiber73StateAt 0]) (tmFiber73StateAt 14)
    tmFiber73State14_in_pass1_prefix

theorem tmFiber73State15_in_pass1_full :
    tmFiber73StateAt 15 ∈ chainClosureStep tmWord tmFiber73DirectStates [tmFiber73StateAt 0] := by
  simpa [tmFiber73DirectStates] using tmFiber73State15_in_pass1_prefix

theorem tmFiber73State0_in_close :
    tmFiber73StateAt 0 ∈ closeChainFiber tmWord tmFiber73DirectStates tmFiber73DirectStates.length [tmFiber73StateAt 0] := by
  change tmFiber73StateAt 0 ∈ closeChainFiber tmWord tmFiber73DirectStates (15 + 1) [tmFiber73StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber73DirectStates 15 [tmFiber73StateAt 0] (tmFiber73StateAt 0) tmFiber73State0_in_pass1_full

theorem tmFiber73State1_in_close :
    tmFiber73StateAt 1 ∈ closeChainFiber tmWord tmFiber73DirectStates tmFiber73DirectStates.length [tmFiber73StateAt 0] := by
  change tmFiber73StateAt 1 ∈ closeChainFiber tmWord tmFiber73DirectStates (15 + 1) [tmFiber73StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber73DirectStates 15 [tmFiber73StateAt 0] (tmFiber73StateAt 1) tmFiber73State1_in_pass1_full

theorem tmFiber73State2_in_close :
    tmFiber73StateAt 2 ∈ closeChainFiber tmWord tmFiber73DirectStates tmFiber73DirectStates.length [tmFiber73StateAt 0] := by
  change tmFiber73StateAt 2 ∈ closeChainFiber tmWord tmFiber73DirectStates (15 + 1) [tmFiber73StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber73DirectStates 15 [tmFiber73StateAt 0] (tmFiber73StateAt 2) tmFiber73State2_in_pass1_full

theorem tmFiber73State3_in_close :
    tmFiber73StateAt 3 ∈ closeChainFiber tmWord tmFiber73DirectStates tmFiber73DirectStates.length [tmFiber73StateAt 0] := by
  change tmFiber73StateAt 3 ∈ closeChainFiber tmWord tmFiber73DirectStates (15 + 1) [tmFiber73StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber73DirectStates 15 [tmFiber73StateAt 0] (tmFiber73StateAt 3) tmFiber73State3_in_pass1_full

theorem tmFiber73State4_in_close :
    tmFiber73StateAt 4 ∈ closeChainFiber tmWord tmFiber73DirectStates tmFiber73DirectStates.length [tmFiber73StateAt 0] := by
  change tmFiber73StateAt 4 ∈ closeChainFiber tmWord tmFiber73DirectStates (15 + 1) [tmFiber73StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber73DirectStates 15 [tmFiber73StateAt 0] (tmFiber73StateAt 4) tmFiber73State4_in_pass1_full

theorem tmFiber73State5_in_close :
    tmFiber73StateAt 5 ∈ closeChainFiber tmWord tmFiber73DirectStates tmFiber73DirectStates.length [tmFiber73StateAt 0] := by
  change tmFiber73StateAt 5 ∈ closeChainFiber tmWord tmFiber73DirectStates (15 + 1) [tmFiber73StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber73DirectStates 15 [tmFiber73StateAt 0] (tmFiber73StateAt 5) tmFiber73State5_in_pass1_full

theorem tmFiber73State6_in_close :
    tmFiber73StateAt 6 ∈ closeChainFiber tmWord tmFiber73DirectStates tmFiber73DirectStates.length [tmFiber73StateAt 0] := by
  change tmFiber73StateAt 6 ∈ closeChainFiber tmWord tmFiber73DirectStates (15 + 1) [tmFiber73StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber73DirectStates 15 [tmFiber73StateAt 0] (tmFiber73StateAt 6) tmFiber73State6_in_pass1_full

theorem tmFiber73State7_in_close :
    tmFiber73StateAt 7 ∈ closeChainFiber tmWord tmFiber73DirectStates tmFiber73DirectStates.length [tmFiber73StateAt 0] := by
  change tmFiber73StateAt 7 ∈ closeChainFiber tmWord tmFiber73DirectStates (15 + 1) [tmFiber73StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber73DirectStates 15 [tmFiber73StateAt 0] (tmFiber73StateAt 7) tmFiber73State7_in_pass1_full

theorem tmFiber73State8_in_close :
    tmFiber73StateAt 8 ∈ closeChainFiber tmWord tmFiber73DirectStates tmFiber73DirectStates.length [tmFiber73StateAt 0] := by
  change tmFiber73StateAt 8 ∈ closeChainFiber tmWord tmFiber73DirectStates (15 + 1) [tmFiber73StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber73DirectStates 15 [tmFiber73StateAt 0] (tmFiber73StateAt 8) tmFiber73State8_in_pass1_full

theorem tmFiber73State9_in_close :
    tmFiber73StateAt 9 ∈ closeChainFiber tmWord tmFiber73DirectStates tmFiber73DirectStates.length [tmFiber73StateAt 0] := by
  change tmFiber73StateAt 9 ∈ closeChainFiber tmWord tmFiber73DirectStates (15 + 1) [tmFiber73StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber73DirectStates 15 [tmFiber73StateAt 0] (tmFiber73StateAt 9) tmFiber73State9_in_pass1_full

theorem tmFiber73State10_in_close :
    tmFiber73StateAt 10 ∈ closeChainFiber tmWord tmFiber73DirectStates tmFiber73DirectStates.length [tmFiber73StateAt 0] := by
  change tmFiber73StateAt 10 ∈ closeChainFiber tmWord tmFiber73DirectStates (15 + 1) [tmFiber73StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber73DirectStates 15 [tmFiber73StateAt 0] (tmFiber73StateAt 10) tmFiber73State10_in_pass1_full

theorem tmFiber73State11_in_close :
    tmFiber73StateAt 11 ∈ closeChainFiber tmWord tmFiber73DirectStates tmFiber73DirectStates.length [tmFiber73StateAt 0] := by
  change tmFiber73StateAt 11 ∈ closeChainFiber tmWord tmFiber73DirectStates (15 + 1) [tmFiber73StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber73DirectStates 15 [tmFiber73StateAt 0] (tmFiber73StateAt 11) tmFiber73State11_in_pass1_full

theorem tmFiber73State12_in_close :
    tmFiber73StateAt 12 ∈ closeChainFiber tmWord tmFiber73DirectStates tmFiber73DirectStates.length [tmFiber73StateAt 0] := by
  change tmFiber73StateAt 12 ∈ closeChainFiber tmWord tmFiber73DirectStates (15 + 1) [tmFiber73StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber73DirectStates 15 [tmFiber73StateAt 0] (tmFiber73StateAt 12) tmFiber73State12_in_pass1_full

theorem tmFiber73State13_in_close :
    tmFiber73StateAt 13 ∈ closeChainFiber tmWord tmFiber73DirectStates tmFiber73DirectStates.length [tmFiber73StateAt 0] := by
  change tmFiber73StateAt 13 ∈ closeChainFiber tmWord tmFiber73DirectStates (15 + 1) [tmFiber73StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber73DirectStates 15 [tmFiber73StateAt 0] (tmFiber73StateAt 13) tmFiber73State13_in_pass1_full

theorem tmFiber73State14_in_close :
    tmFiber73StateAt 14 ∈ closeChainFiber tmWord tmFiber73DirectStates tmFiber73DirectStates.length [tmFiber73StateAt 0] := by
  change tmFiber73StateAt 14 ∈ closeChainFiber tmWord tmFiber73DirectStates (15 + 1) [tmFiber73StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber73DirectStates 15 [tmFiber73StateAt 0] (tmFiber73StateAt 14) tmFiber73State14_in_pass1_full

theorem tmFiber73State15_in_close :
    tmFiber73StateAt 15 ∈ closeChainFiber tmWord tmFiber73DirectStates tmFiber73DirectStates.length [tmFiber73StateAt 0] := by
  change tmFiber73StateAt 15 ∈ closeChainFiber tmWord tmFiber73DirectStates (15 + 1) [tmFiber73StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber73DirectStates 15 [tmFiber73StateAt 0] (tmFiber73StateAt 15) tmFiber73State15_in_pass1_full

theorem tmFiber73DirectConnected :
    chainFiberConnected tmWord tmFiber73DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber73DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber73State0_in_close
  · subst state
    exact tmFiber73State1_in_close
  · subst state
    exact tmFiber73State2_in_close
  · subst state
    exact tmFiber73State3_in_close
  · subst state
    exact tmFiber73State4_in_close
  · subst state
    exact tmFiber73State5_in_close
  · subst state
    exact tmFiber73State6_in_close
  · subst state
    exact tmFiber73State7_in_close
  · subst state
    exact tmFiber73State8_in_close
  · subst state
    exact tmFiber73State9_in_close
  · subst state
    exact tmFiber73State10_in_close
  · subst state
    exact tmFiber73State11_in_close
  · subst state
    exact tmFiber73State12_in_close
  · subst state
    exact tmFiber73State13_in_close
  · subst state
    exact tmFiber73State14_in_close
  · subst state
    exact tmFiber73State15_in_close
  · cases h

def tmFiber74StateAt (i : Nat) : List TauState :=
  directStates (tmFiber74RowAt i).sourceLeft (tmFiber74RowAt i).sourceRight

def tmFiber74DirectStates : List (List TauState) :=
  [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14, tmFiber74StateAt 15]

theorem tmFiber74ReverseRow_1_ok :
    tmRowReverseValid tmFiber74Key tmFiber74Expected (tmFiber74RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber74Chunk0_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber74Chunk0] at h
  exact h.2

theorem tmFiber74ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber74StateAt 0) (tmFiber74StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber74StateAt 0) (tmFiber74StateAt 1)
    (tmFiber74RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber74Key tmFiber74Expected
        (tmFiber74RowAt 1) (by decide) tmFiber74ReverseRow_1_ok
      simpa [tmFiber74StateAt, tmFiber74RowAt, tmFiber74Rows, listGetD, directRow] using h)

theorem tmFiber74ReverseRow_2_ok :
    tmRowReverseValid tmFiber74Key tmFiber74Expected (tmFiber74RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber74Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber74Chunk1] at h
  exact h.1

theorem tmFiber74ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber74StateAt 0) (tmFiber74StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber74StateAt 0) (tmFiber74StateAt 2)
    (tmFiber74RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber74Key tmFiber74Expected
        (tmFiber74RowAt 2) (by decide) tmFiber74ReverseRow_2_ok
      simpa [tmFiber74StateAt, tmFiber74RowAt, tmFiber74Rows, listGetD, directRow] using h)

theorem tmFiber74ReverseRow_3_ok :
    tmRowReverseValid tmFiber74Key tmFiber74Expected (tmFiber74RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber74Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber74Chunk1] at h
  exact h.2

theorem tmFiber74ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber74StateAt 1) (tmFiber74StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber74StateAt 1) (tmFiber74StateAt 3)
    (tmFiber74RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber74Key tmFiber74Expected
        (tmFiber74RowAt 3) (by decide) tmFiber74ReverseRow_3_ok
      simpa [tmFiber74StateAt, tmFiber74RowAt, tmFiber74Rows, listGetD, directRow] using h)

theorem tmFiber74ReverseRow_4_ok :
    tmRowReverseValid tmFiber74Key tmFiber74Expected (tmFiber74RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber74Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber74Chunk2] at h
  exact h.1

theorem tmFiber74ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber74StateAt 0) (tmFiber74StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber74StateAt 0) (tmFiber74StateAt 4)
    (tmFiber74RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber74Key tmFiber74Expected
        (tmFiber74RowAt 4) (by decide) tmFiber74ReverseRow_4_ok
      simpa [tmFiber74StateAt, tmFiber74RowAt, tmFiber74Rows, listGetD, directRow] using h)

theorem tmFiber74ReverseRow_5_ok :
    tmRowReverseValid tmFiber74Key tmFiber74Expected (tmFiber74RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber74Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber74Chunk2] at h
  exact h.2

theorem tmFiber74ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber74StateAt 1) (tmFiber74StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber74StateAt 1) (tmFiber74StateAt 5)
    (tmFiber74RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber74Key tmFiber74Expected
        (tmFiber74RowAt 5) (by decide) tmFiber74ReverseRow_5_ok
      simpa [tmFiber74StateAt, tmFiber74RowAt, tmFiber74Rows, listGetD, directRow] using h)

theorem tmFiber74ReverseRow_6_ok :
    tmRowReverseValid tmFiber74Key tmFiber74Expected (tmFiber74RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber74Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber74Chunk3] at h
  exact h.1

theorem tmFiber74ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber74StateAt 2) (tmFiber74StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber74StateAt 2) (tmFiber74StateAt 6)
    (tmFiber74RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber74Key tmFiber74Expected
        (tmFiber74RowAt 6) (by decide) tmFiber74ReverseRow_6_ok
      simpa [tmFiber74StateAt, tmFiber74RowAt, tmFiber74Rows, listGetD, directRow] using h)

theorem tmFiber74ReverseRow_7_ok :
    tmRowReverseValid tmFiber74Key tmFiber74Expected (tmFiber74RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber74Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber74Chunk3] at h
  exact h.2

theorem tmFiber74ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber74StateAt 3) (tmFiber74StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber74StateAt 3) (tmFiber74StateAt 7)
    (tmFiber74RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber74Key tmFiber74Expected
        (tmFiber74RowAt 7) (by decide) tmFiber74ReverseRow_7_ok
      simpa [tmFiber74StateAt, tmFiber74RowAt, tmFiber74Rows, listGetD, directRow] using h)

theorem tmFiber74ReverseRow_8_ok :
    tmRowReverseValid tmFiber74Key tmFiber74Expected (tmFiber74RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber74Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber74Chunk4] at h
  exact h.1

theorem tmFiber74ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber74StateAt 0) (tmFiber74StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber74StateAt 0) (tmFiber74StateAt 8)
    (tmFiber74RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber74Key tmFiber74Expected
        (tmFiber74RowAt 8) (by decide) tmFiber74ReverseRow_8_ok
      simpa [tmFiber74StateAt, tmFiber74RowAt, tmFiber74Rows, listGetD, directRow] using h)

theorem tmFiber74ReverseRow_9_ok :
    tmRowReverseValid tmFiber74Key tmFiber74Expected (tmFiber74RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber74Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber74Chunk4] at h
  exact h.2

theorem tmFiber74ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber74StateAt 1) (tmFiber74StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber74StateAt 1) (tmFiber74StateAt 9)
    (tmFiber74RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber74Key tmFiber74Expected
        (tmFiber74RowAt 9) (by decide) tmFiber74ReverseRow_9_ok
      simpa [tmFiber74StateAt, tmFiber74RowAt, tmFiber74Rows, listGetD, directRow] using h)

theorem tmFiber74ReverseRow_10_ok :
    tmRowReverseValid tmFiber74Key tmFiber74Expected (tmFiber74RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber74Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber74Chunk5] at h
  exact h.1

theorem tmFiber74ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber74StateAt 2) (tmFiber74StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber74StateAt 2) (tmFiber74StateAt 10)
    (tmFiber74RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber74Key tmFiber74Expected
        (tmFiber74RowAt 10) (by decide) tmFiber74ReverseRow_10_ok
      simpa [tmFiber74StateAt, tmFiber74RowAt, tmFiber74Rows, listGetD, directRow] using h)

theorem tmFiber74ReverseRow_11_ok :
    tmRowReverseValid tmFiber74Key tmFiber74Expected (tmFiber74RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber74Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber74Chunk5] at h
  exact h.2

theorem tmFiber74ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber74StateAt 3) (tmFiber74StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber74StateAt 3) (tmFiber74StateAt 11)
    (tmFiber74RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber74Key tmFiber74Expected
        (tmFiber74RowAt 11) (by decide) tmFiber74ReverseRow_11_ok
      simpa [tmFiber74StateAt, tmFiber74RowAt, tmFiber74Rows, listGetD, directRow] using h)

theorem tmFiber74ReverseRow_12_ok :
    tmRowReverseValid tmFiber74Key tmFiber74Expected (tmFiber74RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber74Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber74Chunk6] at h
  exact h.1

theorem tmFiber74ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber74StateAt 4) (tmFiber74StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber74StateAt 4) (tmFiber74StateAt 12)
    (tmFiber74RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber74Key tmFiber74Expected
        (tmFiber74RowAt 12) (by decide) tmFiber74ReverseRow_12_ok
      simpa [tmFiber74StateAt, tmFiber74RowAt, tmFiber74Rows, listGetD, directRow] using h)

theorem tmFiber74ReverseRow_13_ok :
    tmRowReverseValid tmFiber74Key tmFiber74Expected (tmFiber74RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber74Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber74Chunk6] at h
  exact h.2

theorem tmFiber74ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber74StateAt 5) (tmFiber74StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber74StateAt 5) (tmFiber74StateAt 13)
    (tmFiber74RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber74Key tmFiber74Expected
        (tmFiber74RowAt 13) (by decide) tmFiber74ReverseRow_13_ok
      simpa [tmFiber74StateAt, tmFiber74RowAt, tmFiber74Rows, listGetD, directRow] using h)

theorem tmFiber74ReverseRow_14_ok :
    tmRowReverseValid tmFiber74Key tmFiber74Expected (tmFiber74RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber74Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber74Chunk7] at h
  exact h.1

theorem tmFiber74ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber74StateAt 6) (tmFiber74StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber74StateAt 6) (tmFiber74StateAt 14)
    (tmFiber74RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber74Key tmFiber74Expected
        (tmFiber74RowAt 14) (by decide) tmFiber74ReverseRow_14_ok
      simpa [tmFiber74StateAt, tmFiber74RowAt, tmFiber74Rows, listGetD, directRow] using h)

theorem tmFiber74ReverseRow_15_ok :
    tmRowReverseValid tmFiber74Key tmFiber74Expected (tmFiber74RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber74Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber74Chunk7] at h
  exact h.2

theorem tmFiber74ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber74StateAt 7) (tmFiber74StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber74StateAt 7) (tmFiber74StateAt 15)
    (tmFiber74RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber74Key tmFiber74Expected
        (tmFiber74RowAt 15) (by decide) tmFiber74ReverseRow_15_ok
      simpa [tmFiber74StateAt, tmFiber74RowAt, tmFiber74Rows, listGetD, directRow] using h)

theorem tmFiber74State0_in_pass1_prefix :
    tmFiber74StateAt 0 ∈ chainClosureStep tmWord [tmFiber74StateAt 0] [tmFiber74StateAt 0] := by
  exact chainClosureStep_mem_of_seen tmWord [tmFiber74StateAt 0] [tmFiber74StateAt 0] (tmFiber74StateAt 0) (by simp)

theorem tmFiber74State1_in_pass1_prefix :
    tmFiber74StateAt 1 ∈ chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1] [tmFiber74StateAt 0] := by
  have hparentBefore :
      tmFiber74StateAt 0 ∈ chainClosureStep tmWord [tmFiber74StateAt 0] [tmFiber74StateAt 0] := by
    exact tmFiber74State0_in_pass1_prefix
  rw [show [tmFiber74StateAt 0, tmFiber74StateAt 1] = [tmFiber74StateAt 0] ++ [tmFiber74StateAt 1] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber74StateAt 1) []
    (chainClosureStep tmWord [tmFiber74StateAt 0] [tmFiber74StateAt 0]) (tmFiber74StateAt 0)
    hparentBefore tmFiber74ReverseSingleStep1

theorem tmFiber74State2_in_pass1_prefix :
    tmFiber74StateAt 2 ∈ chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2] [tmFiber74StateAt 0] := by
  have hparentBefore :
      tmFiber74StateAt 0 ∈ chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1] [tmFiber74StateAt 0] := by
    rw [show [tmFiber74StateAt 0, tmFiber74StateAt 1] = [tmFiber74StateAt 0] ++ [tmFiber74StateAt 1] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber74StateAt 1]
      (chainClosureStep tmWord [tmFiber74StateAt 0] [tmFiber74StateAt 0]) (tmFiber74StateAt 0)
      tmFiber74State0_in_pass1_prefix
  rw [show [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2] = [tmFiber74StateAt 0, tmFiber74StateAt 1] ++ [tmFiber74StateAt 2] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber74StateAt 2) []
    (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1] [tmFiber74StateAt 0]) (tmFiber74StateAt 0)
    hparentBefore tmFiber74ReverseSingleStep2

theorem tmFiber74State3_in_pass1_prefix :
    tmFiber74StateAt 3 ∈ chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3] [tmFiber74StateAt 0] := by
  have hparentBefore :
      tmFiber74StateAt 1 ∈ chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2] [tmFiber74StateAt 0] := by
    rw [show [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2] = [tmFiber74StateAt 0, tmFiber74StateAt 1] ++ [tmFiber74StateAt 2] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber74StateAt 2]
      (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1] [tmFiber74StateAt 0]) (tmFiber74StateAt 1)
      tmFiber74State1_in_pass1_prefix
  rw [show [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3] = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2] ++ [tmFiber74StateAt 3] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber74StateAt 3) []
    (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2] [tmFiber74StateAt 0]) (tmFiber74StateAt 1)
    hparentBefore tmFiber74ReverseSingleStep3

theorem tmFiber74State4_in_pass1_prefix :
    tmFiber74StateAt 4 ∈ chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4] [tmFiber74StateAt 0] := by
  have hparentBefore :
      tmFiber74StateAt 0 ∈ chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3] [tmFiber74StateAt 0] := by
    rw [show [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3] = [tmFiber74StateAt 0] ++ [tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3]
      (chainClosureStep tmWord [tmFiber74StateAt 0] [tmFiber74StateAt 0]) (tmFiber74StateAt 0)
      tmFiber74State0_in_pass1_prefix
  rw [show [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4] = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3] ++ [tmFiber74StateAt 4] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber74StateAt 4) []
    (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3] [tmFiber74StateAt 0]) (tmFiber74StateAt 0)
    hparentBefore tmFiber74ReverseSingleStep4

theorem tmFiber74State5_in_pass1_prefix :
    tmFiber74StateAt 5 ∈ chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5] [tmFiber74StateAt 0] := by
  have hparentBefore :
      tmFiber74StateAt 1 ∈ chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4] [tmFiber74StateAt 0] := by
    rw [show [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4] = [tmFiber74StateAt 0, tmFiber74StateAt 1] ++ [tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4]
      (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1] [tmFiber74StateAt 0]) (tmFiber74StateAt 1)
      tmFiber74State1_in_pass1_prefix
  rw [show [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5] = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4] ++ [tmFiber74StateAt 5] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber74StateAt 5) []
    (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4] [tmFiber74StateAt 0]) (tmFiber74StateAt 1)
    hparentBefore tmFiber74ReverseSingleStep5

theorem tmFiber74State6_in_pass1_prefix :
    tmFiber74StateAt 6 ∈ chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6] [tmFiber74StateAt 0] := by
  have hparentBefore :
      tmFiber74StateAt 2 ∈ chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5] [tmFiber74StateAt 0] := by
    rw [show [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5] = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2] ++ [tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5]
      (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2] [tmFiber74StateAt 0]) (tmFiber74StateAt 2)
      tmFiber74State2_in_pass1_prefix
  rw [show [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6] = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5] ++ [tmFiber74StateAt 6] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber74StateAt 6) []
    (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5] [tmFiber74StateAt 0]) (tmFiber74StateAt 2)
    hparentBefore tmFiber74ReverseSingleStep6

theorem tmFiber74State7_in_pass1_prefix :
    tmFiber74StateAt 7 ∈ chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7] [tmFiber74StateAt 0] := by
  have hparentBefore :
      tmFiber74StateAt 3 ∈ chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6] [tmFiber74StateAt 0] := by
    rw [show [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6] = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3] ++ [tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6]
      (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3] [tmFiber74StateAt 0]) (tmFiber74StateAt 3)
      tmFiber74State3_in_pass1_prefix
  rw [show [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7] = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6] ++ [tmFiber74StateAt 7] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber74StateAt 7) []
    (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6] [tmFiber74StateAt 0]) (tmFiber74StateAt 3)
    hparentBefore tmFiber74ReverseSingleStep7

theorem tmFiber74State8_in_pass1_prefix :
    tmFiber74StateAt 8 ∈ chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8] [tmFiber74StateAt 0] := by
  have hparentBefore :
      tmFiber74StateAt 0 ∈ chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7] [tmFiber74StateAt 0] := by
    rw [show [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7] = [tmFiber74StateAt 0] ++ [tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7]
      (chainClosureStep tmWord [tmFiber74StateAt 0] [tmFiber74StateAt 0]) (tmFiber74StateAt 0)
      tmFiber74State0_in_pass1_prefix
  rw [show [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8] = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7] ++ [tmFiber74StateAt 8] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber74StateAt 8) []
    (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7] [tmFiber74StateAt 0]) (tmFiber74StateAt 0)
    hparentBefore tmFiber74ReverseSingleStep8

theorem tmFiber74State9_in_pass1_prefix :
    tmFiber74StateAt 9 ∈ chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9] [tmFiber74StateAt 0] := by
  have hparentBefore :
      tmFiber74StateAt 1 ∈ chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8] [tmFiber74StateAt 0] := by
    rw [show [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8] = [tmFiber74StateAt 0, tmFiber74StateAt 1] ++ [tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8]
      (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1] [tmFiber74StateAt 0]) (tmFiber74StateAt 1)
      tmFiber74State1_in_pass1_prefix
  rw [show [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9] = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8] ++ [tmFiber74StateAt 9] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber74StateAt 9) []
    (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8] [tmFiber74StateAt 0]) (tmFiber74StateAt 1)
    hparentBefore tmFiber74ReverseSingleStep9

theorem tmFiber74State10_in_pass1_prefix :
    tmFiber74StateAt 10 ∈ chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10] [tmFiber74StateAt 0] := by
  have hparentBefore :
      tmFiber74StateAt 2 ∈ chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9] [tmFiber74StateAt 0] := by
    rw [show [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9] = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2] ++ [tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9]
      (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2] [tmFiber74StateAt 0]) (tmFiber74StateAt 2)
      tmFiber74State2_in_pass1_prefix
  rw [show [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10] = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9] ++ [tmFiber74StateAt 10] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber74StateAt 10) []
    (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9] [tmFiber74StateAt 0]) (tmFiber74StateAt 2)
    hparentBefore tmFiber74ReverseSingleStep10

theorem tmFiber74State11_in_pass1_prefix :
    tmFiber74StateAt 11 ∈ chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11] [tmFiber74StateAt 0] := by
  have hparentBefore :
      tmFiber74StateAt 3 ∈ chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10] [tmFiber74StateAt 0] := by
    rw [show [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10] = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3] ++ [tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10]
      (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3] [tmFiber74StateAt 0]) (tmFiber74StateAt 3)
      tmFiber74State3_in_pass1_prefix
  rw [show [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11] = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10] ++ [tmFiber74StateAt 11] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber74StateAt 11) []
    (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10] [tmFiber74StateAt 0]) (tmFiber74StateAt 3)
    hparentBefore tmFiber74ReverseSingleStep11

theorem tmFiber74State12_in_pass1_prefix :
    tmFiber74StateAt 12 ∈ chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12] [tmFiber74StateAt 0] := by
  have hparentBefore :
      tmFiber74StateAt 4 ∈ chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11] [tmFiber74StateAt 0] := by
    rw [show [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11] = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4] ++ [tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11]
      (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4] [tmFiber74StateAt 0]) (tmFiber74StateAt 4)
      tmFiber74State4_in_pass1_prefix
  rw [show [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12] = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11] ++ [tmFiber74StateAt 12] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber74StateAt 12) []
    (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11] [tmFiber74StateAt 0]) (tmFiber74StateAt 4)
    hparentBefore tmFiber74ReverseSingleStep12

theorem tmFiber74State13_in_pass1_prefix :
    tmFiber74StateAt 13 ∈ chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13] [tmFiber74StateAt 0] := by
  have hparentBefore :
      tmFiber74StateAt 5 ∈ chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12] [tmFiber74StateAt 0] := by
    rw [show [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12] = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5] ++ [tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12]
      (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5] [tmFiber74StateAt 0]) (tmFiber74StateAt 5)
      tmFiber74State5_in_pass1_prefix
  rw [show [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13] = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12] ++ [tmFiber74StateAt 13] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber74StateAt 13) []
    (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12] [tmFiber74StateAt 0]) (tmFiber74StateAt 5)
    hparentBefore tmFiber74ReverseSingleStep13

theorem tmFiber74State14_in_pass1_prefix :
    tmFiber74StateAt 14 ∈ chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14] [tmFiber74StateAt 0] := by
  have hparentBefore :
      tmFiber74StateAt 6 ∈ chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13] [tmFiber74StateAt 0] := by
    rw [show [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13] = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6] ++ [tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13]
      (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6] [tmFiber74StateAt 0]) (tmFiber74StateAt 6)
      tmFiber74State6_in_pass1_prefix
  rw [show [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14] = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13] ++ [tmFiber74StateAt 14] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber74StateAt 14) []
    (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13] [tmFiber74StateAt 0]) (tmFiber74StateAt 6)
    hparentBefore tmFiber74ReverseSingleStep14

theorem tmFiber74State15_in_pass1_prefix :
    tmFiber74StateAt 15 ∈ chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14, tmFiber74StateAt 15] [tmFiber74StateAt 0] := by
  have hparentBefore :
      tmFiber74StateAt 7 ∈ chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14] [tmFiber74StateAt 0] := by
    rw [show [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14] = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7] ++ [tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14]
      (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7] [tmFiber74StateAt 0]) (tmFiber74StateAt 7)
      tmFiber74State7_in_pass1_prefix
  rw [show [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14, tmFiber74StateAt 15] = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14] ++ [tmFiber74StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber74StateAt 15) []
    (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14] [tmFiber74StateAt 0]) (tmFiber74StateAt 7)
    hparentBefore tmFiber74ReverseSingleStep15

theorem tmFiber74State0_in_pass1_full :
    tmFiber74StateAt 0 ∈ chainClosureStep tmWord tmFiber74DirectStates [tmFiber74StateAt 0] := by
  rw [show tmFiber74DirectStates = [tmFiber74StateAt 0] ++ [tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14, tmFiber74StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14, tmFiber74StateAt 15]
    (chainClosureStep tmWord [tmFiber74StateAt 0] [tmFiber74StateAt 0]) (tmFiber74StateAt 0)
    tmFiber74State0_in_pass1_prefix

theorem tmFiber74State1_in_pass1_full :
    tmFiber74StateAt 1 ∈ chainClosureStep tmWord tmFiber74DirectStates [tmFiber74StateAt 0] := by
  rw [show tmFiber74DirectStates = [tmFiber74StateAt 0, tmFiber74StateAt 1] ++ [tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14, tmFiber74StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14, tmFiber74StateAt 15]
    (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1] [tmFiber74StateAt 0]) (tmFiber74StateAt 1)
    tmFiber74State1_in_pass1_prefix

theorem tmFiber74State2_in_pass1_full :
    tmFiber74StateAt 2 ∈ chainClosureStep tmWord tmFiber74DirectStates [tmFiber74StateAt 0] := by
  rw [show tmFiber74DirectStates = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2] ++ [tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14, tmFiber74StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14, tmFiber74StateAt 15]
    (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2] [tmFiber74StateAt 0]) (tmFiber74StateAt 2)
    tmFiber74State2_in_pass1_prefix

theorem tmFiber74State3_in_pass1_full :
    tmFiber74StateAt 3 ∈ chainClosureStep tmWord tmFiber74DirectStates [tmFiber74StateAt 0] := by
  rw [show tmFiber74DirectStates = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3] ++ [tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14, tmFiber74StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14, tmFiber74StateAt 15]
    (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3] [tmFiber74StateAt 0]) (tmFiber74StateAt 3)
    tmFiber74State3_in_pass1_prefix

theorem tmFiber74State4_in_pass1_full :
    tmFiber74StateAt 4 ∈ chainClosureStep tmWord tmFiber74DirectStates [tmFiber74StateAt 0] := by
  rw [show tmFiber74DirectStates = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4] ++ [tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14, tmFiber74StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14, tmFiber74StateAt 15]
    (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4] [tmFiber74StateAt 0]) (tmFiber74StateAt 4)
    tmFiber74State4_in_pass1_prefix

theorem tmFiber74State5_in_pass1_full :
    tmFiber74StateAt 5 ∈ chainClosureStep tmWord tmFiber74DirectStates [tmFiber74StateAt 0] := by
  rw [show tmFiber74DirectStates = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5] ++ [tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14, tmFiber74StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14, tmFiber74StateAt 15]
    (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5] [tmFiber74StateAt 0]) (tmFiber74StateAt 5)
    tmFiber74State5_in_pass1_prefix

theorem tmFiber74State6_in_pass1_full :
    tmFiber74StateAt 6 ∈ chainClosureStep tmWord tmFiber74DirectStates [tmFiber74StateAt 0] := by
  rw [show tmFiber74DirectStates = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6] ++ [tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14, tmFiber74StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14, tmFiber74StateAt 15]
    (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6] [tmFiber74StateAt 0]) (tmFiber74StateAt 6)
    tmFiber74State6_in_pass1_prefix

theorem tmFiber74State7_in_pass1_full :
    tmFiber74StateAt 7 ∈ chainClosureStep tmWord tmFiber74DirectStates [tmFiber74StateAt 0] := by
  rw [show tmFiber74DirectStates = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7] ++ [tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14, tmFiber74StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14, tmFiber74StateAt 15]
    (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7] [tmFiber74StateAt 0]) (tmFiber74StateAt 7)
    tmFiber74State7_in_pass1_prefix

theorem tmFiber74State8_in_pass1_full :
    tmFiber74StateAt 8 ∈ chainClosureStep tmWord tmFiber74DirectStates [tmFiber74StateAt 0] := by
  rw [show tmFiber74DirectStates = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8] ++ [tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14, tmFiber74StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14, tmFiber74StateAt 15]
    (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8] [tmFiber74StateAt 0]) (tmFiber74StateAt 8)
    tmFiber74State8_in_pass1_prefix

theorem tmFiber74State9_in_pass1_full :
    tmFiber74StateAt 9 ∈ chainClosureStep tmWord tmFiber74DirectStates [tmFiber74StateAt 0] := by
  rw [show tmFiber74DirectStates = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9] ++ [tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14, tmFiber74StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14, tmFiber74StateAt 15]
    (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9] [tmFiber74StateAt 0]) (tmFiber74StateAt 9)
    tmFiber74State9_in_pass1_prefix

theorem tmFiber74State10_in_pass1_full :
    tmFiber74StateAt 10 ∈ chainClosureStep tmWord tmFiber74DirectStates [tmFiber74StateAt 0] := by
  rw [show tmFiber74DirectStates = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10] ++ [tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14, tmFiber74StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14, tmFiber74StateAt 15]
    (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10] [tmFiber74StateAt 0]) (tmFiber74StateAt 10)
    tmFiber74State10_in_pass1_prefix

theorem tmFiber74State11_in_pass1_full :
    tmFiber74StateAt 11 ∈ chainClosureStep tmWord tmFiber74DirectStates [tmFiber74StateAt 0] := by
  rw [show tmFiber74DirectStates = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11] ++ [tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14, tmFiber74StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14, tmFiber74StateAt 15]
    (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11] [tmFiber74StateAt 0]) (tmFiber74StateAt 11)
    tmFiber74State11_in_pass1_prefix

theorem tmFiber74State12_in_pass1_full :
    tmFiber74StateAt 12 ∈ chainClosureStep tmWord tmFiber74DirectStates [tmFiber74StateAt 0] := by
  rw [show tmFiber74DirectStates = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12] ++ [tmFiber74StateAt 13, tmFiber74StateAt 14, tmFiber74StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber74StateAt 13, tmFiber74StateAt 14, tmFiber74StateAt 15]
    (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12] [tmFiber74StateAt 0]) (tmFiber74StateAt 12)
    tmFiber74State12_in_pass1_prefix

theorem tmFiber74State13_in_pass1_full :
    tmFiber74StateAt 13 ∈ chainClosureStep tmWord tmFiber74DirectStates [tmFiber74StateAt 0] := by
  rw [show tmFiber74DirectStates = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13] ++ [tmFiber74StateAt 14, tmFiber74StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber74StateAt 14, tmFiber74StateAt 15]
    (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13] [tmFiber74StateAt 0]) (tmFiber74StateAt 13)
    tmFiber74State13_in_pass1_prefix

theorem tmFiber74State14_in_pass1_full :
    tmFiber74StateAt 14 ∈ chainClosureStep tmWord tmFiber74DirectStates [tmFiber74StateAt 0] := by
  rw [show tmFiber74DirectStates = [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14] ++ [tmFiber74StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber74StateAt 15]
    (chainClosureStep tmWord [tmFiber74StateAt 0, tmFiber74StateAt 1, tmFiber74StateAt 2, tmFiber74StateAt 3, tmFiber74StateAt 4, tmFiber74StateAt 5, tmFiber74StateAt 6, tmFiber74StateAt 7, tmFiber74StateAt 8, tmFiber74StateAt 9, tmFiber74StateAt 10, tmFiber74StateAt 11, tmFiber74StateAt 12, tmFiber74StateAt 13, tmFiber74StateAt 14] [tmFiber74StateAt 0]) (tmFiber74StateAt 14)
    tmFiber74State14_in_pass1_prefix

theorem tmFiber74State15_in_pass1_full :
    tmFiber74StateAt 15 ∈ chainClosureStep tmWord tmFiber74DirectStates [tmFiber74StateAt 0] := by
  simpa [tmFiber74DirectStates] using tmFiber74State15_in_pass1_prefix

theorem tmFiber74State0_in_close :
    tmFiber74StateAt 0 ∈ closeChainFiber tmWord tmFiber74DirectStates tmFiber74DirectStates.length [tmFiber74StateAt 0] := by
  change tmFiber74StateAt 0 ∈ closeChainFiber tmWord tmFiber74DirectStates (15 + 1) [tmFiber74StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber74DirectStates 15 [tmFiber74StateAt 0] (tmFiber74StateAt 0) tmFiber74State0_in_pass1_full

theorem tmFiber74State1_in_close :
    tmFiber74StateAt 1 ∈ closeChainFiber tmWord tmFiber74DirectStates tmFiber74DirectStates.length [tmFiber74StateAt 0] := by
  change tmFiber74StateAt 1 ∈ closeChainFiber tmWord tmFiber74DirectStates (15 + 1) [tmFiber74StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber74DirectStates 15 [tmFiber74StateAt 0] (tmFiber74StateAt 1) tmFiber74State1_in_pass1_full

theorem tmFiber74State2_in_close :
    tmFiber74StateAt 2 ∈ closeChainFiber tmWord tmFiber74DirectStates tmFiber74DirectStates.length [tmFiber74StateAt 0] := by
  change tmFiber74StateAt 2 ∈ closeChainFiber tmWord tmFiber74DirectStates (15 + 1) [tmFiber74StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber74DirectStates 15 [tmFiber74StateAt 0] (tmFiber74StateAt 2) tmFiber74State2_in_pass1_full

theorem tmFiber74State3_in_close :
    tmFiber74StateAt 3 ∈ closeChainFiber tmWord tmFiber74DirectStates tmFiber74DirectStates.length [tmFiber74StateAt 0] := by
  change tmFiber74StateAt 3 ∈ closeChainFiber tmWord tmFiber74DirectStates (15 + 1) [tmFiber74StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber74DirectStates 15 [tmFiber74StateAt 0] (tmFiber74StateAt 3) tmFiber74State3_in_pass1_full

theorem tmFiber74State4_in_close :
    tmFiber74StateAt 4 ∈ closeChainFiber tmWord tmFiber74DirectStates tmFiber74DirectStates.length [tmFiber74StateAt 0] := by
  change tmFiber74StateAt 4 ∈ closeChainFiber tmWord tmFiber74DirectStates (15 + 1) [tmFiber74StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber74DirectStates 15 [tmFiber74StateAt 0] (tmFiber74StateAt 4) tmFiber74State4_in_pass1_full

theorem tmFiber74State5_in_close :
    tmFiber74StateAt 5 ∈ closeChainFiber tmWord tmFiber74DirectStates tmFiber74DirectStates.length [tmFiber74StateAt 0] := by
  change tmFiber74StateAt 5 ∈ closeChainFiber tmWord tmFiber74DirectStates (15 + 1) [tmFiber74StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber74DirectStates 15 [tmFiber74StateAt 0] (tmFiber74StateAt 5) tmFiber74State5_in_pass1_full

theorem tmFiber74State6_in_close :
    tmFiber74StateAt 6 ∈ closeChainFiber tmWord tmFiber74DirectStates tmFiber74DirectStates.length [tmFiber74StateAt 0] := by
  change tmFiber74StateAt 6 ∈ closeChainFiber tmWord tmFiber74DirectStates (15 + 1) [tmFiber74StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber74DirectStates 15 [tmFiber74StateAt 0] (tmFiber74StateAt 6) tmFiber74State6_in_pass1_full

theorem tmFiber74State7_in_close :
    tmFiber74StateAt 7 ∈ closeChainFiber tmWord tmFiber74DirectStates tmFiber74DirectStates.length [tmFiber74StateAt 0] := by
  change tmFiber74StateAt 7 ∈ closeChainFiber tmWord tmFiber74DirectStates (15 + 1) [tmFiber74StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber74DirectStates 15 [tmFiber74StateAt 0] (tmFiber74StateAt 7) tmFiber74State7_in_pass1_full

theorem tmFiber74State8_in_close :
    tmFiber74StateAt 8 ∈ closeChainFiber tmWord tmFiber74DirectStates tmFiber74DirectStates.length [tmFiber74StateAt 0] := by
  change tmFiber74StateAt 8 ∈ closeChainFiber tmWord tmFiber74DirectStates (15 + 1) [tmFiber74StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber74DirectStates 15 [tmFiber74StateAt 0] (tmFiber74StateAt 8) tmFiber74State8_in_pass1_full

theorem tmFiber74State9_in_close :
    tmFiber74StateAt 9 ∈ closeChainFiber tmWord tmFiber74DirectStates tmFiber74DirectStates.length [tmFiber74StateAt 0] := by
  change tmFiber74StateAt 9 ∈ closeChainFiber tmWord tmFiber74DirectStates (15 + 1) [tmFiber74StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber74DirectStates 15 [tmFiber74StateAt 0] (tmFiber74StateAt 9) tmFiber74State9_in_pass1_full

theorem tmFiber74State10_in_close :
    tmFiber74StateAt 10 ∈ closeChainFiber tmWord tmFiber74DirectStates tmFiber74DirectStates.length [tmFiber74StateAt 0] := by
  change tmFiber74StateAt 10 ∈ closeChainFiber tmWord tmFiber74DirectStates (15 + 1) [tmFiber74StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber74DirectStates 15 [tmFiber74StateAt 0] (tmFiber74StateAt 10) tmFiber74State10_in_pass1_full

theorem tmFiber74State11_in_close :
    tmFiber74StateAt 11 ∈ closeChainFiber tmWord tmFiber74DirectStates tmFiber74DirectStates.length [tmFiber74StateAt 0] := by
  change tmFiber74StateAt 11 ∈ closeChainFiber tmWord tmFiber74DirectStates (15 + 1) [tmFiber74StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber74DirectStates 15 [tmFiber74StateAt 0] (tmFiber74StateAt 11) tmFiber74State11_in_pass1_full

theorem tmFiber74State12_in_close :
    tmFiber74StateAt 12 ∈ closeChainFiber tmWord tmFiber74DirectStates tmFiber74DirectStates.length [tmFiber74StateAt 0] := by
  change tmFiber74StateAt 12 ∈ closeChainFiber tmWord tmFiber74DirectStates (15 + 1) [tmFiber74StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber74DirectStates 15 [tmFiber74StateAt 0] (tmFiber74StateAt 12) tmFiber74State12_in_pass1_full

theorem tmFiber74State13_in_close :
    tmFiber74StateAt 13 ∈ closeChainFiber tmWord tmFiber74DirectStates tmFiber74DirectStates.length [tmFiber74StateAt 0] := by
  change tmFiber74StateAt 13 ∈ closeChainFiber tmWord tmFiber74DirectStates (15 + 1) [tmFiber74StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber74DirectStates 15 [tmFiber74StateAt 0] (tmFiber74StateAt 13) tmFiber74State13_in_pass1_full

theorem tmFiber74State14_in_close :
    tmFiber74StateAt 14 ∈ closeChainFiber tmWord tmFiber74DirectStates tmFiber74DirectStates.length [tmFiber74StateAt 0] := by
  change tmFiber74StateAt 14 ∈ closeChainFiber tmWord tmFiber74DirectStates (15 + 1) [tmFiber74StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber74DirectStates 15 [tmFiber74StateAt 0] (tmFiber74StateAt 14) tmFiber74State14_in_pass1_full

theorem tmFiber74State15_in_close :
    tmFiber74StateAt 15 ∈ closeChainFiber tmWord tmFiber74DirectStates tmFiber74DirectStates.length [tmFiber74StateAt 0] := by
  change tmFiber74StateAt 15 ∈ closeChainFiber tmWord tmFiber74DirectStates (15 + 1) [tmFiber74StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber74DirectStates 15 [tmFiber74StateAt 0] (tmFiber74StateAt 15) tmFiber74State15_in_pass1_full

theorem tmFiber74DirectConnected :
    chainFiberConnected tmWord tmFiber74DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber74DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber74State0_in_close
  · subst state
    exact tmFiber74State1_in_close
  · subst state
    exact tmFiber74State2_in_close
  · subst state
    exact tmFiber74State3_in_close
  · subst state
    exact tmFiber74State4_in_close
  · subst state
    exact tmFiber74State5_in_close
  · subst state
    exact tmFiber74State6_in_close
  · subst state
    exact tmFiber74State7_in_close
  · subst state
    exact tmFiber74State8_in_close
  · subst state
    exact tmFiber74State9_in_close
  · subst state
    exact tmFiber74State10_in_close
  · subst state
    exact tmFiber74State11_in_close
  · subst state
    exact tmFiber74State12_in_close
  · subst state
    exact tmFiber74State13_in_close
  · subst state
    exact tmFiber74State14_in_close
  · subst state
    exact tmFiber74State15_in_close
  · cases h

def tmFiber75StateAt (i : Nat) : List TauState :=
  directStates (tmFiber75RowAt i).sourceLeft (tmFiber75RowAt i).sourceRight

def tmFiber75DirectStates : List (List TauState) :=
  [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14, tmFiber75StateAt 15]

theorem tmFiber75ReverseRow_1_ok :
    tmRowReverseValid tmFiber75Key tmFiber75Expected (tmFiber75RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber75Chunk0_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber75Chunk0] at h
  exact h.2

theorem tmFiber75ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber75StateAt 0) (tmFiber75StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber75StateAt 0) (tmFiber75StateAt 1)
    (tmFiber75RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber75Key tmFiber75Expected
        (tmFiber75RowAt 1) (by decide) tmFiber75ReverseRow_1_ok
      simpa [tmFiber75StateAt, tmFiber75RowAt, tmFiber75Rows, listGetD, directRow] using h)

theorem tmFiber75ReverseRow_2_ok :
    tmRowReverseValid tmFiber75Key tmFiber75Expected (tmFiber75RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber75Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber75Chunk1] at h
  exact h.1

theorem tmFiber75ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber75StateAt 1) (tmFiber75StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber75StateAt 1) (tmFiber75StateAt 2)
    (tmFiber75RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber75Key tmFiber75Expected
        (tmFiber75RowAt 2) (by decide) tmFiber75ReverseRow_2_ok
      simpa [tmFiber75StateAt, tmFiber75RowAt, tmFiber75Rows, listGetD, directRow] using h)

theorem tmFiber75ReverseRow_3_ok :
    tmRowReverseValid tmFiber75Key tmFiber75Expected (tmFiber75RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber75Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber75Chunk1] at h
  exact h.2

theorem tmFiber75ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber75StateAt 0) (tmFiber75StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber75StateAt 0) (tmFiber75StateAt 3)
    (tmFiber75RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber75Key tmFiber75Expected
        (tmFiber75RowAt 3) (by decide) tmFiber75ReverseRow_3_ok
      simpa [tmFiber75StateAt, tmFiber75RowAt, tmFiber75Rows, listGetD, directRow] using h)

theorem tmFiber75ReverseRow_4_ok :
    tmRowReverseValid tmFiber75Key tmFiber75Expected (tmFiber75RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber75Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber75Chunk2] at h
  exact h.1

theorem tmFiber75ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber75StateAt 0) (tmFiber75StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber75StateAt 0) (tmFiber75StateAt 4)
    (tmFiber75RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber75Key tmFiber75Expected
        (tmFiber75RowAt 4) (by decide) tmFiber75ReverseRow_4_ok
      simpa [tmFiber75StateAt, tmFiber75RowAt, tmFiber75Rows, listGetD, directRow] using h)

theorem tmFiber75ReverseRow_5_ok :
    tmRowReverseValid tmFiber75Key tmFiber75Expected (tmFiber75RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber75Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber75Chunk2] at h
  exact h.2

theorem tmFiber75ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber75StateAt 1) (tmFiber75StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber75StateAt 1) (tmFiber75StateAt 5)
    (tmFiber75RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber75Key tmFiber75Expected
        (tmFiber75RowAt 5) (by decide) tmFiber75ReverseRow_5_ok
      simpa [tmFiber75StateAt, tmFiber75RowAt, tmFiber75Rows, listGetD, directRow] using h)

theorem tmFiber75ReverseRow_6_ok :
    tmRowReverseValid tmFiber75Key tmFiber75Expected (tmFiber75RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber75Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber75Chunk3] at h
  exact h.1

theorem tmFiber75ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber75StateAt 2) (tmFiber75StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber75StateAt 2) (tmFiber75StateAt 6)
    (tmFiber75RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber75Key tmFiber75Expected
        (tmFiber75RowAt 6) (by decide) tmFiber75ReverseRow_6_ok
      simpa [tmFiber75StateAt, tmFiber75RowAt, tmFiber75Rows, listGetD, directRow] using h)

theorem tmFiber75ReverseRow_7_ok :
    tmRowReverseValid tmFiber75Key tmFiber75Expected (tmFiber75RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber75Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber75Chunk3] at h
  exact h.2

theorem tmFiber75ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber75StateAt 3) (tmFiber75StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber75StateAt 3) (tmFiber75StateAt 7)
    (tmFiber75RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber75Key tmFiber75Expected
        (tmFiber75RowAt 7) (by decide) tmFiber75ReverseRow_7_ok
      simpa [tmFiber75StateAt, tmFiber75RowAt, tmFiber75Rows, listGetD, directRow] using h)

theorem tmFiber75ReverseRow_8_ok :
    tmRowReverseValid tmFiber75Key tmFiber75Expected (tmFiber75RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber75Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber75Chunk4] at h
  exact h.1

theorem tmFiber75ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber75StateAt 0) (tmFiber75StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber75StateAt 0) (tmFiber75StateAt 8)
    (tmFiber75RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber75Key tmFiber75Expected
        (tmFiber75RowAt 8) (by decide) tmFiber75ReverseRow_8_ok
      simpa [tmFiber75StateAt, tmFiber75RowAt, tmFiber75Rows, listGetD, directRow] using h)

theorem tmFiber75ReverseRow_9_ok :
    tmRowReverseValid tmFiber75Key tmFiber75Expected (tmFiber75RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber75Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber75Chunk4] at h
  exact h.2

theorem tmFiber75ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber75StateAt 1) (tmFiber75StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber75StateAt 1) (tmFiber75StateAt 9)
    (tmFiber75RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber75Key tmFiber75Expected
        (tmFiber75RowAt 9) (by decide) tmFiber75ReverseRow_9_ok
      simpa [tmFiber75StateAt, tmFiber75RowAt, tmFiber75Rows, listGetD, directRow] using h)

theorem tmFiber75ReverseRow_10_ok :
    tmRowReverseValid tmFiber75Key tmFiber75Expected (tmFiber75RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber75Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber75Chunk5] at h
  exact h.1

theorem tmFiber75ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber75StateAt 2) (tmFiber75StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber75StateAt 2) (tmFiber75StateAt 10)
    (tmFiber75RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber75Key tmFiber75Expected
        (tmFiber75RowAt 10) (by decide) tmFiber75ReverseRow_10_ok
      simpa [tmFiber75StateAt, tmFiber75RowAt, tmFiber75Rows, listGetD, directRow] using h)

theorem tmFiber75ReverseRow_11_ok :
    tmRowReverseValid tmFiber75Key tmFiber75Expected (tmFiber75RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber75Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber75Chunk5] at h
  exact h.2

theorem tmFiber75ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber75StateAt 3) (tmFiber75StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber75StateAt 3) (tmFiber75StateAt 11)
    (tmFiber75RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber75Key tmFiber75Expected
        (tmFiber75RowAt 11) (by decide) tmFiber75ReverseRow_11_ok
      simpa [tmFiber75StateAt, tmFiber75RowAt, tmFiber75Rows, listGetD, directRow] using h)

theorem tmFiber75ReverseRow_12_ok :
    tmRowReverseValid tmFiber75Key tmFiber75Expected (tmFiber75RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber75Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber75Chunk6] at h
  exact h.1

theorem tmFiber75ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber75StateAt 4) (tmFiber75StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber75StateAt 4) (tmFiber75StateAt 12)
    (tmFiber75RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber75Key tmFiber75Expected
        (tmFiber75RowAt 12) (by decide) tmFiber75ReverseRow_12_ok
      simpa [tmFiber75StateAt, tmFiber75RowAt, tmFiber75Rows, listGetD, directRow] using h)

theorem tmFiber75ReverseRow_13_ok :
    tmRowReverseValid tmFiber75Key tmFiber75Expected (tmFiber75RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber75Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber75Chunk6] at h
  exact h.2

theorem tmFiber75ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber75StateAt 5) (tmFiber75StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber75StateAt 5) (tmFiber75StateAt 13)
    (tmFiber75RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber75Key tmFiber75Expected
        (tmFiber75RowAt 13) (by decide) tmFiber75ReverseRow_13_ok
      simpa [tmFiber75StateAt, tmFiber75RowAt, tmFiber75Rows, listGetD, directRow] using h)

theorem tmFiber75ReverseRow_14_ok :
    tmRowReverseValid tmFiber75Key tmFiber75Expected (tmFiber75RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber75Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber75Chunk7] at h
  exact h.1

theorem tmFiber75ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber75StateAt 6) (tmFiber75StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber75StateAt 6) (tmFiber75StateAt 14)
    (tmFiber75RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber75Key tmFiber75Expected
        (tmFiber75RowAt 14) (by decide) tmFiber75ReverseRow_14_ok
      simpa [tmFiber75StateAt, tmFiber75RowAt, tmFiber75Rows, listGetD, directRow] using h)

theorem tmFiber75ReverseRow_15_ok :
    tmRowReverseValid tmFiber75Key tmFiber75Expected (tmFiber75RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber75Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber75Chunk7] at h
  exact h.2

theorem tmFiber75ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber75StateAt 7) (tmFiber75StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber75StateAt 7) (tmFiber75StateAt 15)
    (tmFiber75RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber75Key tmFiber75Expected
        (tmFiber75RowAt 15) (by decide) tmFiber75ReverseRow_15_ok
      simpa [tmFiber75StateAt, tmFiber75RowAt, tmFiber75Rows, listGetD, directRow] using h)

theorem tmFiber75State0_in_pass1_prefix :
    tmFiber75StateAt 0 ∈ chainClosureStep tmWord [tmFiber75StateAt 0] [tmFiber75StateAt 0] := by
  exact chainClosureStep_mem_of_seen tmWord [tmFiber75StateAt 0] [tmFiber75StateAt 0] (tmFiber75StateAt 0) (by simp)

theorem tmFiber75State1_in_pass1_prefix :
    tmFiber75StateAt 1 ∈ chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1] [tmFiber75StateAt 0] := by
  have hparentBefore :
      tmFiber75StateAt 0 ∈ chainClosureStep tmWord [tmFiber75StateAt 0] [tmFiber75StateAt 0] := by
    exact tmFiber75State0_in_pass1_prefix
  rw [show [tmFiber75StateAt 0, tmFiber75StateAt 1] = [tmFiber75StateAt 0] ++ [tmFiber75StateAt 1] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber75StateAt 1) []
    (chainClosureStep tmWord [tmFiber75StateAt 0] [tmFiber75StateAt 0]) (tmFiber75StateAt 0)
    hparentBefore tmFiber75ReverseSingleStep1

theorem tmFiber75State2_in_pass1_prefix :
    tmFiber75StateAt 2 ∈ chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2] [tmFiber75StateAt 0] := by
  have hparentBefore :
      tmFiber75StateAt 1 ∈ chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1] [tmFiber75StateAt 0] := by
    exact tmFiber75State1_in_pass1_prefix
  rw [show [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2] = [tmFiber75StateAt 0, tmFiber75StateAt 1] ++ [tmFiber75StateAt 2] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber75StateAt 2) []
    (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1] [tmFiber75StateAt 0]) (tmFiber75StateAt 1)
    hparentBefore tmFiber75ReverseSingleStep2

theorem tmFiber75State3_in_pass1_prefix :
    tmFiber75StateAt 3 ∈ chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3] [tmFiber75StateAt 0] := by
  have hparentBefore :
      tmFiber75StateAt 0 ∈ chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2] [tmFiber75StateAt 0] := by
    rw [show [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2] = [tmFiber75StateAt 0] ++ [tmFiber75StateAt 1, tmFiber75StateAt 2] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber75StateAt 1, tmFiber75StateAt 2]
      (chainClosureStep tmWord [tmFiber75StateAt 0] [tmFiber75StateAt 0]) (tmFiber75StateAt 0)
      tmFiber75State0_in_pass1_prefix
  rw [show [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3] = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2] ++ [tmFiber75StateAt 3] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber75StateAt 3) []
    (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2] [tmFiber75StateAt 0]) (tmFiber75StateAt 0)
    hparentBefore tmFiber75ReverseSingleStep3

theorem tmFiber75State4_in_pass1_prefix :
    tmFiber75StateAt 4 ∈ chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4] [tmFiber75StateAt 0] := by
  have hparentBefore :
      tmFiber75StateAt 0 ∈ chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3] [tmFiber75StateAt 0] := by
    rw [show [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3] = [tmFiber75StateAt 0] ++ [tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3]
      (chainClosureStep tmWord [tmFiber75StateAt 0] [tmFiber75StateAt 0]) (tmFiber75StateAt 0)
      tmFiber75State0_in_pass1_prefix
  rw [show [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4] = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3] ++ [tmFiber75StateAt 4] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber75StateAt 4) []
    (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3] [tmFiber75StateAt 0]) (tmFiber75StateAt 0)
    hparentBefore tmFiber75ReverseSingleStep4

theorem tmFiber75State5_in_pass1_prefix :
    tmFiber75StateAt 5 ∈ chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5] [tmFiber75StateAt 0] := by
  have hparentBefore :
      tmFiber75StateAt 1 ∈ chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4] [tmFiber75StateAt 0] := by
    rw [show [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4] = [tmFiber75StateAt 0, tmFiber75StateAt 1] ++ [tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4]
      (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1] [tmFiber75StateAt 0]) (tmFiber75StateAt 1)
      tmFiber75State1_in_pass1_prefix
  rw [show [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5] = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4] ++ [tmFiber75StateAt 5] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber75StateAt 5) []
    (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4] [tmFiber75StateAt 0]) (tmFiber75StateAt 1)
    hparentBefore tmFiber75ReverseSingleStep5

theorem tmFiber75State6_in_pass1_prefix :
    tmFiber75StateAt 6 ∈ chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6] [tmFiber75StateAt 0] := by
  have hparentBefore :
      tmFiber75StateAt 2 ∈ chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5] [tmFiber75StateAt 0] := by
    rw [show [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5] = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2] ++ [tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5]
      (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2] [tmFiber75StateAt 0]) (tmFiber75StateAt 2)
      tmFiber75State2_in_pass1_prefix
  rw [show [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6] = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5] ++ [tmFiber75StateAt 6] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber75StateAt 6) []
    (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5] [tmFiber75StateAt 0]) (tmFiber75StateAt 2)
    hparentBefore tmFiber75ReverseSingleStep6

theorem tmFiber75State7_in_pass1_prefix :
    tmFiber75StateAt 7 ∈ chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7] [tmFiber75StateAt 0] := by
  have hparentBefore :
      tmFiber75StateAt 3 ∈ chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6] [tmFiber75StateAt 0] := by
    rw [show [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6] = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3] ++ [tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6]
      (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3] [tmFiber75StateAt 0]) (tmFiber75StateAt 3)
      tmFiber75State3_in_pass1_prefix
  rw [show [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7] = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6] ++ [tmFiber75StateAt 7] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber75StateAt 7) []
    (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6] [tmFiber75StateAt 0]) (tmFiber75StateAt 3)
    hparentBefore tmFiber75ReverseSingleStep7

theorem tmFiber75State8_in_pass1_prefix :
    tmFiber75StateAt 8 ∈ chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8] [tmFiber75StateAt 0] := by
  have hparentBefore :
      tmFiber75StateAt 0 ∈ chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7] [tmFiber75StateAt 0] := by
    rw [show [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7] = [tmFiber75StateAt 0] ++ [tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7]
      (chainClosureStep tmWord [tmFiber75StateAt 0] [tmFiber75StateAt 0]) (tmFiber75StateAt 0)
      tmFiber75State0_in_pass1_prefix
  rw [show [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8] = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7] ++ [tmFiber75StateAt 8] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber75StateAt 8) []
    (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7] [tmFiber75StateAt 0]) (tmFiber75StateAt 0)
    hparentBefore tmFiber75ReverseSingleStep8

theorem tmFiber75State9_in_pass1_prefix :
    tmFiber75StateAt 9 ∈ chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9] [tmFiber75StateAt 0] := by
  have hparentBefore :
      tmFiber75StateAt 1 ∈ chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8] [tmFiber75StateAt 0] := by
    rw [show [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8] = [tmFiber75StateAt 0, tmFiber75StateAt 1] ++ [tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8]
      (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1] [tmFiber75StateAt 0]) (tmFiber75StateAt 1)
      tmFiber75State1_in_pass1_prefix
  rw [show [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9] = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8] ++ [tmFiber75StateAt 9] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber75StateAt 9) []
    (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8] [tmFiber75StateAt 0]) (tmFiber75StateAt 1)
    hparentBefore tmFiber75ReverseSingleStep9

theorem tmFiber75State10_in_pass1_prefix :
    tmFiber75StateAt 10 ∈ chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10] [tmFiber75StateAt 0] := by
  have hparentBefore :
      tmFiber75StateAt 2 ∈ chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9] [tmFiber75StateAt 0] := by
    rw [show [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9] = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2] ++ [tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9]
      (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2] [tmFiber75StateAt 0]) (tmFiber75StateAt 2)
      tmFiber75State2_in_pass1_prefix
  rw [show [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10] = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9] ++ [tmFiber75StateAt 10] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber75StateAt 10) []
    (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9] [tmFiber75StateAt 0]) (tmFiber75StateAt 2)
    hparentBefore tmFiber75ReverseSingleStep10

theorem tmFiber75State11_in_pass1_prefix :
    tmFiber75StateAt 11 ∈ chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11] [tmFiber75StateAt 0] := by
  have hparentBefore :
      tmFiber75StateAt 3 ∈ chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10] [tmFiber75StateAt 0] := by
    rw [show [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10] = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3] ++ [tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10]
      (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3] [tmFiber75StateAt 0]) (tmFiber75StateAt 3)
      tmFiber75State3_in_pass1_prefix
  rw [show [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11] = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10] ++ [tmFiber75StateAt 11] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber75StateAt 11) []
    (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10] [tmFiber75StateAt 0]) (tmFiber75StateAt 3)
    hparentBefore tmFiber75ReverseSingleStep11

theorem tmFiber75State12_in_pass1_prefix :
    tmFiber75StateAt 12 ∈ chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12] [tmFiber75StateAt 0] := by
  have hparentBefore :
      tmFiber75StateAt 4 ∈ chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11] [tmFiber75StateAt 0] := by
    rw [show [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11] = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4] ++ [tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11]
      (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4] [tmFiber75StateAt 0]) (tmFiber75StateAt 4)
      tmFiber75State4_in_pass1_prefix
  rw [show [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12] = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11] ++ [tmFiber75StateAt 12] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber75StateAt 12) []
    (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11] [tmFiber75StateAt 0]) (tmFiber75StateAt 4)
    hparentBefore tmFiber75ReverseSingleStep12

theorem tmFiber75State13_in_pass1_prefix :
    tmFiber75StateAt 13 ∈ chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13] [tmFiber75StateAt 0] := by
  have hparentBefore :
      tmFiber75StateAt 5 ∈ chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12] [tmFiber75StateAt 0] := by
    rw [show [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12] = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5] ++ [tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12]
      (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5] [tmFiber75StateAt 0]) (tmFiber75StateAt 5)
      tmFiber75State5_in_pass1_prefix
  rw [show [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13] = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12] ++ [tmFiber75StateAt 13] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber75StateAt 13) []
    (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12] [tmFiber75StateAt 0]) (tmFiber75StateAt 5)
    hparentBefore tmFiber75ReverseSingleStep13

theorem tmFiber75State14_in_pass1_prefix :
    tmFiber75StateAt 14 ∈ chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14] [tmFiber75StateAt 0] := by
  have hparentBefore :
      tmFiber75StateAt 6 ∈ chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13] [tmFiber75StateAt 0] := by
    rw [show [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13] = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6] ++ [tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13]
      (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6] [tmFiber75StateAt 0]) (tmFiber75StateAt 6)
      tmFiber75State6_in_pass1_prefix
  rw [show [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14] = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13] ++ [tmFiber75StateAt 14] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber75StateAt 14) []
    (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13] [tmFiber75StateAt 0]) (tmFiber75StateAt 6)
    hparentBefore tmFiber75ReverseSingleStep14

theorem tmFiber75State15_in_pass1_prefix :
    tmFiber75StateAt 15 ∈ chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14, tmFiber75StateAt 15] [tmFiber75StateAt 0] := by
  have hparentBefore :
      tmFiber75StateAt 7 ∈ chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14] [tmFiber75StateAt 0] := by
    rw [show [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14] = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7] ++ [tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14]
      (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7] [tmFiber75StateAt 0]) (tmFiber75StateAt 7)
      tmFiber75State7_in_pass1_prefix
  rw [show [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14, tmFiber75StateAt 15] = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14] ++ [tmFiber75StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber75StateAt 15) []
    (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14] [tmFiber75StateAt 0]) (tmFiber75StateAt 7)
    hparentBefore tmFiber75ReverseSingleStep15

theorem tmFiber75State0_in_pass1_full :
    tmFiber75StateAt 0 ∈ chainClosureStep tmWord tmFiber75DirectStates [tmFiber75StateAt 0] := by
  rw [show tmFiber75DirectStates = [tmFiber75StateAt 0] ++ [tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14, tmFiber75StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14, tmFiber75StateAt 15]
    (chainClosureStep tmWord [tmFiber75StateAt 0] [tmFiber75StateAt 0]) (tmFiber75StateAt 0)
    tmFiber75State0_in_pass1_prefix

theorem tmFiber75State1_in_pass1_full :
    tmFiber75StateAt 1 ∈ chainClosureStep tmWord tmFiber75DirectStates [tmFiber75StateAt 0] := by
  rw [show tmFiber75DirectStates = [tmFiber75StateAt 0, tmFiber75StateAt 1] ++ [tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14, tmFiber75StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14, tmFiber75StateAt 15]
    (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1] [tmFiber75StateAt 0]) (tmFiber75StateAt 1)
    tmFiber75State1_in_pass1_prefix

theorem tmFiber75State2_in_pass1_full :
    tmFiber75StateAt 2 ∈ chainClosureStep tmWord tmFiber75DirectStates [tmFiber75StateAt 0] := by
  rw [show tmFiber75DirectStates = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2] ++ [tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14, tmFiber75StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14, tmFiber75StateAt 15]
    (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2] [tmFiber75StateAt 0]) (tmFiber75StateAt 2)
    tmFiber75State2_in_pass1_prefix

theorem tmFiber75State3_in_pass1_full :
    tmFiber75StateAt 3 ∈ chainClosureStep tmWord tmFiber75DirectStates [tmFiber75StateAt 0] := by
  rw [show tmFiber75DirectStates = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3] ++ [tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14, tmFiber75StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14, tmFiber75StateAt 15]
    (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3] [tmFiber75StateAt 0]) (tmFiber75StateAt 3)
    tmFiber75State3_in_pass1_prefix

theorem tmFiber75State4_in_pass1_full :
    tmFiber75StateAt 4 ∈ chainClosureStep tmWord tmFiber75DirectStates [tmFiber75StateAt 0] := by
  rw [show tmFiber75DirectStates = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4] ++ [tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14, tmFiber75StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14, tmFiber75StateAt 15]
    (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4] [tmFiber75StateAt 0]) (tmFiber75StateAt 4)
    tmFiber75State4_in_pass1_prefix

theorem tmFiber75State5_in_pass1_full :
    tmFiber75StateAt 5 ∈ chainClosureStep tmWord tmFiber75DirectStates [tmFiber75StateAt 0] := by
  rw [show tmFiber75DirectStates = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5] ++ [tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14, tmFiber75StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14, tmFiber75StateAt 15]
    (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5] [tmFiber75StateAt 0]) (tmFiber75StateAt 5)
    tmFiber75State5_in_pass1_prefix

theorem tmFiber75State6_in_pass1_full :
    tmFiber75StateAt 6 ∈ chainClosureStep tmWord tmFiber75DirectStates [tmFiber75StateAt 0] := by
  rw [show tmFiber75DirectStates = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6] ++ [tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14, tmFiber75StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14, tmFiber75StateAt 15]
    (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6] [tmFiber75StateAt 0]) (tmFiber75StateAt 6)
    tmFiber75State6_in_pass1_prefix

theorem tmFiber75State7_in_pass1_full :
    tmFiber75StateAt 7 ∈ chainClosureStep tmWord tmFiber75DirectStates [tmFiber75StateAt 0] := by
  rw [show tmFiber75DirectStates = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7] ++ [tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14, tmFiber75StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14, tmFiber75StateAt 15]
    (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7] [tmFiber75StateAt 0]) (tmFiber75StateAt 7)
    tmFiber75State7_in_pass1_prefix

theorem tmFiber75State8_in_pass1_full :
    tmFiber75StateAt 8 ∈ chainClosureStep tmWord tmFiber75DirectStates [tmFiber75StateAt 0] := by
  rw [show tmFiber75DirectStates = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8] ++ [tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14, tmFiber75StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14, tmFiber75StateAt 15]
    (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8] [tmFiber75StateAt 0]) (tmFiber75StateAt 8)
    tmFiber75State8_in_pass1_prefix

theorem tmFiber75State9_in_pass1_full :
    tmFiber75StateAt 9 ∈ chainClosureStep tmWord tmFiber75DirectStates [tmFiber75StateAt 0] := by
  rw [show tmFiber75DirectStates = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9] ++ [tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14, tmFiber75StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14, tmFiber75StateAt 15]
    (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9] [tmFiber75StateAt 0]) (tmFiber75StateAt 9)
    tmFiber75State9_in_pass1_prefix

theorem tmFiber75State10_in_pass1_full :
    tmFiber75StateAt 10 ∈ chainClosureStep tmWord tmFiber75DirectStates [tmFiber75StateAt 0] := by
  rw [show tmFiber75DirectStates = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10] ++ [tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14, tmFiber75StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14, tmFiber75StateAt 15]
    (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10] [tmFiber75StateAt 0]) (tmFiber75StateAt 10)
    tmFiber75State10_in_pass1_prefix

theorem tmFiber75State11_in_pass1_full :
    tmFiber75StateAt 11 ∈ chainClosureStep tmWord tmFiber75DirectStates [tmFiber75StateAt 0] := by
  rw [show tmFiber75DirectStates = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11] ++ [tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14, tmFiber75StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14, tmFiber75StateAt 15]
    (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11] [tmFiber75StateAt 0]) (tmFiber75StateAt 11)
    tmFiber75State11_in_pass1_prefix

theorem tmFiber75State12_in_pass1_full :
    tmFiber75StateAt 12 ∈ chainClosureStep tmWord tmFiber75DirectStates [tmFiber75StateAt 0] := by
  rw [show tmFiber75DirectStates = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12] ++ [tmFiber75StateAt 13, tmFiber75StateAt 14, tmFiber75StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber75StateAt 13, tmFiber75StateAt 14, tmFiber75StateAt 15]
    (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12] [tmFiber75StateAt 0]) (tmFiber75StateAt 12)
    tmFiber75State12_in_pass1_prefix

theorem tmFiber75State13_in_pass1_full :
    tmFiber75StateAt 13 ∈ chainClosureStep tmWord tmFiber75DirectStates [tmFiber75StateAt 0] := by
  rw [show tmFiber75DirectStates = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13] ++ [tmFiber75StateAt 14, tmFiber75StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber75StateAt 14, tmFiber75StateAt 15]
    (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13] [tmFiber75StateAt 0]) (tmFiber75StateAt 13)
    tmFiber75State13_in_pass1_prefix

theorem tmFiber75State14_in_pass1_full :
    tmFiber75StateAt 14 ∈ chainClosureStep tmWord tmFiber75DirectStates [tmFiber75StateAt 0] := by
  rw [show tmFiber75DirectStates = [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14] ++ [tmFiber75StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber75StateAt 15]
    (chainClosureStep tmWord [tmFiber75StateAt 0, tmFiber75StateAt 1, tmFiber75StateAt 2, tmFiber75StateAt 3, tmFiber75StateAt 4, tmFiber75StateAt 5, tmFiber75StateAt 6, tmFiber75StateAt 7, tmFiber75StateAt 8, tmFiber75StateAt 9, tmFiber75StateAt 10, tmFiber75StateAt 11, tmFiber75StateAt 12, tmFiber75StateAt 13, tmFiber75StateAt 14] [tmFiber75StateAt 0]) (tmFiber75StateAt 14)
    tmFiber75State14_in_pass1_prefix

theorem tmFiber75State15_in_pass1_full :
    tmFiber75StateAt 15 ∈ chainClosureStep tmWord tmFiber75DirectStates [tmFiber75StateAt 0] := by
  simpa [tmFiber75DirectStates] using tmFiber75State15_in_pass1_prefix

theorem tmFiber75State0_in_close :
    tmFiber75StateAt 0 ∈ closeChainFiber tmWord tmFiber75DirectStates tmFiber75DirectStates.length [tmFiber75StateAt 0] := by
  change tmFiber75StateAt 0 ∈ closeChainFiber tmWord tmFiber75DirectStates (15 + 1) [tmFiber75StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber75DirectStates 15 [tmFiber75StateAt 0] (tmFiber75StateAt 0) tmFiber75State0_in_pass1_full

theorem tmFiber75State1_in_close :
    tmFiber75StateAt 1 ∈ closeChainFiber tmWord tmFiber75DirectStates tmFiber75DirectStates.length [tmFiber75StateAt 0] := by
  change tmFiber75StateAt 1 ∈ closeChainFiber tmWord tmFiber75DirectStates (15 + 1) [tmFiber75StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber75DirectStates 15 [tmFiber75StateAt 0] (tmFiber75StateAt 1) tmFiber75State1_in_pass1_full

theorem tmFiber75State2_in_close :
    tmFiber75StateAt 2 ∈ closeChainFiber tmWord tmFiber75DirectStates tmFiber75DirectStates.length [tmFiber75StateAt 0] := by
  change tmFiber75StateAt 2 ∈ closeChainFiber tmWord tmFiber75DirectStates (15 + 1) [tmFiber75StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber75DirectStates 15 [tmFiber75StateAt 0] (tmFiber75StateAt 2) tmFiber75State2_in_pass1_full

theorem tmFiber75State3_in_close :
    tmFiber75StateAt 3 ∈ closeChainFiber tmWord tmFiber75DirectStates tmFiber75DirectStates.length [tmFiber75StateAt 0] := by
  change tmFiber75StateAt 3 ∈ closeChainFiber tmWord tmFiber75DirectStates (15 + 1) [tmFiber75StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber75DirectStates 15 [tmFiber75StateAt 0] (tmFiber75StateAt 3) tmFiber75State3_in_pass1_full

theorem tmFiber75State4_in_close :
    tmFiber75StateAt 4 ∈ closeChainFiber tmWord tmFiber75DirectStates tmFiber75DirectStates.length [tmFiber75StateAt 0] := by
  change tmFiber75StateAt 4 ∈ closeChainFiber tmWord tmFiber75DirectStates (15 + 1) [tmFiber75StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber75DirectStates 15 [tmFiber75StateAt 0] (tmFiber75StateAt 4) tmFiber75State4_in_pass1_full

theorem tmFiber75State5_in_close :
    tmFiber75StateAt 5 ∈ closeChainFiber tmWord tmFiber75DirectStates tmFiber75DirectStates.length [tmFiber75StateAt 0] := by
  change tmFiber75StateAt 5 ∈ closeChainFiber tmWord tmFiber75DirectStates (15 + 1) [tmFiber75StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber75DirectStates 15 [tmFiber75StateAt 0] (tmFiber75StateAt 5) tmFiber75State5_in_pass1_full

theorem tmFiber75State6_in_close :
    tmFiber75StateAt 6 ∈ closeChainFiber tmWord tmFiber75DirectStates tmFiber75DirectStates.length [tmFiber75StateAt 0] := by
  change tmFiber75StateAt 6 ∈ closeChainFiber tmWord tmFiber75DirectStates (15 + 1) [tmFiber75StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber75DirectStates 15 [tmFiber75StateAt 0] (tmFiber75StateAt 6) tmFiber75State6_in_pass1_full

theorem tmFiber75State7_in_close :
    tmFiber75StateAt 7 ∈ closeChainFiber tmWord tmFiber75DirectStates tmFiber75DirectStates.length [tmFiber75StateAt 0] := by
  change tmFiber75StateAt 7 ∈ closeChainFiber tmWord tmFiber75DirectStates (15 + 1) [tmFiber75StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber75DirectStates 15 [tmFiber75StateAt 0] (tmFiber75StateAt 7) tmFiber75State7_in_pass1_full

theorem tmFiber75State8_in_close :
    tmFiber75StateAt 8 ∈ closeChainFiber tmWord tmFiber75DirectStates tmFiber75DirectStates.length [tmFiber75StateAt 0] := by
  change tmFiber75StateAt 8 ∈ closeChainFiber tmWord tmFiber75DirectStates (15 + 1) [tmFiber75StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber75DirectStates 15 [tmFiber75StateAt 0] (tmFiber75StateAt 8) tmFiber75State8_in_pass1_full

theorem tmFiber75State9_in_close :
    tmFiber75StateAt 9 ∈ closeChainFiber tmWord tmFiber75DirectStates tmFiber75DirectStates.length [tmFiber75StateAt 0] := by
  change tmFiber75StateAt 9 ∈ closeChainFiber tmWord tmFiber75DirectStates (15 + 1) [tmFiber75StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber75DirectStates 15 [tmFiber75StateAt 0] (tmFiber75StateAt 9) tmFiber75State9_in_pass1_full

theorem tmFiber75State10_in_close :
    tmFiber75StateAt 10 ∈ closeChainFiber tmWord tmFiber75DirectStates tmFiber75DirectStates.length [tmFiber75StateAt 0] := by
  change tmFiber75StateAt 10 ∈ closeChainFiber tmWord tmFiber75DirectStates (15 + 1) [tmFiber75StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber75DirectStates 15 [tmFiber75StateAt 0] (tmFiber75StateAt 10) tmFiber75State10_in_pass1_full

theorem tmFiber75State11_in_close :
    tmFiber75StateAt 11 ∈ closeChainFiber tmWord tmFiber75DirectStates tmFiber75DirectStates.length [tmFiber75StateAt 0] := by
  change tmFiber75StateAt 11 ∈ closeChainFiber tmWord tmFiber75DirectStates (15 + 1) [tmFiber75StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber75DirectStates 15 [tmFiber75StateAt 0] (tmFiber75StateAt 11) tmFiber75State11_in_pass1_full

theorem tmFiber75State12_in_close :
    tmFiber75StateAt 12 ∈ closeChainFiber tmWord tmFiber75DirectStates tmFiber75DirectStates.length [tmFiber75StateAt 0] := by
  change tmFiber75StateAt 12 ∈ closeChainFiber tmWord tmFiber75DirectStates (15 + 1) [tmFiber75StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber75DirectStates 15 [tmFiber75StateAt 0] (tmFiber75StateAt 12) tmFiber75State12_in_pass1_full

theorem tmFiber75State13_in_close :
    tmFiber75StateAt 13 ∈ closeChainFiber tmWord tmFiber75DirectStates tmFiber75DirectStates.length [tmFiber75StateAt 0] := by
  change tmFiber75StateAt 13 ∈ closeChainFiber tmWord tmFiber75DirectStates (15 + 1) [tmFiber75StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber75DirectStates 15 [tmFiber75StateAt 0] (tmFiber75StateAt 13) tmFiber75State13_in_pass1_full

theorem tmFiber75State14_in_close :
    tmFiber75StateAt 14 ∈ closeChainFiber tmWord tmFiber75DirectStates tmFiber75DirectStates.length [tmFiber75StateAt 0] := by
  change tmFiber75StateAt 14 ∈ closeChainFiber tmWord tmFiber75DirectStates (15 + 1) [tmFiber75StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber75DirectStates 15 [tmFiber75StateAt 0] (tmFiber75StateAt 14) tmFiber75State14_in_pass1_full

theorem tmFiber75State15_in_close :
    tmFiber75StateAt 15 ∈ closeChainFiber tmWord tmFiber75DirectStates tmFiber75DirectStates.length [tmFiber75StateAt 0] := by
  change tmFiber75StateAt 15 ∈ closeChainFiber tmWord tmFiber75DirectStates (15 + 1) [tmFiber75StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber75DirectStates 15 [tmFiber75StateAt 0] (tmFiber75StateAt 15) tmFiber75State15_in_pass1_full

theorem tmFiber75DirectConnected :
    chainFiberConnected tmWord tmFiber75DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber75DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber75State0_in_close
  · subst state
    exact tmFiber75State1_in_close
  · subst state
    exact tmFiber75State2_in_close
  · subst state
    exact tmFiber75State3_in_close
  · subst state
    exact tmFiber75State4_in_close
  · subst state
    exact tmFiber75State5_in_close
  · subst state
    exact tmFiber75State6_in_close
  · subst state
    exact tmFiber75State7_in_close
  · subst state
    exact tmFiber75State8_in_close
  · subst state
    exact tmFiber75State9_in_close
  · subst state
    exact tmFiber75State10_in_close
  · subst state
    exact tmFiber75State11_in_close
  · subst state
    exact tmFiber75State12_in_close
  · subst state
    exact tmFiber75State13_in_close
  · subst state
    exact tmFiber75State14_in_close
  · subst state
    exact tmFiber75State15_in_close
  · cases h

def tmFiber77StateAt (i : Nat) : List TauState :=
  directStates (tmFiber77RowAt i).sourceLeft (tmFiber77RowAt i).sourceRight

def tmFiber77DirectStates : List (List TauState) :=
  [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14, tmFiber77StateAt 15]

theorem tmFiber77ReverseRow_1_ok :
    tmRowReverseValid tmFiber77Key tmFiber77Expected (tmFiber77RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber77Chunk0_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber77Chunk0] at h
  exact h.2

theorem tmFiber77ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber77StateAt 0) (tmFiber77StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber77StateAt 0) (tmFiber77StateAt 1)
    (tmFiber77RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber77Key tmFiber77Expected
        (tmFiber77RowAt 1) (by decide) tmFiber77ReverseRow_1_ok
      simpa [tmFiber77StateAt, tmFiber77RowAt, tmFiber77Rows, listGetD, directRow] using h)

theorem tmFiber77ReverseRow_2_ok :
    tmRowReverseValid tmFiber77Key tmFiber77Expected (tmFiber77RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber77Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber77Chunk1] at h
  exact h.1

theorem tmFiber77ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber77StateAt 1) (tmFiber77StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber77StateAt 1) (tmFiber77StateAt 2)
    (tmFiber77RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber77Key tmFiber77Expected
        (tmFiber77RowAt 2) (by decide) tmFiber77ReverseRow_2_ok
      simpa [tmFiber77StateAt, tmFiber77RowAt, tmFiber77Rows, listGetD, directRow] using h)

theorem tmFiber77ReverseRow_3_ok :
    tmRowReverseValid tmFiber77Key tmFiber77Expected (tmFiber77RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber77Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber77Chunk1] at h
  exact h.2

theorem tmFiber77ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber77StateAt 0) (tmFiber77StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber77StateAt 0) (tmFiber77StateAt 3)
    (tmFiber77RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber77Key tmFiber77Expected
        (tmFiber77RowAt 3) (by decide) tmFiber77ReverseRow_3_ok
      simpa [tmFiber77StateAt, tmFiber77RowAt, tmFiber77Rows, listGetD, directRow] using h)

theorem tmFiber77ReverseRow_4_ok :
    tmRowReverseValid tmFiber77Key tmFiber77Expected (tmFiber77RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber77Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber77Chunk2] at h
  exact h.1

theorem tmFiber77ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber77StateAt 0) (tmFiber77StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber77StateAt 0) (tmFiber77StateAt 4)
    (tmFiber77RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber77Key tmFiber77Expected
        (tmFiber77RowAt 4) (by decide) tmFiber77ReverseRow_4_ok
      simpa [tmFiber77StateAt, tmFiber77RowAt, tmFiber77Rows, listGetD, directRow] using h)

theorem tmFiber77ReverseRow_5_ok :
    tmRowReverseValid tmFiber77Key tmFiber77Expected (tmFiber77RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber77Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber77Chunk2] at h
  exact h.2

theorem tmFiber77ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber77StateAt 1) (tmFiber77StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber77StateAt 1) (tmFiber77StateAt 5)
    (tmFiber77RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber77Key tmFiber77Expected
        (tmFiber77RowAt 5) (by decide) tmFiber77ReverseRow_5_ok
      simpa [tmFiber77StateAt, tmFiber77RowAt, tmFiber77Rows, listGetD, directRow] using h)

theorem tmFiber77ReverseRow_6_ok :
    tmRowReverseValid tmFiber77Key tmFiber77Expected (tmFiber77RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber77Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber77Chunk3] at h
  exact h.1

theorem tmFiber77ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber77StateAt 2) (tmFiber77StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber77StateAt 2) (tmFiber77StateAt 6)
    (tmFiber77RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber77Key tmFiber77Expected
        (tmFiber77RowAt 6) (by decide) tmFiber77ReverseRow_6_ok
      simpa [tmFiber77StateAt, tmFiber77RowAt, tmFiber77Rows, listGetD, directRow] using h)

theorem tmFiber77ReverseRow_7_ok :
    tmRowReverseValid tmFiber77Key tmFiber77Expected (tmFiber77RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber77Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber77Chunk3] at h
  exact h.2

theorem tmFiber77ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber77StateAt 3) (tmFiber77StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber77StateAt 3) (tmFiber77StateAt 7)
    (tmFiber77RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber77Key tmFiber77Expected
        (tmFiber77RowAt 7) (by decide) tmFiber77ReverseRow_7_ok
      simpa [tmFiber77StateAt, tmFiber77RowAt, tmFiber77Rows, listGetD, directRow] using h)

theorem tmFiber77ReverseRow_8_ok :
    tmRowReverseValid tmFiber77Key tmFiber77Expected (tmFiber77RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber77Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber77Chunk4] at h
  exact h.1

theorem tmFiber77ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber77StateAt 0) (tmFiber77StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber77StateAt 0) (tmFiber77StateAt 8)
    (tmFiber77RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber77Key tmFiber77Expected
        (tmFiber77RowAt 8) (by decide) tmFiber77ReverseRow_8_ok
      simpa [tmFiber77StateAt, tmFiber77RowAt, tmFiber77Rows, listGetD, directRow] using h)

theorem tmFiber77ReverseRow_9_ok :
    tmRowReverseValid tmFiber77Key tmFiber77Expected (tmFiber77RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber77Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber77Chunk4] at h
  exact h.2

theorem tmFiber77ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber77StateAt 1) (tmFiber77StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber77StateAt 1) (tmFiber77StateAt 9)
    (tmFiber77RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber77Key tmFiber77Expected
        (tmFiber77RowAt 9) (by decide) tmFiber77ReverseRow_9_ok
      simpa [tmFiber77StateAt, tmFiber77RowAt, tmFiber77Rows, listGetD, directRow] using h)

theorem tmFiber77ReverseRow_10_ok :
    tmRowReverseValid tmFiber77Key tmFiber77Expected (tmFiber77RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber77Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber77Chunk5] at h
  exact h.1

theorem tmFiber77ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber77StateAt 2) (tmFiber77StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber77StateAt 2) (tmFiber77StateAt 10)
    (tmFiber77RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber77Key tmFiber77Expected
        (tmFiber77RowAt 10) (by decide) tmFiber77ReverseRow_10_ok
      simpa [tmFiber77StateAt, tmFiber77RowAt, tmFiber77Rows, listGetD, directRow] using h)

theorem tmFiber77ReverseRow_11_ok :
    tmRowReverseValid tmFiber77Key tmFiber77Expected (tmFiber77RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber77Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber77Chunk5] at h
  exact h.2

theorem tmFiber77ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber77StateAt 3) (tmFiber77StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber77StateAt 3) (tmFiber77StateAt 11)
    (tmFiber77RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber77Key tmFiber77Expected
        (tmFiber77RowAt 11) (by decide) tmFiber77ReverseRow_11_ok
      simpa [tmFiber77StateAt, tmFiber77RowAt, tmFiber77Rows, listGetD, directRow] using h)

theorem tmFiber77ReverseRow_12_ok :
    tmRowReverseValid tmFiber77Key tmFiber77Expected (tmFiber77RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber77Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber77Chunk6] at h
  exact h.1

theorem tmFiber77ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber77StateAt 4) (tmFiber77StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber77StateAt 4) (tmFiber77StateAt 12)
    (tmFiber77RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber77Key tmFiber77Expected
        (tmFiber77RowAt 12) (by decide) tmFiber77ReverseRow_12_ok
      simpa [tmFiber77StateAt, tmFiber77RowAt, tmFiber77Rows, listGetD, directRow] using h)

theorem tmFiber77ReverseRow_13_ok :
    tmRowReverseValid tmFiber77Key tmFiber77Expected (tmFiber77RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber77Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber77Chunk6] at h
  exact h.2

theorem tmFiber77ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber77StateAt 5) (tmFiber77StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber77StateAt 5) (tmFiber77StateAt 13)
    (tmFiber77RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber77Key tmFiber77Expected
        (tmFiber77RowAt 13) (by decide) tmFiber77ReverseRow_13_ok
      simpa [tmFiber77StateAt, tmFiber77RowAt, tmFiber77Rows, listGetD, directRow] using h)

theorem tmFiber77ReverseRow_14_ok :
    tmRowReverseValid tmFiber77Key tmFiber77Expected (tmFiber77RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber77Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber77Chunk7] at h
  exact h.1

theorem tmFiber77ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber77StateAt 6) (tmFiber77StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber77StateAt 6) (tmFiber77StateAt 14)
    (tmFiber77RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber77Key tmFiber77Expected
        (tmFiber77RowAt 14) (by decide) tmFiber77ReverseRow_14_ok
      simpa [tmFiber77StateAt, tmFiber77RowAt, tmFiber77Rows, listGetD, directRow] using h)

theorem tmFiber77ReverseRow_15_ok :
    tmRowReverseValid tmFiber77Key tmFiber77Expected (tmFiber77RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber77Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber77Chunk7] at h
  exact h.2

theorem tmFiber77ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber77StateAt 7) (tmFiber77StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber77StateAt 7) (tmFiber77StateAt 15)
    (tmFiber77RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber77Key tmFiber77Expected
        (tmFiber77RowAt 15) (by decide) tmFiber77ReverseRow_15_ok
      simpa [tmFiber77StateAt, tmFiber77RowAt, tmFiber77Rows, listGetD, directRow] using h)

theorem tmFiber77State0_in_pass1_prefix :
    tmFiber77StateAt 0 ∈ chainClosureStep tmWord [tmFiber77StateAt 0] [tmFiber77StateAt 0] := by
  exact chainClosureStep_mem_of_seen tmWord [tmFiber77StateAt 0] [tmFiber77StateAt 0] (tmFiber77StateAt 0) (by simp)

theorem tmFiber77State1_in_pass1_prefix :
    tmFiber77StateAt 1 ∈ chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1] [tmFiber77StateAt 0] := by
  have hparentBefore :
      tmFiber77StateAt 0 ∈ chainClosureStep tmWord [tmFiber77StateAt 0] [tmFiber77StateAt 0] := by
    exact tmFiber77State0_in_pass1_prefix
  rw [show [tmFiber77StateAt 0, tmFiber77StateAt 1] = [tmFiber77StateAt 0] ++ [tmFiber77StateAt 1] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber77StateAt 1) []
    (chainClosureStep tmWord [tmFiber77StateAt 0] [tmFiber77StateAt 0]) (tmFiber77StateAt 0)
    hparentBefore tmFiber77ReverseSingleStep1

theorem tmFiber77State2_in_pass1_prefix :
    tmFiber77StateAt 2 ∈ chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2] [tmFiber77StateAt 0] := by
  have hparentBefore :
      tmFiber77StateAt 1 ∈ chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1] [tmFiber77StateAt 0] := by
    exact tmFiber77State1_in_pass1_prefix
  rw [show [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2] = [tmFiber77StateAt 0, tmFiber77StateAt 1] ++ [tmFiber77StateAt 2] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber77StateAt 2) []
    (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1] [tmFiber77StateAt 0]) (tmFiber77StateAt 1)
    hparentBefore tmFiber77ReverseSingleStep2

theorem tmFiber77State3_in_pass1_prefix :
    tmFiber77StateAt 3 ∈ chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3] [tmFiber77StateAt 0] := by
  have hparentBefore :
      tmFiber77StateAt 0 ∈ chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2] [tmFiber77StateAt 0] := by
    rw [show [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2] = [tmFiber77StateAt 0] ++ [tmFiber77StateAt 1, tmFiber77StateAt 2] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber77StateAt 1, tmFiber77StateAt 2]
      (chainClosureStep tmWord [tmFiber77StateAt 0] [tmFiber77StateAt 0]) (tmFiber77StateAt 0)
      tmFiber77State0_in_pass1_prefix
  rw [show [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3] = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2] ++ [tmFiber77StateAt 3] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber77StateAt 3) []
    (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2] [tmFiber77StateAt 0]) (tmFiber77StateAt 0)
    hparentBefore tmFiber77ReverseSingleStep3

theorem tmFiber77State4_in_pass1_prefix :
    tmFiber77StateAt 4 ∈ chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4] [tmFiber77StateAt 0] := by
  have hparentBefore :
      tmFiber77StateAt 0 ∈ chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3] [tmFiber77StateAt 0] := by
    rw [show [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3] = [tmFiber77StateAt 0] ++ [tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3]
      (chainClosureStep tmWord [tmFiber77StateAt 0] [tmFiber77StateAt 0]) (tmFiber77StateAt 0)
      tmFiber77State0_in_pass1_prefix
  rw [show [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4] = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3] ++ [tmFiber77StateAt 4] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber77StateAt 4) []
    (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3] [tmFiber77StateAt 0]) (tmFiber77StateAt 0)
    hparentBefore tmFiber77ReverseSingleStep4

theorem tmFiber77State5_in_pass1_prefix :
    tmFiber77StateAt 5 ∈ chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5] [tmFiber77StateAt 0] := by
  have hparentBefore :
      tmFiber77StateAt 1 ∈ chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4] [tmFiber77StateAt 0] := by
    rw [show [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4] = [tmFiber77StateAt 0, tmFiber77StateAt 1] ++ [tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4]
      (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1] [tmFiber77StateAt 0]) (tmFiber77StateAt 1)
      tmFiber77State1_in_pass1_prefix
  rw [show [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5] = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4] ++ [tmFiber77StateAt 5] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber77StateAt 5) []
    (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4] [tmFiber77StateAt 0]) (tmFiber77StateAt 1)
    hparentBefore tmFiber77ReverseSingleStep5

theorem tmFiber77State6_in_pass1_prefix :
    tmFiber77StateAt 6 ∈ chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6] [tmFiber77StateAt 0] := by
  have hparentBefore :
      tmFiber77StateAt 2 ∈ chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5] [tmFiber77StateAt 0] := by
    rw [show [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5] = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2] ++ [tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5]
      (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2] [tmFiber77StateAt 0]) (tmFiber77StateAt 2)
      tmFiber77State2_in_pass1_prefix
  rw [show [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6] = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5] ++ [tmFiber77StateAt 6] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber77StateAt 6) []
    (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5] [tmFiber77StateAt 0]) (tmFiber77StateAt 2)
    hparentBefore tmFiber77ReverseSingleStep6

theorem tmFiber77State7_in_pass1_prefix :
    tmFiber77StateAt 7 ∈ chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7] [tmFiber77StateAt 0] := by
  have hparentBefore :
      tmFiber77StateAt 3 ∈ chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6] [tmFiber77StateAt 0] := by
    rw [show [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6] = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3] ++ [tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6]
      (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3] [tmFiber77StateAt 0]) (tmFiber77StateAt 3)
      tmFiber77State3_in_pass1_prefix
  rw [show [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7] = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6] ++ [tmFiber77StateAt 7] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber77StateAt 7) []
    (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6] [tmFiber77StateAt 0]) (tmFiber77StateAt 3)
    hparentBefore tmFiber77ReverseSingleStep7

theorem tmFiber77State8_in_pass1_prefix :
    tmFiber77StateAt 8 ∈ chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8] [tmFiber77StateAt 0] := by
  have hparentBefore :
      tmFiber77StateAt 0 ∈ chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7] [tmFiber77StateAt 0] := by
    rw [show [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7] = [tmFiber77StateAt 0] ++ [tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7]
      (chainClosureStep tmWord [tmFiber77StateAt 0] [tmFiber77StateAt 0]) (tmFiber77StateAt 0)
      tmFiber77State0_in_pass1_prefix
  rw [show [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8] = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7] ++ [tmFiber77StateAt 8] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber77StateAt 8) []
    (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7] [tmFiber77StateAt 0]) (tmFiber77StateAt 0)
    hparentBefore tmFiber77ReverseSingleStep8

theorem tmFiber77State9_in_pass1_prefix :
    tmFiber77StateAt 9 ∈ chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9] [tmFiber77StateAt 0] := by
  have hparentBefore :
      tmFiber77StateAt 1 ∈ chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8] [tmFiber77StateAt 0] := by
    rw [show [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8] = [tmFiber77StateAt 0, tmFiber77StateAt 1] ++ [tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8]
      (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1] [tmFiber77StateAt 0]) (tmFiber77StateAt 1)
      tmFiber77State1_in_pass1_prefix
  rw [show [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9] = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8] ++ [tmFiber77StateAt 9] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber77StateAt 9) []
    (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8] [tmFiber77StateAt 0]) (tmFiber77StateAt 1)
    hparentBefore tmFiber77ReverseSingleStep9

theorem tmFiber77State10_in_pass1_prefix :
    tmFiber77StateAt 10 ∈ chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10] [tmFiber77StateAt 0] := by
  have hparentBefore :
      tmFiber77StateAt 2 ∈ chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9] [tmFiber77StateAt 0] := by
    rw [show [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9] = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2] ++ [tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9]
      (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2] [tmFiber77StateAt 0]) (tmFiber77StateAt 2)
      tmFiber77State2_in_pass1_prefix
  rw [show [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10] = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9] ++ [tmFiber77StateAt 10] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber77StateAt 10) []
    (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9] [tmFiber77StateAt 0]) (tmFiber77StateAt 2)
    hparentBefore tmFiber77ReverseSingleStep10

theorem tmFiber77State11_in_pass1_prefix :
    tmFiber77StateAt 11 ∈ chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11] [tmFiber77StateAt 0] := by
  have hparentBefore :
      tmFiber77StateAt 3 ∈ chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10] [tmFiber77StateAt 0] := by
    rw [show [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10] = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3] ++ [tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10]
      (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3] [tmFiber77StateAt 0]) (tmFiber77StateAt 3)
      tmFiber77State3_in_pass1_prefix
  rw [show [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11] = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10] ++ [tmFiber77StateAt 11] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber77StateAt 11) []
    (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10] [tmFiber77StateAt 0]) (tmFiber77StateAt 3)
    hparentBefore tmFiber77ReverseSingleStep11

theorem tmFiber77State12_in_pass1_prefix :
    tmFiber77StateAt 12 ∈ chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12] [tmFiber77StateAt 0] := by
  have hparentBefore :
      tmFiber77StateAt 4 ∈ chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11] [tmFiber77StateAt 0] := by
    rw [show [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11] = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4] ++ [tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11]
      (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4] [tmFiber77StateAt 0]) (tmFiber77StateAt 4)
      tmFiber77State4_in_pass1_prefix
  rw [show [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12] = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11] ++ [tmFiber77StateAt 12] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber77StateAt 12) []
    (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11] [tmFiber77StateAt 0]) (tmFiber77StateAt 4)
    hparentBefore tmFiber77ReverseSingleStep12

theorem tmFiber77State13_in_pass1_prefix :
    tmFiber77StateAt 13 ∈ chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13] [tmFiber77StateAt 0] := by
  have hparentBefore :
      tmFiber77StateAt 5 ∈ chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12] [tmFiber77StateAt 0] := by
    rw [show [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12] = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5] ++ [tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12]
      (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5] [tmFiber77StateAt 0]) (tmFiber77StateAt 5)
      tmFiber77State5_in_pass1_prefix
  rw [show [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13] = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12] ++ [tmFiber77StateAt 13] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber77StateAt 13) []
    (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12] [tmFiber77StateAt 0]) (tmFiber77StateAt 5)
    hparentBefore tmFiber77ReverseSingleStep13

theorem tmFiber77State14_in_pass1_prefix :
    tmFiber77StateAt 14 ∈ chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14] [tmFiber77StateAt 0] := by
  have hparentBefore :
      tmFiber77StateAt 6 ∈ chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13] [tmFiber77StateAt 0] := by
    rw [show [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13] = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6] ++ [tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13]
      (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6] [tmFiber77StateAt 0]) (tmFiber77StateAt 6)
      tmFiber77State6_in_pass1_prefix
  rw [show [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14] = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13] ++ [tmFiber77StateAt 14] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber77StateAt 14) []
    (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13] [tmFiber77StateAt 0]) (tmFiber77StateAt 6)
    hparentBefore tmFiber77ReverseSingleStep14

theorem tmFiber77State15_in_pass1_prefix :
    tmFiber77StateAt 15 ∈ chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14, tmFiber77StateAt 15] [tmFiber77StateAt 0] := by
  have hparentBefore :
      tmFiber77StateAt 7 ∈ chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14] [tmFiber77StateAt 0] := by
    rw [show [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14] = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7] ++ [tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14]
      (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7] [tmFiber77StateAt 0]) (tmFiber77StateAt 7)
      tmFiber77State7_in_pass1_prefix
  rw [show [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14, tmFiber77StateAt 15] = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14] ++ [tmFiber77StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber77StateAt 15) []
    (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14] [tmFiber77StateAt 0]) (tmFiber77StateAt 7)
    hparentBefore tmFiber77ReverseSingleStep15

theorem tmFiber77State0_in_pass1_full :
    tmFiber77StateAt 0 ∈ chainClosureStep tmWord tmFiber77DirectStates [tmFiber77StateAt 0] := by
  rw [show tmFiber77DirectStates = [tmFiber77StateAt 0] ++ [tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14, tmFiber77StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14, tmFiber77StateAt 15]
    (chainClosureStep tmWord [tmFiber77StateAt 0] [tmFiber77StateAt 0]) (tmFiber77StateAt 0)
    tmFiber77State0_in_pass1_prefix

theorem tmFiber77State1_in_pass1_full :
    tmFiber77StateAt 1 ∈ chainClosureStep tmWord tmFiber77DirectStates [tmFiber77StateAt 0] := by
  rw [show tmFiber77DirectStates = [tmFiber77StateAt 0, tmFiber77StateAt 1] ++ [tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14, tmFiber77StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14, tmFiber77StateAt 15]
    (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1] [tmFiber77StateAt 0]) (tmFiber77StateAt 1)
    tmFiber77State1_in_pass1_prefix

theorem tmFiber77State2_in_pass1_full :
    tmFiber77StateAt 2 ∈ chainClosureStep tmWord tmFiber77DirectStates [tmFiber77StateAt 0] := by
  rw [show tmFiber77DirectStates = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2] ++ [tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14, tmFiber77StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14, tmFiber77StateAt 15]
    (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2] [tmFiber77StateAt 0]) (tmFiber77StateAt 2)
    tmFiber77State2_in_pass1_prefix

theorem tmFiber77State3_in_pass1_full :
    tmFiber77StateAt 3 ∈ chainClosureStep tmWord tmFiber77DirectStates [tmFiber77StateAt 0] := by
  rw [show tmFiber77DirectStates = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3] ++ [tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14, tmFiber77StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14, tmFiber77StateAt 15]
    (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3] [tmFiber77StateAt 0]) (tmFiber77StateAt 3)
    tmFiber77State3_in_pass1_prefix

theorem tmFiber77State4_in_pass1_full :
    tmFiber77StateAt 4 ∈ chainClosureStep tmWord tmFiber77DirectStates [tmFiber77StateAt 0] := by
  rw [show tmFiber77DirectStates = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4] ++ [tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14, tmFiber77StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14, tmFiber77StateAt 15]
    (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4] [tmFiber77StateAt 0]) (tmFiber77StateAt 4)
    tmFiber77State4_in_pass1_prefix

theorem tmFiber77State5_in_pass1_full :
    tmFiber77StateAt 5 ∈ chainClosureStep tmWord tmFiber77DirectStates [tmFiber77StateAt 0] := by
  rw [show tmFiber77DirectStates = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5] ++ [tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14, tmFiber77StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14, tmFiber77StateAt 15]
    (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5] [tmFiber77StateAt 0]) (tmFiber77StateAt 5)
    tmFiber77State5_in_pass1_prefix

theorem tmFiber77State6_in_pass1_full :
    tmFiber77StateAt 6 ∈ chainClosureStep tmWord tmFiber77DirectStates [tmFiber77StateAt 0] := by
  rw [show tmFiber77DirectStates = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6] ++ [tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14, tmFiber77StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14, tmFiber77StateAt 15]
    (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6] [tmFiber77StateAt 0]) (tmFiber77StateAt 6)
    tmFiber77State6_in_pass1_prefix

theorem tmFiber77State7_in_pass1_full :
    tmFiber77StateAt 7 ∈ chainClosureStep tmWord tmFiber77DirectStates [tmFiber77StateAt 0] := by
  rw [show tmFiber77DirectStates = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7] ++ [tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14, tmFiber77StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14, tmFiber77StateAt 15]
    (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7] [tmFiber77StateAt 0]) (tmFiber77StateAt 7)
    tmFiber77State7_in_pass1_prefix

theorem tmFiber77State8_in_pass1_full :
    tmFiber77StateAt 8 ∈ chainClosureStep tmWord tmFiber77DirectStates [tmFiber77StateAt 0] := by
  rw [show tmFiber77DirectStates = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8] ++ [tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14, tmFiber77StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14, tmFiber77StateAt 15]
    (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8] [tmFiber77StateAt 0]) (tmFiber77StateAt 8)
    tmFiber77State8_in_pass1_prefix

theorem tmFiber77State9_in_pass1_full :
    tmFiber77StateAt 9 ∈ chainClosureStep tmWord tmFiber77DirectStates [tmFiber77StateAt 0] := by
  rw [show tmFiber77DirectStates = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9] ++ [tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14, tmFiber77StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14, tmFiber77StateAt 15]
    (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9] [tmFiber77StateAt 0]) (tmFiber77StateAt 9)
    tmFiber77State9_in_pass1_prefix

theorem tmFiber77State10_in_pass1_full :
    tmFiber77StateAt 10 ∈ chainClosureStep tmWord tmFiber77DirectStates [tmFiber77StateAt 0] := by
  rw [show tmFiber77DirectStates = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10] ++ [tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14, tmFiber77StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14, tmFiber77StateAt 15]
    (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10] [tmFiber77StateAt 0]) (tmFiber77StateAt 10)
    tmFiber77State10_in_pass1_prefix

theorem tmFiber77State11_in_pass1_full :
    tmFiber77StateAt 11 ∈ chainClosureStep tmWord tmFiber77DirectStates [tmFiber77StateAt 0] := by
  rw [show tmFiber77DirectStates = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11] ++ [tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14, tmFiber77StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14, tmFiber77StateAt 15]
    (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11] [tmFiber77StateAt 0]) (tmFiber77StateAt 11)
    tmFiber77State11_in_pass1_prefix

theorem tmFiber77State12_in_pass1_full :
    tmFiber77StateAt 12 ∈ chainClosureStep tmWord tmFiber77DirectStates [tmFiber77StateAt 0] := by
  rw [show tmFiber77DirectStates = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12] ++ [tmFiber77StateAt 13, tmFiber77StateAt 14, tmFiber77StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber77StateAt 13, tmFiber77StateAt 14, tmFiber77StateAt 15]
    (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12] [tmFiber77StateAt 0]) (tmFiber77StateAt 12)
    tmFiber77State12_in_pass1_prefix

theorem tmFiber77State13_in_pass1_full :
    tmFiber77StateAt 13 ∈ chainClosureStep tmWord tmFiber77DirectStates [tmFiber77StateAt 0] := by
  rw [show tmFiber77DirectStates = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13] ++ [tmFiber77StateAt 14, tmFiber77StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber77StateAt 14, tmFiber77StateAt 15]
    (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13] [tmFiber77StateAt 0]) (tmFiber77StateAt 13)
    tmFiber77State13_in_pass1_prefix

theorem tmFiber77State14_in_pass1_full :
    tmFiber77StateAt 14 ∈ chainClosureStep tmWord tmFiber77DirectStates [tmFiber77StateAt 0] := by
  rw [show tmFiber77DirectStates = [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14] ++ [tmFiber77StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber77StateAt 15]
    (chainClosureStep tmWord [tmFiber77StateAt 0, tmFiber77StateAt 1, tmFiber77StateAt 2, tmFiber77StateAt 3, tmFiber77StateAt 4, tmFiber77StateAt 5, tmFiber77StateAt 6, tmFiber77StateAt 7, tmFiber77StateAt 8, tmFiber77StateAt 9, tmFiber77StateAt 10, tmFiber77StateAt 11, tmFiber77StateAt 12, tmFiber77StateAt 13, tmFiber77StateAt 14] [tmFiber77StateAt 0]) (tmFiber77StateAt 14)
    tmFiber77State14_in_pass1_prefix

theorem tmFiber77State15_in_pass1_full :
    tmFiber77StateAt 15 ∈ chainClosureStep tmWord tmFiber77DirectStates [tmFiber77StateAt 0] := by
  simpa [tmFiber77DirectStates] using tmFiber77State15_in_pass1_prefix

theorem tmFiber77State0_in_close :
    tmFiber77StateAt 0 ∈ closeChainFiber tmWord tmFiber77DirectStates tmFiber77DirectStates.length [tmFiber77StateAt 0] := by
  change tmFiber77StateAt 0 ∈ closeChainFiber tmWord tmFiber77DirectStates (15 + 1) [tmFiber77StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber77DirectStates 15 [tmFiber77StateAt 0] (tmFiber77StateAt 0) tmFiber77State0_in_pass1_full

theorem tmFiber77State1_in_close :
    tmFiber77StateAt 1 ∈ closeChainFiber tmWord tmFiber77DirectStates tmFiber77DirectStates.length [tmFiber77StateAt 0] := by
  change tmFiber77StateAt 1 ∈ closeChainFiber tmWord tmFiber77DirectStates (15 + 1) [tmFiber77StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber77DirectStates 15 [tmFiber77StateAt 0] (tmFiber77StateAt 1) tmFiber77State1_in_pass1_full

theorem tmFiber77State2_in_close :
    tmFiber77StateAt 2 ∈ closeChainFiber tmWord tmFiber77DirectStates tmFiber77DirectStates.length [tmFiber77StateAt 0] := by
  change tmFiber77StateAt 2 ∈ closeChainFiber tmWord tmFiber77DirectStates (15 + 1) [tmFiber77StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber77DirectStates 15 [tmFiber77StateAt 0] (tmFiber77StateAt 2) tmFiber77State2_in_pass1_full

theorem tmFiber77State3_in_close :
    tmFiber77StateAt 3 ∈ closeChainFiber tmWord tmFiber77DirectStates tmFiber77DirectStates.length [tmFiber77StateAt 0] := by
  change tmFiber77StateAt 3 ∈ closeChainFiber tmWord tmFiber77DirectStates (15 + 1) [tmFiber77StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber77DirectStates 15 [tmFiber77StateAt 0] (tmFiber77StateAt 3) tmFiber77State3_in_pass1_full

theorem tmFiber77State4_in_close :
    tmFiber77StateAt 4 ∈ closeChainFiber tmWord tmFiber77DirectStates tmFiber77DirectStates.length [tmFiber77StateAt 0] := by
  change tmFiber77StateAt 4 ∈ closeChainFiber tmWord tmFiber77DirectStates (15 + 1) [tmFiber77StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber77DirectStates 15 [tmFiber77StateAt 0] (tmFiber77StateAt 4) tmFiber77State4_in_pass1_full

theorem tmFiber77State5_in_close :
    tmFiber77StateAt 5 ∈ closeChainFiber tmWord tmFiber77DirectStates tmFiber77DirectStates.length [tmFiber77StateAt 0] := by
  change tmFiber77StateAt 5 ∈ closeChainFiber tmWord tmFiber77DirectStates (15 + 1) [tmFiber77StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber77DirectStates 15 [tmFiber77StateAt 0] (tmFiber77StateAt 5) tmFiber77State5_in_pass1_full

theorem tmFiber77State6_in_close :
    tmFiber77StateAt 6 ∈ closeChainFiber tmWord tmFiber77DirectStates tmFiber77DirectStates.length [tmFiber77StateAt 0] := by
  change tmFiber77StateAt 6 ∈ closeChainFiber tmWord tmFiber77DirectStates (15 + 1) [tmFiber77StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber77DirectStates 15 [tmFiber77StateAt 0] (tmFiber77StateAt 6) tmFiber77State6_in_pass1_full

theorem tmFiber77State7_in_close :
    tmFiber77StateAt 7 ∈ closeChainFiber tmWord tmFiber77DirectStates tmFiber77DirectStates.length [tmFiber77StateAt 0] := by
  change tmFiber77StateAt 7 ∈ closeChainFiber tmWord tmFiber77DirectStates (15 + 1) [tmFiber77StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber77DirectStates 15 [tmFiber77StateAt 0] (tmFiber77StateAt 7) tmFiber77State7_in_pass1_full

theorem tmFiber77State8_in_close :
    tmFiber77StateAt 8 ∈ closeChainFiber tmWord tmFiber77DirectStates tmFiber77DirectStates.length [tmFiber77StateAt 0] := by
  change tmFiber77StateAt 8 ∈ closeChainFiber tmWord tmFiber77DirectStates (15 + 1) [tmFiber77StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber77DirectStates 15 [tmFiber77StateAt 0] (tmFiber77StateAt 8) tmFiber77State8_in_pass1_full

theorem tmFiber77State9_in_close :
    tmFiber77StateAt 9 ∈ closeChainFiber tmWord tmFiber77DirectStates tmFiber77DirectStates.length [tmFiber77StateAt 0] := by
  change tmFiber77StateAt 9 ∈ closeChainFiber tmWord tmFiber77DirectStates (15 + 1) [tmFiber77StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber77DirectStates 15 [tmFiber77StateAt 0] (tmFiber77StateAt 9) tmFiber77State9_in_pass1_full

theorem tmFiber77State10_in_close :
    tmFiber77StateAt 10 ∈ closeChainFiber tmWord tmFiber77DirectStates tmFiber77DirectStates.length [tmFiber77StateAt 0] := by
  change tmFiber77StateAt 10 ∈ closeChainFiber tmWord tmFiber77DirectStates (15 + 1) [tmFiber77StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber77DirectStates 15 [tmFiber77StateAt 0] (tmFiber77StateAt 10) tmFiber77State10_in_pass1_full

theorem tmFiber77State11_in_close :
    tmFiber77StateAt 11 ∈ closeChainFiber tmWord tmFiber77DirectStates tmFiber77DirectStates.length [tmFiber77StateAt 0] := by
  change tmFiber77StateAt 11 ∈ closeChainFiber tmWord tmFiber77DirectStates (15 + 1) [tmFiber77StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber77DirectStates 15 [tmFiber77StateAt 0] (tmFiber77StateAt 11) tmFiber77State11_in_pass1_full

theorem tmFiber77State12_in_close :
    tmFiber77StateAt 12 ∈ closeChainFiber tmWord tmFiber77DirectStates tmFiber77DirectStates.length [tmFiber77StateAt 0] := by
  change tmFiber77StateAt 12 ∈ closeChainFiber tmWord tmFiber77DirectStates (15 + 1) [tmFiber77StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber77DirectStates 15 [tmFiber77StateAt 0] (tmFiber77StateAt 12) tmFiber77State12_in_pass1_full

theorem tmFiber77State13_in_close :
    tmFiber77StateAt 13 ∈ closeChainFiber tmWord tmFiber77DirectStates tmFiber77DirectStates.length [tmFiber77StateAt 0] := by
  change tmFiber77StateAt 13 ∈ closeChainFiber tmWord tmFiber77DirectStates (15 + 1) [tmFiber77StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber77DirectStates 15 [tmFiber77StateAt 0] (tmFiber77StateAt 13) tmFiber77State13_in_pass1_full

theorem tmFiber77State14_in_close :
    tmFiber77StateAt 14 ∈ closeChainFiber tmWord tmFiber77DirectStates tmFiber77DirectStates.length [tmFiber77StateAt 0] := by
  change tmFiber77StateAt 14 ∈ closeChainFiber tmWord tmFiber77DirectStates (15 + 1) [tmFiber77StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber77DirectStates 15 [tmFiber77StateAt 0] (tmFiber77StateAt 14) tmFiber77State14_in_pass1_full

theorem tmFiber77State15_in_close :
    tmFiber77StateAt 15 ∈ closeChainFiber tmWord tmFiber77DirectStates tmFiber77DirectStates.length [tmFiber77StateAt 0] := by
  change tmFiber77StateAt 15 ∈ closeChainFiber tmWord tmFiber77DirectStates (15 + 1) [tmFiber77StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber77DirectStates 15 [tmFiber77StateAt 0] (tmFiber77StateAt 15) tmFiber77State15_in_pass1_full

theorem tmFiber77DirectConnected :
    chainFiberConnected tmWord tmFiber77DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber77DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber77State0_in_close
  · subst state
    exact tmFiber77State1_in_close
  · subst state
    exact tmFiber77State2_in_close
  · subst state
    exact tmFiber77State3_in_close
  · subst state
    exact tmFiber77State4_in_close
  · subst state
    exact tmFiber77State5_in_close
  · subst state
    exact tmFiber77State6_in_close
  · subst state
    exact tmFiber77State7_in_close
  · subst state
    exact tmFiber77State8_in_close
  · subst state
    exact tmFiber77State9_in_close
  · subst state
    exact tmFiber77State10_in_close
  · subst state
    exact tmFiber77State11_in_close
  · subst state
    exact tmFiber77State12_in_close
  · subst state
    exact tmFiber77State13_in_close
  · subst state
    exact tmFiber77State14_in_close
  · subst state
    exact tmFiber77State15_in_close
  · cases h

end GoertzelLemma818LengthTwoTMShape16Bridge

end Mettapedia.GraphTheory.FourColor
