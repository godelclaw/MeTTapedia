import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated direct closure bridge for size-16 `normal,mirror` length-two fibers, group 1

This module proves direct connectedness for four generated `normal,mirror`
size-16 fibers from row-local reverse certificate chunks, keeping Lean on
default recursion limits.
-/

namespace GoertzelLemma818LengthTwoTMShape16Bridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818TauMirrorCertificate
open GoertzelLemma818TauMirrorReverseAudit

def tmFiber9StateAt (i : Nat) : List TauState :=
  directStates (tmFiber9RowAt i).sourceLeft (tmFiber9RowAt i).sourceRight

def tmFiber9DirectStates : List (List TauState) :=
  [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14, tmFiber9StateAt 15]

theorem tmFiber9ReverseRow_1_ok :
    tmRowReverseValid tmFiber9Key tmFiber9Expected (tmFiber9RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber9Chunk0_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber9Chunk0] at h
  exact h.2

theorem tmFiber9ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber9StateAt 0) (tmFiber9StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber9StateAt 0) (tmFiber9StateAt 1)
    (tmFiber9RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber9Key tmFiber9Expected
        (tmFiber9RowAt 1) (by decide) tmFiber9ReverseRow_1_ok
      simpa [tmFiber9StateAt, tmFiber9RowAt, tmFiber9Rows, listGetD, directRow] using h)

theorem tmFiber9ReverseRow_2_ok :
    tmRowReverseValid tmFiber9Key tmFiber9Expected (tmFiber9RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber9Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber9Chunk1] at h
  exact h.1

theorem tmFiber9ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber9StateAt 1) (tmFiber9StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber9StateAt 1) (tmFiber9StateAt 2)
    (tmFiber9RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber9Key tmFiber9Expected
        (tmFiber9RowAt 2) (by decide) tmFiber9ReverseRow_2_ok
      simpa [tmFiber9StateAt, tmFiber9RowAt, tmFiber9Rows, listGetD, directRow] using h)

theorem tmFiber9ReverseRow_3_ok :
    tmRowReverseValid tmFiber9Key tmFiber9Expected (tmFiber9RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber9Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber9Chunk1] at h
  exact h.2

theorem tmFiber9ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber9StateAt 0) (tmFiber9StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber9StateAt 0) (tmFiber9StateAt 3)
    (tmFiber9RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber9Key tmFiber9Expected
        (tmFiber9RowAt 3) (by decide) tmFiber9ReverseRow_3_ok
      simpa [tmFiber9StateAt, tmFiber9RowAt, tmFiber9Rows, listGetD, directRow] using h)

theorem tmFiber9ReverseRow_4_ok :
    tmRowReverseValid tmFiber9Key tmFiber9Expected (tmFiber9RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber9Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber9Chunk2] at h
  exact h.1

theorem tmFiber9ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber9StateAt 0) (tmFiber9StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber9StateAt 0) (tmFiber9StateAt 4)
    (tmFiber9RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber9Key tmFiber9Expected
        (tmFiber9RowAt 4) (by decide) tmFiber9ReverseRow_4_ok
      simpa [tmFiber9StateAt, tmFiber9RowAt, tmFiber9Rows, listGetD, directRow] using h)

theorem tmFiber9ReverseRow_5_ok :
    tmRowReverseValid tmFiber9Key tmFiber9Expected (tmFiber9RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber9Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber9Chunk2] at h
  exact h.2

theorem tmFiber9ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber9StateAt 1) (tmFiber9StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber9StateAt 1) (tmFiber9StateAt 5)
    (tmFiber9RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber9Key tmFiber9Expected
        (tmFiber9RowAt 5) (by decide) tmFiber9ReverseRow_5_ok
      simpa [tmFiber9StateAt, tmFiber9RowAt, tmFiber9Rows, listGetD, directRow] using h)

theorem tmFiber9ReverseRow_6_ok :
    tmRowReverseValid tmFiber9Key tmFiber9Expected (tmFiber9RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber9Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber9Chunk3] at h
  exact h.1

theorem tmFiber9ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber9StateAt 2) (tmFiber9StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber9StateAt 2) (tmFiber9StateAt 6)
    (tmFiber9RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber9Key tmFiber9Expected
        (tmFiber9RowAt 6) (by decide) tmFiber9ReverseRow_6_ok
      simpa [tmFiber9StateAt, tmFiber9RowAt, tmFiber9Rows, listGetD, directRow] using h)

theorem tmFiber9ReverseRow_7_ok :
    tmRowReverseValid tmFiber9Key tmFiber9Expected (tmFiber9RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber9Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber9Chunk3] at h
  exact h.2

theorem tmFiber9ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber9StateAt 3) (tmFiber9StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber9StateAt 3) (tmFiber9StateAt 7)
    (tmFiber9RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber9Key tmFiber9Expected
        (tmFiber9RowAt 7) (by decide) tmFiber9ReverseRow_7_ok
      simpa [tmFiber9StateAt, tmFiber9RowAt, tmFiber9Rows, listGetD, directRow] using h)

theorem tmFiber9ReverseRow_8_ok :
    tmRowReverseValid tmFiber9Key tmFiber9Expected (tmFiber9RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber9Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber9Chunk4] at h
  exact h.1

theorem tmFiber9ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber9StateAt 0) (tmFiber9StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber9StateAt 0) (tmFiber9StateAt 8)
    (tmFiber9RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber9Key tmFiber9Expected
        (tmFiber9RowAt 8) (by decide) tmFiber9ReverseRow_8_ok
      simpa [tmFiber9StateAt, tmFiber9RowAt, tmFiber9Rows, listGetD, directRow] using h)

theorem tmFiber9ReverseRow_9_ok :
    tmRowReverseValid tmFiber9Key tmFiber9Expected (tmFiber9RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber9Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber9Chunk4] at h
  exact h.2

theorem tmFiber9ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber9StateAt 1) (tmFiber9StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber9StateAt 1) (tmFiber9StateAt 9)
    (tmFiber9RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber9Key tmFiber9Expected
        (tmFiber9RowAt 9) (by decide) tmFiber9ReverseRow_9_ok
      simpa [tmFiber9StateAt, tmFiber9RowAt, tmFiber9Rows, listGetD, directRow] using h)

theorem tmFiber9ReverseRow_10_ok :
    tmRowReverseValid tmFiber9Key tmFiber9Expected (tmFiber9RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber9Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber9Chunk5] at h
  exact h.1

theorem tmFiber9ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber9StateAt 2) (tmFiber9StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber9StateAt 2) (tmFiber9StateAt 10)
    (tmFiber9RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber9Key tmFiber9Expected
        (tmFiber9RowAt 10) (by decide) tmFiber9ReverseRow_10_ok
      simpa [tmFiber9StateAt, tmFiber9RowAt, tmFiber9Rows, listGetD, directRow] using h)

theorem tmFiber9ReverseRow_11_ok :
    tmRowReverseValid tmFiber9Key tmFiber9Expected (tmFiber9RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber9Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber9Chunk5] at h
  exact h.2

theorem tmFiber9ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber9StateAt 3) (tmFiber9StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber9StateAt 3) (tmFiber9StateAt 11)
    (tmFiber9RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber9Key tmFiber9Expected
        (tmFiber9RowAt 11) (by decide) tmFiber9ReverseRow_11_ok
      simpa [tmFiber9StateAt, tmFiber9RowAt, tmFiber9Rows, listGetD, directRow] using h)

theorem tmFiber9ReverseRow_12_ok :
    tmRowReverseValid tmFiber9Key tmFiber9Expected (tmFiber9RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber9Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber9Chunk6] at h
  exact h.1

theorem tmFiber9ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber9StateAt 4) (tmFiber9StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber9StateAt 4) (tmFiber9StateAt 12)
    (tmFiber9RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber9Key tmFiber9Expected
        (tmFiber9RowAt 12) (by decide) tmFiber9ReverseRow_12_ok
      simpa [tmFiber9StateAt, tmFiber9RowAt, tmFiber9Rows, listGetD, directRow] using h)

theorem tmFiber9ReverseRow_13_ok :
    tmRowReverseValid tmFiber9Key tmFiber9Expected (tmFiber9RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber9Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber9Chunk6] at h
  exact h.2

theorem tmFiber9ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber9StateAt 5) (tmFiber9StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber9StateAt 5) (tmFiber9StateAt 13)
    (tmFiber9RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber9Key tmFiber9Expected
        (tmFiber9RowAt 13) (by decide) tmFiber9ReverseRow_13_ok
      simpa [tmFiber9StateAt, tmFiber9RowAt, tmFiber9Rows, listGetD, directRow] using h)

theorem tmFiber9ReverseRow_14_ok :
    tmRowReverseValid tmFiber9Key tmFiber9Expected (tmFiber9RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber9Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber9Chunk7] at h
  exact h.1

theorem tmFiber9ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber9StateAt 6) (tmFiber9StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber9StateAt 6) (tmFiber9StateAt 14)
    (tmFiber9RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber9Key tmFiber9Expected
        (tmFiber9RowAt 14) (by decide) tmFiber9ReverseRow_14_ok
      simpa [tmFiber9StateAt, tmFiber9RowAt, tmFiber9Rows, listGetD, directRow] using h)

theorem tmFiber9ReverseRow_15_ok :
    tmRowReverseValid tmFiber9Key tmFiber9Expected (tmFiber9RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber9Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber9Chunk7] at h
  exact h.2

theorem tmFiber9ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber9StateAt 7) (tmFiber9StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber9StateAt 7) (tmFiber9StateAt 15)
    (tmFiber9RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber9Key tmFiber9Expected
        (tmFiber9RowAt 15) (by decide) tmFiber9ReverseRow_15_ok
      simpa [tmFiber9StateAt, tmFiber9RowAt, tmFiber9Rows, listGetD, directRow] using h)

theorem tmFiber9State0_in_pass1_prefix :
    tmFiber9StateAt 0 ∈ chainClosureStep tmWord [tmFiber9StateAt 0] [tmFiber9StateAt 0] := by
  exact chainClosureStep_mem_of_seen tmWord [tmFiber9StateAt 0] [tmFiber9StateAt 0] (tmFiber9StateAt 0) (by simp)

theorem tmFiber9State1_in_pass1_prefix :
    tmFiber9StateAt 1 ∈ chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1] [tmFiber9StateAt 0] := by
  have hparentBefore :
      tmFiber9StateAt 0 ∈ chainClosureStep tmWord [tmFiber9StateAt 0] [tmFiber9StateAt 0] := by
    exact tmFiber9State0_in_pass1_prefix
  rw [show [tmFiber9StateAt 0, tmFiber9StateAt 1] = [tmFiber9StateAt 0] ++ [tmFiber9StateAt 1] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber9StateAt 1) []
    (chainClosureStep tmWord [tmFiber9StateAt 0] [tmFiber9StateAt 0]) (tmFiber9StateAt 0)
    hparentBefore tmFiber9ReverseSingleStep1

theorem tmFiber9State2_in_pass1_prefix :
    tmFiber9StateAt 2 ∈ chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2] [tmFiber9StateAt 0] := by
  have hparentBefore :
      tmFiber9StateAt 1 ∈ chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1] [tmFiber9StateAt 0] := by
    exact tmFiber9State1_in_pass1_prefix
  rw [show [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2] = [tmFiber9StateAt 0, tmFiber9StateAt 1] ++ [tmFiber9StateAt 2] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber9StateAt 2) []
    (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1] [tmFiber9StateAt 0]) (tmFiber9StateAt 1)
    hparentBefore tmFiber9ReverseSingleStep2

theorem tmFiber9State3_in_pass1_prefix :
    tmFiber9StateAt 3 ∈ chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3] [tmFiber9StateAt 0] := by
  have hparentBefore :
      tmFiber9StateAt 0 ∈ chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2] [tmFiber9StateAt 0] := by
    rw [show [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2] = [tmFiber9StateAt 0] ++ [tmFiber9StateAt 1, tmFiber9StateAt 2] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber9StateAt 1, tmFiber9StateAt 2]
      (chainClosureStep tmWord [tmFiber9StateAt 0] [tmFiber9StateAt 0]) (tmFiber9StateAt 0)
      tmFiber9State0_in_pass1_prefix
  rw [show [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3] = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2] ++ [tmFiber9StateAt 3] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber9StateAt 3) []
    (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2] [tmFiber9StateAt 0]) (tmFiber9StateAt 0)
    hparentBefore tmFiber9ReverseSingleStep3

theorem tmFiber9State4_in_pass1_prefix :
    tmFiber9StateAt 4 ∈ chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4] [tmFiber9StateAt 0] := by
  have hparentBefore :
      tmFiber9StateAt 0 ∈ chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3] [tmFiber9StateAt 0] := by
    rw [show [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3] = [tmFiber9StateAt 0] ++ [tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3]
      (chainClosureStep tmWord [tmFiber9StateAt 0] [tmFiber9StateAt 0]) (tmFiber9StateAt 0)
      tmFiber9State0_in_pass1_prefix
  rw [show [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4] = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3] ++ [tmFiber9StateAt 4] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber9StateAt 4) []
    (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3] [tmFiber9StateAt 0]) (tmFiber9StateAt 0)
    hparentBefore tmFiber9ReverseSingleStep4

theorem tmFiber9State5_in_pass1_prefix :
    tmFiber9StateAt 5 ∈ chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5] [tmFiber9StateAt 0] := by
  have hparentBefore :
      tmFiber9StateAt 1 ∈ chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4] [tmFiber9StateAt 0] := by
    rw [show [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4] = [tmFiber9StateAt 0, tmFiber9StateAt 1] ++ [tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4]
      (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1] [tmFiber9StateAt 0]) (tmFiber9StateAt 1)
      tmFiber9State1_in_pass1_prefix
  rw [show [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5] = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4] ++ [tmFiber9StateAt 5] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber9StateAt 5) []
    (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4] [tmFiber9StateAt 0]) (tmFiber9StateAt 1)
    hparentBefore tmFiber9ReverseSingleStep5

theorem tmFiber9State6_in_pass1_prefix :
    tmFiber9StateAt 6 ∈ chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6] [tmFiber9StateAt 0] := by
  have hparentBefore :
      tmFiber9StateAt 2 ∈ chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5] [tmFiber9StateAt 0] := by
    rw [show [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5] = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2] ++ [tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5]
      (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2] [tmFiber9StateAt 0]) (tmFiber9StateAt 2)
      tmFiber9State2_in_pass1_prefix
  rw [show [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6] = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5] ++ [tmFiber9StateAt 6] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber9StateAt 6) []
    (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5] [tmFiber9StateAt 0]) (tmFiber9StateAt 2)
    hparentBefore tmFiber9ReverseSingleStep6

theorem tmFiber9State7_in_pass1_prefix :
    tmFiber9StateAt 7 ∈ chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7] [tmFiber9StateAt 0] := by
  have hparentBefore :
      tmFiber9StateAt 3 ∈ chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6] [tmFiber9StateAt 0] := by
    rw [show [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6] = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3] ++ [tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6]
      (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3] [tmFiber9StateAt 0]) (tmFiber9StateAt 3)
      tmFiber9State3_in_pass1_prefix
  rw [show [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7] = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6] ++ [tmFiber9StateAt 7] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber9StateAt 7) []
    (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6] [tmFiber9StateAt 0]) (tmFiber9StateAt 3)
    hparentBefore tmFiber9ReverseSingleStep7

theorem tmFiber9State8_in_pass1_prefix :
    tmFiber9StateAt 8 ∈ chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8] [tmFiber9StateAt 0] := by
  have hparentBefore :
      tmFiber9StateAt 0 ∈ chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7] [tmFiber9StateAt 0] := by
    rw [show [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7] = [tmFiber9StateAt 0] ++ [tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7]
      (chainClosureStep tmWord [tmFiber9StateAt 0] [tmFiber9StateAt 0]) (tmFiber9StateAt 0)
      tmFiber9State0_in_pass1_prefix
  rw [show [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8] = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7] ++ [tmFiber9StateAt 8] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber9StateAt 8) []
    (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7] [tmFiber9StateAt 0]) (tmFiber9StateAt 0)
    hparentBefore tmFiber9ReverseSingleStep8

theorem tmFiber9State9_in_pass1_prefix :
    tmFiber9StateAt 9 ∈ chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9] [tmFiber9StateAt 0] := by
  have hparentBefore :
      tmFiber9StateAt 1 ∈ chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8] [tmFiber9StateAt 0] := by
    rw [show [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8] = [tmFiber9StateAt 0, tmFiber9StateAt 1] ++ [tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8]
      (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1] [tmFiber9StateAt 0]) (tmFiber9StateAt 1)
      tmFiber9State1_in_pass1_prefix
  rw [show [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9] = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8] ++ [tmFiber9StateAt 9] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber9StateAt 9) []
    (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8] [tmFiber9StateAt 0]) (tmFiber9StateAt 1)
    hparentBefore tmFiber9ReverseSingleStep9

theorem tmFiber9State10_in_pass1_prefix :
    tmFiber9StateAt 10 ∈ chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10] [tmFiber9StateAt 0] := by
  have hparentBefore :
      tmFiber9StateAt 2 ∈ chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9] [tmFiber9StateAt 0] := by
    rw [show [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9] = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2] ++ [tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9]
      (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2] [tmFiber9StateAt 0]) (tmFiber9StateAt 2)
      tmFiber9State2_in_pass1_prefix
  rw [show [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10] = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9] ++ [tmFiber9StateAt 10] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber9StateAt 10) []
    (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9] [tmFiber9StateAt 0]) (tmFiber9StateAt 2)
    hparentBefore tmFiber9ReverseSingleStep10

theorem tmFiber9State11_in_pass1_prefix :
    tmFiber9StateAt 11 ∈ chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11] [tmFiber9StateAt 0] := by
  have hparentBefore :
      tmFiber9StateAt 3 ∈ chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10] [tmFiber9StateAt 0] := by
    rw [show [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10] = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3] ++ [tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10]
      (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3] [tmFiber9StateAt 0]) (tmFiber9StateAt 3)
      tmFiber9State3_in_pass1_prefix
  rw [show [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11] = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10] ++ [tmFiber9StateAt 11] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber9StateAt 11) []
    (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10] [tmFiber9StateAt 0]) (tmFiber9StateAt 3)
    hparentBefore tmFiber9ReverseSingleStep11

theorem tmFiber9State12_in_pass1_prefix :
    tmFiber9StateAt 12 ∈ chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12] [tmFiber9StateAt 0] := by
  have hparentBefore :
      tmFiber9StateAt 4 ∈ chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11] [tmFiber9StateAt 0] := by
    rw [show [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11] = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4] ++ [tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11]
      (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4] [tmFiber9StateAt 0]) (tmFiber9StateAt 4)
      tmFiber9State4_in_pass1_prefix
  rw [show [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12] = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11] ++ [tmFiber9StateAt 12] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber9StateAt 12) []
    (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11] [tmFiber9StateAt 0]) (tmFiber9StateAt 4)
    hparentBefore tmFiber9ReverseSingleStep12

theorem tmFiber9State13_in_pass1_prefix :
    tmFiber9StateAt 13 ∈ chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13] [tmFiber9StateAt 0] := by
  have hparentBefore :
      tmFiber9StateAt 5 ∈ chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12] [tmFiber9StateAt 0] := by
    rw [show [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12] = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5] ++ [tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12]
      (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5] [tmFiber9StateAt 0]) (tmFiber9StateAt 5)
      tmFiber9State5_in_pass1_prefix
  rw [show [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13] = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12] ++ [tmFiber9StateAt 13] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber9StateAt 13) []
    (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12] [tmFiber9StateAt 0]) (tmFiber9StateAt 5)
    hparentBefore tmFiber9ReverseSingleStep13

theorem tmFiber9State14_in_pass1_prefix :
    tmFiber9StateAt 14 ∈ chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14] [tmFiber9StateAt 0] := by
  have hparentBefore :
      tmFiber9StateAt 6 ∈ chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13] [tmFiber9StateAt 0] := by
    rw [show [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13] = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6] ++ [tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13]
      (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6] [tmFiber9StateAt 0]) (tmFiber9StateAt 6)
      tmFiber9State6_in_pass1_prefix
  rw [show [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14] = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13] ++ [tmFiber9StateAt 14] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber9StateAt 14) []
    (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13] [tmFiber9StateAt 0]) (tmFiber9StateAt 6)
    hparentBefore tmFiber9ReverseSingleStep14

theorem tmFiber9State15_in_pass1_prefix :
    tmFiber9StateAt 15 ∈ chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14, tmFiber9StateAt 15] [tmFiber9StateAt 0] := by
  have hparentBefore :
      tmFiber9StateAt 7 ∈ chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14] [tmFiber9StateAt 0] := by
    rw [show [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14] = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7] ++ [tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14]
      (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7] [tmFiber9StateAt 0]) (tmFiber9StateAt 7)
      tmFiber9State7_in_pass1_prefix
  rw [show [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14, tmFiber9StateAt 15] = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14] ++ [tmFiber9StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber9StateAt 15) []
    (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14] [tmFiber9StateAt 0]) (tmFiber9StateAt 7)
    hparentBefore tmFiber9ReverseSingleStep15

theorem tmFiber9State0_in_pass1_full :
    tmFiber9StateAt 0 ∈ chainClosureStep tmWord tmFiber9DirectStates [tmFiber9StateAt 0] := by
  rw [show tmFiber9DirectStates = [tmFiber9StateAt 0] ++ [tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14, tmFiber9StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14, tmFiber9StateAt 15]
    (chainClosureStep tmWord [tmFiber9StateAt 0] [tmFiber9StateAt 0]) (tmFiber9StateAt 0)
    tmFiber9State0_in_pass1_prefix

theorem tmFiber9State1_in_pass1_full :
    tmFiber9StateAt 1 ∈ chainClosureStep tmWord tmFiber9DirectStates [tmFiber9StateAt 0] := by
  rw [show tmFiber9DirectStates = [tmFiber9StateAt 0, tmFiber9StateAt 1] ++ [tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14, tmFiber9StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14, tmFiber9StateAt 15]
    (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1] [tmFiber9StateAt 0]) (tmFiber9StateAt 1)
    tmFiber9State1_in_pass1_prefix

theorem tmFiber9State2_in_pass1_full :
    tmFiber9StateAt 2 ∈ chainClosureStep tmWord tmFiber9DirectStates [tmFiber9StateAt 0] := by
  rw [show tmFiber9DirectStates = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2] ++ [tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14, tmFiber9StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14, tmFiber9StateAt 15]
    (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2] [tmFiber9StateAt 0]) (tmFiber9StateAt 2)
    tmFiber9State2_in_pass1_prefix

theorem tmFiber9State3_in_pass1_full :
    tmFiber9StateAt 3 ∈ chainClosureStep tmWord tmFiber9DirectStates [tmFiber9StateAt 0] := by
  rw [show tmFiber9DirectStates = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3] ++ [tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14, tmFiber9StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14, tmFiber9StateAt 15]
    (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3] [tmFiber9StateAt 0]) (tmFiber9StateAt 3)
    tmFiber9State3_in_pass1_prefix

theorem tmFiber9State4_in_pass1_full :
    tmFiber9StateAt 4 ∈ chainClosureStep tmWord tmFiber9DirectStates [tmFiber9StateAt 0] := by
  rw [show tmFiber9DirectStates = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4] ++ [tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14, tmFiber9StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14, tmFiber9StateAt 15]
    (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4] [tmFiber9StateAt 0]) (tmFiber9StateAt 4)
    tmFiber9State4_in_pass1_prefix

theorem tmFiber9State5_in_pass1_full :
    tmFiber9StateAt 5 ∈ chainClosureStep tmWord tmFiber9DirectStates [tmFiber9StateAt 0] := by
  rw [show tmFiber9DirectStates = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5] ++ [tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14, tmFiber9StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14, tmFiber9StateAt 15]
    (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5] [tmFiber9StateAt 0]) (tmFiber9StateAt 5)
    tmFiber9State5_in_pass1_prefix

theorem tmFiber9State6_in_pass1_full :
    tmFiber9StateAt 6 ∈ chainClosureStep tmWord tmFiber9DirectStates [tmFiber9StateAt 0] := by
  rw [show tmFiber9DirectStates = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6] ++ [tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14, tmFiber9StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14, tmFiber9StateAt 15]
    (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6] [tmFiber9StateAt 0]) (tmFiber9StateAt 6)
    tmFiber9State6_in_pass1_prefix

theorem tmFiber9State7_in_pass1_full :
    tmFiber9StateAt 7 ∈ chainClosureStep tmWord tmFiber9DirectStates [tmFiber9StateAt 0] := by
  rw [show tmFiber9DirectStates = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7] ++ [tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14, tmFiber9StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14, tmFiber9StateAt 15]
    (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7] [tmFiber9StateAt 0]) (tmFiber9StateAt 7)
    tmFiber9State7_in_pass1_prefix

theorem tmFiber9State8_in_pass1_full :
    tmFiber9StateAt 8 ∈ chainClosureStep tmWord tmFiber9DirectStates [tmFiber9StateAt 0] := by
  rw [show tmFiber9DirectStates = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8] ++ [tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14, tmFiber9StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14, tmFiber9StateAt 15]
    (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8] [tmFiber9StateAt 0]) (tmFiber9StateAt 8)
    tmFiber9State8_in_pass1_prefix

theorem tmFiber9State9_in_pass1_full :
    tmFiber9StateAt 9 ∈ chainClosureStep tmWord tmFiber9DirectStates [tmFiber9StateAt 0] := by
  rw [show tmFiber9DirectStates = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9] ++ [tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14, tmFiber9StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14, tmFiber9StateAt 15]
    (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9] [tmFiber9StateAt 0]) (tmFiber9StateAt 9)
    tmFiber9State9_in_pass1_prefix

theorem tmFiber9State10_in_pass1_full :
    tmFiber9StateAt 10 ∈ chainClosureStep tmWord tmFiber9DirectStates [tmFiber9StateAt 0] := by
  rw [show tmFiber9DirectStates = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10] ++ [tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14, tmFiber9StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14, tmFiber9StateAt 15]
    (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10] [tmFiber9StateAt 0]) (tmFiber9StateAt 10)
    tmFiber9State10_in_pass1_prefix

theorem tmFiber9State11_in_pass1_full :
    tmFiber9StateAt 11 ∈ chainClosureStep tmWord tmFiber9DirectStates [tmFiber9StateAt 0] := by
  rw [show tmFiber9DirectStates = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11] ++ [tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14, tmFiber9StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14, tmFiber9StateAt 15]
    (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11] [tmFiber9StateAt 0]) (tmFiber9StateAt 11)
    tmFiber9State11_in_pass1_prefix

theorem tmFiber9State12_in_pass1_full :
    tmFiber9StateAt 12 ∈ chainClosureStep tmWord tmFiber9DirectStates [tmFiber9StateAt 0] := by
  rw [show tmFiber9DirectStates = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12] ++ [tmFiber9StateAt 13, tmFiber9StateAt 14, tmFiber9StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber9StateAt 13, tmFiber9StateAt 14, tmFiber9StateAt 15]
    (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12] [tmFiber9StateAt 0]) (tmFiber9StateAt 12)
    tmFiber9State12_in_pass1_prefix

theorem tmFiber9State13_in_pass1_full :
    tmFiber9StateAt 13 ∈ chainClosureStep tmWord tmFiber9DirectStates [tmFiber9StateAt 0] := by
  rw [show tmFiber9DirectStates = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13] ++ [tmFiber9StateAt 14, tmFiber9StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber9StateAt 14, tmFiber9StateAt 15]
    (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13] [tmFiber9StateAt 0]) (tmFiber9StateAt 13)
    tmFiber9State13_in_pass1_prefix

theorem tmFiber9State14_in_pass1_full :
    tmFiber9StateAt 14 ∈ chainClosureStep tmWord tmFiber9DirectStates [tmFiber9StateAt 0] := by
  rw [show tmFiber9DirectStates = [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14] ++ [tmFiber9StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber9StateAt 15]
    (chainClosureStep tmWord [tmFiber9StateAt 0, tmFiber9StateAt 1, tmFiber9StateAt 2, tmFiber9StateAt 3, tmFiber9StateAt 4, tmFiber9StateAt 5, tmFiber9StateAt 6, tmFiber9StateAt 7, tmFiber9StateAt 8, tmFiber9StateAt 9, tmFiber9StateAt 10, tmFiber9StateAt 11, tmFiber9StateAt 12, tmFiber9StateAt 13, tmFiber9StateAt 14] [tmFiber9StateAt 0]) (tmFiber9StateAt 14)
    tmFiber9State14_in_pass1_prefix

theorem tmFiber9State15_in_pass1_full :
    tmFiber9StateAt 15 ∈ chainClosureStep tmWord tmFiber9DirectStates [tmFiber9StateAt 0] := by
  simpa [tmFiber9DirectStates] using tmFiber9State15_in_pass1_prefix

theorem tmFiber9State0_in_close :
    tmFiber9StateAt 0 ∈ closeChainFiber tmWord tmFiber9DirectStates tmFiber9DirectStates.length [tmFiber9StateAt 0] := by
  change tmFiber9StateAt 0 ∈ closeChainFiber tmWord tmFiber9DirectStates (15 + 1) [tmFiber9StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber9DirectStates 15 [tmFiber9StateAt 0] (tmFiber9StateAt 0) tmFiber9State0_in_pass1_full

theorem tmFiber9State1_in_close :
    tmFiber9StateAt 1 ∈ closeChainFiber tmWord tmFiber9DirectStates tmFiber9DirectStates.length [tmFiber9StateAt 0] := by
  change tmFiber9StateAt 1 ∈ closeChainFiber tmWord tmFiber9DirectStates (15 + 1) [tmFiber9StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber9DirectStates 15 [tmFiber9StateAt 0] (tmFiber9StateAt 1) tmFiber9State1_in_pass1_full

theorem tmFiber9State2_in_close :
    tmFiber9StateAt 2 ∈ closeChainFiber tmWord tmFiber9DirectStates tmFiber9DirectStates.length [tmFiber9StateAt 0] := by
  change tmFiber9StateAt 2 ∈ closeChainFiber tmWord tmFiber9DirectStates (15 + 1) [tmFiber9StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber9DirectStates 15 [tmFiber9StateAt 0] (tmFiber9StateAt 2) tmFiber9State2_in_pass1_full

theorem tmFiber9State3_in_close :
    tmFiber9StateAt 3 ∈ closeChainFiber tmWord tmFiber9DirectStates tmFiber9DirectStates.length [tmFiber9StateAt 0] := by
  change tmFiber9StateAt 3 ∈ closeChainFiber tmWord tmFiber9DirectStates (15 + 1) [tmFiber9StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber9DirectStates 15 [tmFiber9StateAt 0] (tmFiber9StateAt 3) tmFiber9State3_in_pass1_full

theorem tmFiber9State4_in_close :
    tmFiber9StateAt 4 ∈ closeChainFiber tmWord tmFiber9DirectStates tmFiber9DirectStates.length [tmFiber9StateAt 0] := by
  change tmFiber9StateAt 4 ∈ closeChainFiber tmWord tmFiber9DirectStates (15 + 1) [tmFiber9StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber9DirectStates 15 [tmFiber9StateAt 0] (tmFiber9StateAt 4) tmFiber9State4_in_pass1_full

theorem tmFiber9State5_in_close :
    tmFiber9StateAt 5 ∈ closeChainFiber tmWord tmFiber9DirectStates tmFiber9DirectStates.length [tmFiber9StateAt 0] := by
  change tmFiber9StateAt 5 ∈ closeChainFiber tmWord tmFiber9DirectStates (15 + 1) [tmFiber9StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber9DirectStates 15 [tmFiber9StateAt 0] (tmFiber9StateAt 5) tmFiber9State5_in_pass1_full

theorem tmFiber9State6_in_close :
    tmFiber9StateAt 6 ∈ closeChainFiber tmWord tmFiber9DirectStates tmFiber9DirectStates.length [tmFiber9StateAt 0] := by
  change tmFiber9StateAt 6 ∈ closeChainFiber tmWord tmFiber9DirectStates (15 + 1) [tmFiber9StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber9DirectStates 15 [tmFiber9StateAt 0] (tmFiber9StateAt 6) tmFiber9State6_in_pass1_full

theorem tmFiber9State7_in_close :
    tmFiber9StateAt 7 ∈ closeChainFiber tmWord tmFiber9DirectStates tmFiber9DirectStates.length [tmFiber9StateAt 0] := by
  change tmFiber9StateAt 7 ∈ closeChainFiber tmWord tmFiber9DirectStates (15 + 1) [tmFiber9StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber9DirectStates 15 [tmFiber9StateAt 0] (tmFiber9StateAt 7) tmFiber9State7_in_pass1_full

theorem tmFiber9State8_in_close :
    tmFiber9StateAt 8 ∈ closeChainFiber tmWord tmFiber9DirectStates tmFiber9DirectStates.length [tmFiber9StateAt 0] := by
  change tmFiber9StateAt 8 ∈ closeChainFiber tmWord tmFiber9DirectStates (15 + 1) [tmFiber9StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber9DirectStates 15 [tmFiber9StateAt 0] (tmFiber9StateAt 8) tmFiber9State8_in_pass1_full

theorem tmFiber9State9_in_close :
    tmFiber9StateAt 9 ∈ closeChainFiber tmWord tmFiber9DirectStates tmFiber9DirectStates.length [tmFiber9StateAt 0] := by
  change tmFiber9StateAt 9 ∈ closeChainFiber tmWord tmFiber9DirectStates (15 + 1) [tmFiber9StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber9DirectStates 15 [tmFiber9StateAt 0] (tmFiber9StateAt 9) tmFiber9State9_in_pass1_full

theorem tmFiber9State10_in_close :
    tmFiber9StateAt 10 ∈ closeChainFiber tmWord tmFiber9DirectStates tmFiber9DirectStates.length [tmFiber9StateAt 0] := by
  change tmFiber9StateAt 10 ∈ closeChainFiber tmWord tmFiber9DirectStates (15 + 1) [tmFiber9StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber9DirectStates 15 [tmFiber9StateAt 0] (tmFiber9StateAt 10) tmFiber9State10_in_pass1_full

theorem tmFiber9State11_in_close :
    tmFiber9StateAt 11 ∈ closeChainFiber tmWord tmFiber9DirectStates tmFiber9DirectStates.length [tmFiber9StateAt 0] := by
  change tmFiber9StateAt 11 ∈ closeChainFiber tmWord tmFiber9DirectStates (15 + 1) [tmFiber9StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber9DirectStates 15 [tmFiber9StateAt 0] (tmFiber9StateAt 11) tmFiber9State11_in_pass1_full

theorem tmFiber9State12_in_close :
    tmFiber9StateAt 12 ∈ closeChainFiber tmWord tmFiber9DirectStates tmFiber9DirectStates.length [tmFiber9StateAt 0] := by
  change tmFiber9StateAt 12 ∈ closeChainFiber tmWord tmFiber9DirectStates (15 + 1) [tmFiber9StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber9DirectStates 15 [tmFiber9StateAt 0] (tmFiber9StateAt 12) tmFiber9State12_in_pass1_full

theorem tmFiber9State13_in_close :
    tmFiber9StateAt 13 ∈ closeChainFiber tmWord tmFiber9DirectStates tmFiber9DirectStates.length [tmFiber9StateAt 0] := by
  change tmFiber9StateAt 13 ∈ closeChainFiber tmWord tmFiber9DirectStates (15 + 1) [tmFiber9StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber9DirectStates 15 [tmFiber9StateAt 0] (tmFiber9StateAt 13) tmFiber9State13_in_pass1_full

theorem tmFiber9State14_in_close :
    tmFiber9StateAt 14 ∈ closeChainFiber tmWord tmFiber9DirectStates tmFiber9DirectStates.length [tmFiber9StateAt 0] := by
  change tmFiber9StateAt 14 ∈ closeChainFiber tmWord tmFiber9DirectStates (15 + 1) [tmFiber9StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber9DirectStates 15 [tmFiber9StateAt 0] (tmFiber9StateAt 14) tmFiber9State14_in_pass1_full

theorem tmFiber9State15_in_close :
    tmFiber9StateAt 15 ∈ closeChainFiber tmWord tmFiber9DirectStates tmFiber9DirectStates.length [tmFiber9StateAt 0] := by
  change tmFiber9StateAt 15 ∈ closeChainFiber tmWord tmFiber9DirectStates (15 + 1) [tmFiber9StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber9DirectStates 15 [tmFiber9StateAt 0] (tmFiber9StateAt 15) tmFiber9State15_in_pass1_full

theorem tmFiber9DirectConnected :
    chainFiberConnected tmWord tmFiber9DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber9DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber9State0_in_close
  · subst state
    exact tmFiber9State1_in_close
  · subst state
    exact tmFiber9State2_in_close
  · subst state
    exact tmFiber9State3_in_close
  · subst state
    exact tmFiber9State4_in_close
  · subst state
    exact tmFiber9State5_in_close
  · subst state
    exact tmFiber9State6_in_close
  · subst state
    exact tmFiber9State7_in_close
  · subst state
    exact tmFiber9State8_in_close
  · subst state
    exact tmFiber9State9_in_close
  · subst state
    exact tmFiber9State10_in_close
  · subst state
    exact tmFiber9State11_in_close
  · subst state
    exact tmFiber9State12_in_close
  · subst state
    exact tmFiber9State13_in_close
  · subst state
    exact tmFiber9State14_in_close
  · subst state
    exact tmFiber9State15_in_close
  · cases h

def tmFiber11StateAt (i : Nat) : List TauState :=
  directStates (tmFiber11RowAt i).sourceLeft (tmFiber11RowAt i).sourceRight

def tmFiber11DirectStates : List (List TauState) :=
  [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14, tmFiber11StateAt 15]

theorem tmFiber11ReverseRow_1_ok :
    tmRowReverseValid tmFiber11Key tmFiber11Expected (tmFiber11RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber11Chunk0_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber11Chunk0] at h
  exact h.2

theorem tmFiber11ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber11StateAt 0) (tmFiber11StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber11StateAt 0) (tmFiber11StateAt 1)
    (tmFiber11RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber11Key tmFiber11Expected
        (tmFiber11RowAt 1) (by decide) tmFiber11ReverseRow_1_ok
      simpa [tmFiber11StateAt, tmFiber11RowAt, tmFiber11Rows, listGetD, directRow] using h)

theorem tmFiber11ReverseRow_2_ok :
    tmRowReverseValid tmFiber11Key tmFiber11Expected (tmFiber11RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber11Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber11Chunk1] at h
  exact h.1

theorem tmFiber11ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber11StateAt 1) (tmFiber11StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber11StateAt 1) (tmFiber11StateAt 2)
    (tmFiber11RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber11Key tmFiber11Expected
        (tmFiber11RowAt 2) (by decide) tmFiber11ReverseRow_2_ok
      simpa [tmFiber11StateAt, tmFiber11RowAt, tmFiber11Rows, listGetD, directRow] using h)

theorem tmFiber11ReverseRow_3_ok :
    tmRowReverseValid tmFiber11Key tmFiber11Expected (tmFiber11RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber11Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber11Chunk1] at h
  exact h.2

theorem tmFiber11ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber11StateAt 0) (tmFiber11StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber11StateAt 0) (tmFiber11StateAt 3)
    (tmFiber11RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber11Key tmFiber11Expected
        (tmFiber11RowAt 3) (by decide) tmFiber11ReverseRow_3_ok
      simpa [tmFiber11StateAt, tmFiber11RowAt, tmFiber11Rows, listGetD, directRow] using h)

theorem tmFiber11ReverseRow_4_ok :
    tmRowReverseValid tmFiber11Key tmFiber11Expected (tmFiber11RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber11Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber11Chunk2] at h
  exact h.1

theorem tmFiber11ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber11StateAt 0) (tmFiber11StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber11StateAt 0) (tmFiber11StateAt 4)
    (tmFiber11RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber11Key tmFiber11Expected
        (tmFiber11RowAt 4) (by decide) tmFiber11ReverseRow_4_ok
      simpa [tmFiber11StateAt, tmFiber11RowAt, tmFiber11Rows, listGetD, directRow] using h)

theorem tmFiber11ReverseRow_5_ok :
    tmRowReverseValid tmFiber11Key tmFiber11Expected (tmFiber11RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber11Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber11Chunk2] at h
  exact h.2

theorem tmFiber11ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber11StateAt 1) (tmFiber11StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber11StateAt 1) (tmFiber11StateAt 5)
    (tmFiber11RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber11Key tmFiber11Expected
        (tmFiber11RowAt 5) (by decide) tmFiber11ReverseRow_5_ok
      simpa [tmFiber11StateAt, tmFiber11RowAt, tmFiber11Rows, listGetD, directRow] using h)

theorem tmFiber11ReverseRow_6_ok :
    tmRowReverseValid tmFiber11Key tmFiber11Expected (tmFiber11RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber11Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber11Chunk3] at h
  exact h.1

theorem tmFiber11ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber11StateAt 2) (tmFiber11StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber11StateAt 2) (tmFiber11StateAt 6)
    (tmFiber11RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber11Key tmFiber11Expected
        (tmFiber11RowAt 6) (by decide) tmFiber11ReverseRow_6_ok
      simpa [tmFiber11StateAt, tmFiber11RowAt, tmFiber11Rows, listGetD, directRow] using h)

theorem tmFiber11ReverseRow_7_ok :
    tmRowReverseValid tmFiber11Key tmFiber11Expected (tmFiber11RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber11Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber11Chunk3] at h
  exact h.2

theorem tmFiber11ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber11StateAt 3) (tmFiber11StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber11StateAt 3) (tmFiber11StateAt 7)
    (tmFiber11RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber11Key tmFiber11Expected
        (tmFiber11RowAt 7) (by decide) tmFiber11ReverseRow_7_ok
      simpa [tmFiber11StateAt, tmFiber11RowAt, tmFiber11Rows, listGetD, directRow] using h)

theorem tmFiber11ReverseRow_8_ok :
    tmRowReverseValid tmFiber11Key tmFiber11Expected (tmFiber11RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber11Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber11Chunk4] at h
  exact h.1

theorem tmFiber11ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber11StateAt 0) (tmFiber11StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber11StateAt 0) (tmFiber11StateAt 8)
    (tmFiber11RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber11Key tmFiber11Expected
        (tmFiber11RowAt 8) (by decide) tmFiber11ReverseRow_8_ok
      simpa [tmFiber11StateAt, tmFiber11RowAt, tmFiber11Rows, listGetD, directRow] using h)

theorem tmFiber11ReverseRow_9_ok :
    tmRowReverseValid tmFiber11Key tmFiber11Expected (tmFiber11RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber11Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber11Chunk4] at h
  exact h.2

theorem tmFiber11ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber11StateAt 1) (tmFiber11StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber11StateAt 1) (tmFiber11StateAt 9)
    (tmFiber11RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber11Key tmFiber11Expected
        (tmFiber11RowAt 9) (by decide) tmFiber11ReverseRow_9_ok
      simpa [tmFiber11StateAt, tmFiber11RowAt, tmFiber11Rows, listGetD, directRow] using h)

theorem tmFiber11ReverseRow_10_ok :
    tmRowReverseValid tmFiber11Key tmFiber11Expected (tmFiber11RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber11Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber11Chunk5] at h
  exact h.1

theorem tmFiber11ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber11StateAt 2) (tmFiber11StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber11StateAt 2) (tmFiber11StateAt 10)
    (tmFiber11RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber11Key tmFiber11Expected
        (tmFiber11RowAt 10) (by decide) tmFiber11ReverseRow_10_ok
      simpa [tmFiber11StateAt, tmFiber11RowAt, tmFiber11Rows, listGetD, directRow] using h)

theorem tmFiber11ReverseRow_11_ok :
    tmRowReverseValid tmFiber11Key tmFiber11Expected (tmFiber11RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber11Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber11Chunk5] at h
  exact h.2

theorem tmFiber11ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber11StateAt 3) (tmFiber11StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber11StateAt 3) (tmFiber11StateAt 11)
    (tmFiber11RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber11Key tmFiber11Expected
        (tmFiber11RowAt 11) (by decide) tmFiber11ReverseRow_11_ok
      simpa [tmFiber11StateAt, tmFiber11RowAt, tmFiber11Rows, listGetD, directRow] using h)

theorem tmFiber11ReverseRow_12_ok :
    tmRowReverseValid tmFiber11Key tmFiber11Expected (tmFiber11RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber11Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber11Chunk6] at h
  exact h.1

theorem tmFiber11ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber11StateAt 4) (tmFiber11StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber11StateAt 4) (tmFiber11StateAt 12)
    (tmFiber11RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber11Key tmFiber11Expected
        (tmFiber11RowAt 12) (by decide) tmFiber11ReverseRow_12_ok
      simpa [tmFiber11StateAt, tmFiber11RowAt, tmFiber11Rows, listGetD, directRow] using h)

theorem tmFiber11ReverseRow_13_ok :
    tmRowReverseValid tmFiber11Key tmFiber11Expected (tmFiber11RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber11Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber11Chunk6] at h
  exact h.2

theorem tmFiber11ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber11StateAt 5) (tmFiber11StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber11StateAt 5) (tmFiber11StateAt 13)
    (tmFiber11RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber11Key tmFiber11Expected
        (tmFiber11RowAt 13) (by decide) tmFiber11ReverseRow_13_ok
      simpa [tmFiber11StateAt, tmFiber11RowAt, tmFiber11Rows, listGetD, directRow] using h)

theorem tmFiber11ReverseRow_14_ok :
    tmRowReverseValid tmFiber11Key tmFiber11Expected (tmFiber11RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber11Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber11Chunk7] at h
  exact h.1

theorem tmFiber11ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber11StateAt 6) (tmFiber11StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber11StateAt 6) (tmFiber11StateAt 14)
    (tmFiber11RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber11Key tmFiber11Expected
        (tmFiber11RowAt 14) (by decide) tmFiber11ReverseRow_14_ok
      simpa [tmFiber11StateAt, tmFiber11RowAt, tmFiber11Rows, listGetD, directRow] using h)

theorem tmFiber11ReverseRow_15_ok :
    tmRowReverseValid tmFiber11Key tmFiber11Expected (tmFiber11RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber11Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber11Chunk7] at h
  exact h.2

theorem tmFiber11ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber11StateAt 7) (tmFiber11StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber11StateAt 7) (tmFiber11StateAt 15)
    (tmFiber11RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber11Key tmFiber11Expected
        (tmFiber11RowAt 15) (by decide) tmFiber11ReverseRow_15_ok
      simpa [tmFiber11StateAt, tmFiber11RowAt, tmFiber11Rows, listGetD, directRow] using h)

theorem tmFiber11State0_in_pass1_prefix :
    tmFiber11StateAt 0 ∈ chainClosureStep tmWord [tmFiber11StateAt 0] [tmFiber11StateAt 0] := by
  exact chainClosureStep_mem_of_seen tmWord [tmFiber11StateAt 0] [tmFiber11StateAt 0] (tmFiber11StateAt 0) (by simp)

theorem tmFiber11State1_in_pass1_prefix :
    tmFiber11StateAt 1 ∈ chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1] [tmFiber11StateAt 0] := by
  have hparentBefore :
      tmFiber11StateAt 0 ∈ chainClosureStep tmWord [tmFiber11StateAt 0] [tmFiber11StateAt 0] := by
    exact tmFiber11State0_in_pass1_prefix
  rw [show [tmFiber11StateAt 0, tmFiber11StateAt 1] = [tmFiber11StateAt 0] ++ [tmFiber11StateAt 1] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber11StateAt 1) []
    (chainClosureStep tmWord [tmFiber11StateAt 0] [tmFiber11StateAt 0]) (tmFiber11StateAt 0)
    hparentBefore tmFiber11ReverseSingleStep1

theorem tmFiber11State2_in_pass1_prefix :
    tmFiber11StateAt 2 ∈ chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2] [tmFiber11StateAt 0] := by
  have hparentBefore :
      tmFiber11StateAt 1 ∈ chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1] [tmFiber11StateAt 0] := by
    exact tmFiber11State1_in_pass1_prefix
  rw [show [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2] = [tmFiber11StateAt 0, tmFiber11StateAt 1] ++ [tmFiber11StateAt 2] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber11StateAt 2) []
    (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1] [tmFiber11StateAt 0]) (tmFiber11StateAt 1)
    hparentBefore tmFiber11ReverseSingleStep2

theorem tmFiber11State3_in_pass1_prefix :
    tmFiber11StateAt 3 ∈ chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3] [tmFiber11StateAt 0] := by
  have hparentBefore :
      tmFiber11StateAt 0 ∈ chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2] [tmFiber11StateAt 0] := by
    rw [show [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2] = [tmFiber11StateAt 0] ++ [tmFiber11StateAt 1, tmFiber11StateAt 2] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber11StateAt 1, tmFiber11StateAt 2]
      (chainClosureStep tmWord [tmFiber11StateAt 0] [tmFiber11StateAt 0]) (tmFiber11StateAt 0)
      tmFiber11State0_in_pass1_prefix
  rw [show [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3] = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2] ++ [tmFiber11StateAt 3] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber11StateAt 3) []
    (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2] [tmFiber11StateAt 0]) (tmFiber11StateAt 0)
    hparentBefore tmFiber11ReverseSingleStep3

theorem tmFiber11State4_in_pass1_prefix :
    tmFiber11StateAt 4 ∈ chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4] [tmFiber11StateAt 0] := by
  have hparentBefore :
      tmFiber11StateAt 0 ∈ chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3] [tmFiber11StateAt 0] := by
    rw [show [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3] = [tmFiber11StateAt 0] ++ [tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3]
      (chainClosureStep tmWord [tmFiber11StateAt 0] [tmFiber11StateAt 0]) (tmFiber11StateAt 0)
      tmFiber11State0_in_pass1_prefix
  rw [show [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4] = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3] ++ [tmFiber11StateAt 4] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber11StateAt 4) []
    (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3] [tmFiber11StateAt 0]) (tmFiber11StateAt 0)
    hparentBefore tmFiber11ReverseSingleStep4

theorem tmFiber11State5_in_pass1_prefix :
    tmFiber11StateAt 5 ∈ chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5] [tmFiber11StateAt 0] := by
  have hparentBefore :
      tmFiber11StateAt 1 ∈ chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4] [tmFiber11StateAt 0] := by
    rw [show [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4] = [tmFiber11StateAt 0, tmFiber11StateAt 1] ++ [tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4]
      (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1] [tmFiber11StateAt 0]) (tmFiber11StateAt 1)
      tmFiber11State1_in_pass1_prefix
  rw [show [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5] = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4] ++ [tmFiber11StateAt 5] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber11StateAt 5) []
    (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4] [tmFiber11StateAt 0]) (tmFiber11StateAt 1)
    hparentBefore tmFiber11ReverseSingleStep5

theorem tmFiber11State6_in_pass1_prefix :
    tmFiber11StateAt 6 ∈ chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6] [tmFiber11StateAt 0] := by
  have hparentBefore :
      tmFiber11StateAt 2 ∈ chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5] [tmFiber11StateAt 0] := by
    rw [show [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5] = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2] ++ [tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5]
      (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2] [tmFiber11StateAt 0]) (tmFiber11StateAt 2)
      tmFiber11State2_in_pass1_prefix
  rw [show [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6] = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5] ++ [tmFiber11StateAt 6] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber11StateAt 6) []
    (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5] [tmFiber11StateAt 0]) (tmFiber11StateAt 2)
    hparentBefore tmFiber11ReverseSingleStep6

theorem tmFiber11State7_in_pass1_prefix :
    tmFiber11StateAt 7 ∈ chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7] [tmFiber11StateAt 0] := by
  have hparentBefore :
      tmFiber11StateAt 3 ∈ chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6] [tmFiber11StateAt 0] := by
    rw [show [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6] = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3] ++ [tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6]
      (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3] [tmFiber11StateAt 0]) (tmFiber11StateAt 3)
      tmFiber11State3_in_pass1_prefix
  rw [show [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7] = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6] ++ [tmFiber11StateAt 7] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber11StateAt 7) []
    (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6] [tmFiber11StateAt 0]) (tmFiber11StateAt 3)
    hparentBefore tmFiber11ReverseSingleStep7

theorem tmFiber11State8_in_pass1_prefix :
    tmFiber11StateAt 8 ∈ chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8] [tmFiber11StateAt 0] := by
  have hparentBefore :
      tmFiber11StateAt 0 ∈ chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7] [tmFiber11StateAt 0] := by
    rw [show [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7] = [tmFiber11StateAt 0] ++ [tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7]
      (chainClosureStep tmWord [tmFiber11StateAt 0] [tmFiber11StateAt 0]) (tmFiber11StateAt 0)
      tmFiber11State0_in_pass1_prefix
  rw [show [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8] = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7] ++ [tmFiber11StateAt 8] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber11StateAt 8) []
    (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7] [tmFiber11StateAt 0]) (tmFiber11StateAt 0)
    hparentBefore tmFiber11ReverseSingleStep8

theorem tmFiber11State9_in_pass1_prefix :
    tmFiber11StateAt 9 ∈ chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9] [tmFiber11StateAt 0] := by
  have hparentBefore :
      tmFiber11StateAt 1 ∈ chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8] [tmFiber11StateAt 0] := by
    rw [show [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8] = [tmFiber11StateAt 0, tmFiber11StateAt 1] ++ [tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8]
      (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1] [tmFiber11StateAt 0]) (tmFiber11StateAt 1)
      tmFiber11State1_in_pass1_prefix
  rw [show [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9] = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8] ++ [tmFiber11StateAt 9] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber11StateAt 9) []
    (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8] [tmFiber11StateAt 0]) (tmFiber11StateAt 1)
    hparentBefore tmFiber11ReverseSingleStep9

theorem tmFiber11State10_in_pass1_prefix :
    tmFiber11StateAt 10 ∈ chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10] [tmFiber11StateAt 0] := by
  have hparentBefore :
      tmFiber11StateAt 2 ∈ chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9] [tmFiber11StateAt 0] := by
    rw [show [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9] = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2] ++ [tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9]
      (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2] [tmFiber11StateAt 0]) (tmFiber11StateAt 2)
      tmFiber11State2_in_pass1_prefix
  rw [show [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10] = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9] ++ [tmFiber11StateAt 10] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber11StateAt 10) []
    (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9] [tmFiber11StateAt 0]) (tmFiber11StateAt 2)
    hparentBefore tmFiber11ReverseSingleStep10

theorem tmFiber11State11_in_pass1_prefix :
    tmFiber11StateAt 11 ∈ chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11] [tmFiber11StateAt 0] := by
  have hparentBefore :
      tmFiber11StateAt 3 ∈ chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10] [tmFiber11StateAt 0] := by
    rw [show [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10] = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3] ++ [tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10]
      (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3] [tmFiber11StateAt 0]) (tmFiber11StateAt 3)
      tmFiber11State3_in_pass1_prefix
  rw [show [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11] = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10] ++ [tmFiber11StateAt 11] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber11StateAt 11) []
    (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10] [tmFiber11StateAt 0]) (tmFiber11StateAt 3)
    hparentBefore tmFiber11ReverseSingleStep11

theorem tmFiber11State12_in_pass1_prefix :
    tmFiber11StateAt 12 ∈ chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12] [tmFiber11StateAt 0] := by
  have hparentBefore :
      tmFiber11StateAt 4 ∈ chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11] [tmFiber11StateAt 0] := by
    rw [show [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11] = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4] ++ [tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11]
      (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4] [tmFiber11StateAt 0]) (tmFiber11StateAt 4)
      tmFiber11State4_in_pass1_prefix
  rw [show [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12] = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11] ++ [tmFiber11StateAt 12] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber11StateAt 12) []
    (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11] [tmFiber11StateAt 0]) (tmFiber11StateAt 4)
    hparentBefore tmFiber11ReverseSingleStep12

theorem tmFiber11State13_in_pass1_prefix :
    tmFiber11StateAt 13 ∈ chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13] [tmFiber11StateAt 0] := by
  have hparentBefore :
      tmFiber11StateAt 5 ∈ chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12] [tmFiber11StateAt 0] := by
    rw [show [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12] = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5] ++ [tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12]
      (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5] [tmFiber11StateAt 0]) (tmFiber11StateAt 5)
      tmFiber11State5_in_pass1_prefix
  rw [show [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13] = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12] ++ [tmFiber11StateAt 13] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber11StateAt 13) []
    (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12] [tmFiber11StateAt 0]) (tmFiber11StateAt 5)
    hparentBefore tmFiber11ReverseSingleStep13

theorem tmFiber11State14_in_pass1_prefix :
    tmFiber11StateAt 14 ∈ chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14] [tmFiber11StateAt 0] := by
  have hparentBefore :
      tmFiber11StateAt 6 ∈ chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13] [tmFiber11StateAt 0] := by
    rw [show [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13] = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6] ++ [tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13]
      (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6] [tmFiber11StateAt 0]) (tmFiber11StateAt 6)
      tmFiber11State6_in_pass1_prefix
  rw [show [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14] = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13] ++ [tmFiber11StateAt 14] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber11StateAt 14) []
    (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13] [tmFiber11StateAt 0]) (tmFiber11StateAt 6)
    hparentBefore tmFiber11ReverseSingleStep14

theorem tmFiber11State15_in_pass1_prefix :
    tmFiber11StateAt 15 ∈ chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14, tmFiber11StateAt 15] [tmFiber11StateAt 0] := by
  have hparentBefore :
      tmFiber11StateAt 7 ∈ chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14] [tmFiber11StateAt 0] := by
    rw [show [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14] = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7] ++ [tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14]
      (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7] [tmFiber11StateAt 0]) (tmFiber11StateAt 7)
      tmFiber11State7_in_pass1_prefix
  rw [show [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14, tmFiber11StateAt 15] = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14] ++ [tmFiber11StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber11StateAt 15) []
    (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14] [tmFiber11StateAt 0]) (tmFiber11StateAt 7)
    hparentBefore tmFiber11ReverseSingleStep15

theorem tmFiber11State0_in_pass1_full :
    tmFiber11StateAt 0 ∈ chainClosureStep tmWord tmFiber11DirectStates [tmFiber11StateAt 0] := by
  rw [show tmFiber11DirectStates = [tmFiber11StateAt 0] ++ [tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14, tmFiber11StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14, tmFiber11StateAt 15]
    (chainClosureStep tmWord [tmFiber11StateAt 0] [tmFiber11StateAt 0]) (tmFiber11StateAt 0)
    tmFiber11State0_in_pass1_prefix

theorem tmFiber11State1_in_pass1_full :
    tmFiber11StateAt 1 ∈ chainClosureStep tmWord tmFiber11DirectStates [tmFiber11StateAt 0] := by
  rw [show tmFiber11DirectStates = [tmFiber11StateAt 0, tmFiber11StateAt 1] ++ [tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14, tmFiber11StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14, tmFiber11StateAt 15]
    (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1] [tmFiber11StateAt 0]) (tmFiber11StateAt 1)
    tmFiber11State1_in_pass1_prefix

theorem tmFiber11State2_in_pass1_full :
    tmFiber11StateAt 2 ∈ chainClosureStep tmWord tmFiber11DirectStates [tmFiber11StateAt 0] := by
  rw [show tmFiber11DirectStates = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2] ++ [tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14, tmFiber11StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14, tmFiber11StateAt 15]
    (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2] [tmFiber11StateAt 0]) (tmFiber11StateAt 2)
    tmFiber11State2_in_pass1_prefix

theorem tmFiber11State3_in_pass1_full :
    tmFiber11StateAt 3 ∈ chainClosureStep tmWord tmFiber11DirectStates [tmFiber11StateAt 0] := by
  rw [show tmFiber11DirectStates = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3] ++ [tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14, tmFiber11StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14, tmFiber11StateAt 15]
    (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3] [tmFiber11StateAt 0]) (tmFiber11StateAt 3)
    tmFiber11State3_in_pass1_prefix

theorem tmFiber11State4_in_pass1_full :
    tmFiber11StateAt 4 ∈ chainClosureStep tmWord tmFiber11DirectStates [tmFiber11StateAt 0] := by
  rw [show tmFiber11DirectStates = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4] ++ [tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14, tmFiber11StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14, tmFiber11StateAt 15]
    (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4] [tmFiber11StateAt 0]) (tmFiber11StateAt 4)
    tmFiber11State4_in_pass1_prefix

theorem tmFiber11State5_in_pass1_full :
    tmFiber11StateAt 5 ∈ chainClosureStep tmWord tmFiber11DirectStates [tmFiber11StateAt 0] := by
  rw [show tmFiber11DirectStates = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5] ++ [tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14, tmFiber11StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14, tmFiber11StateAt 15]
    (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5] [tmFiber11StateAt 0]) (tmFiber11StateAt 5)
    tmFiber11State5_in_pass1_prefix

theorem tmFiber11State6_in_pass1_full :
    tmFiber11StateAt 6 ∈ chainClosureStep tmWord tmFiber11DirectStates [tmFiber11StateAt 0] := by
  rw [show tmFiber11DirectStates = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6] ++ [tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14, tmFiber11StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14, tmFiber11StateAt 15]
    (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6] [tmFiber11StateAt 0]) (tmFiber11StateAt 6)
    tmFiber11State6_in_pass1_prefix

theorem tmFiber11State7_in_pass1_full :
    tmFiber11StateAt 7 ∈ chainClosureStep tmWord tmFiber11DirectStates [tmFiber11StateAt 0] := by
  rw [show tmFiber11DirectStates = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7] ++ [tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14, tmFiber11StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14, tmFiber11StateAt 15]
    (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7] [tmFiber11StateAt 0]) (tmFiber11StateAt 7)
    tmFiber11State7_in_pass1_prefix

theorem tmFiber11State8_in_pass1_full :
    tmFiber11StateAt 8 ∈ chainClosureStep tmWord tmFiber11DirectStates [tmFiber11StateAt 0] := by
  rw [show tmFiber11DirectStates = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8] ++ [tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14, tmFiber11StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14, tmFiber11StateAt 15]
    (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8] [tmFiber11StateAt 0]) (tmFiber11StateAt 8)
    tmFiber11State8_in_pass1_prefix

theorem tmFiber11State9_in_pass1_full :
    tmFiber11StateAt 9 ∈ chainClosureStep tmWord tmFiber11DirectStates [tmFiber11StateAt 0] := by
  rw [show tmFiber11DirectStates = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9] ++ [tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14, tmFiber11StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14, tmFiber11StateAt 15]
    (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9] [tmFiber11StateAt 0]) (tmFiber11StateAt 9)
    tmFiber11State9_in_pass1_prefix

theorem tmFiber11State10_in_pass1_full :
    tmFiber11StateAt 10 ∈ chainClosureStep tmWord tmFiber11DirectStates [tmFiber11StateAt 0] := by
  rw [show tmFiber11DirectStates = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10] ++ [tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14, tmFiber11StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14, tmFiber11StateAt 15]
    (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10] [tmFiber11StateAt 0]) (tmFiber11StateAt 10)
    tmFiber11State10_in_pass1_prefix

theorem tmFiber11State11_in_pass1_full :
    tmFiber11StateAt 11 ∈ chainClosureStep tmWord tmFiber11DirectStates [tmFiber11StateAt 0] := by
  rw [show tmFiber11DirectStates = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11] ++ [tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14, tmFiber11StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14, tmFiber11StateAt 15]
    (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11] [tmFiber11StateAt 0]) (tmFiber11StateAt 11)
    tmFiber11State11_in_pass1_prefix

theorem tmFiber11State12_in_pass1_full :
    tmFiber11StateAt 12 ∈ chainClosureStep tmWord tmFiber11DirectStates [tmFiber11StateAt 0] := by
  rw [show tmFiber11DirectStates = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12] ++ [tmFiber11StateAt 13, tmFiber11StateAt 14, tmFiber11StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber11StateAt 13, tmFiber11StateAt 14, tmFiber11StateAt 15]
    (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12] [tmFiber11StateAt 0]) (tmFiber11StateAt 12)
    tmFiber11State12_in_pass1_prefix

theorem tmFiber11State13_in_pass1_full :
    tmFiber11StateAt 13 ∈ chainClosureStep tmWord tmFiber11DirectStates [tmFiber11StateAt 0] := by
  rw [show tmFiber11DirectStates = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13] ++ [tmFiber11StateAt 14, tmFiber11StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber11StateAt 14, tmFiber11StateAt 15]
    (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13] [tmFiber11StateAt 0]) (tmFiber11StateAt 13)
    tmFiber11State13_in_pass1_prefix

theorem tmFiber11State14_in_pass1_full :
    tmFiber11StateAt 14 ∈ chainClosureStep tmWord tmFiber11DirectStates [tmFiber11StateAt 0] := by
  rw [show tmFiber11DirectStates = [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14] ++ [tmFiber11StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber11StateAt 15]
    (chainClosureStep tmWord [tmFiber11StateAt 0, tmFiber11StateAt 1, tmFiber11StateAt 2, tmFiber11StateAt 3, tmFiber11StateAt 4, tmFiber11StateAt 5, tmFiber11StateAt 6, tmFiber11StateAt 7, tmFiber11StateAt 8, tmFiber11StateAt 9, tmFiber11StateAt 10, tmFiber11StateAt 11, tmFiber11StateAt 12, tmFiber11StateAt 13, tmFiber11StateAt 14] [tmFiber11StateAt 0]) (tmFiber11StateAt 14)
    tmFiber11State14_in_pass1_prefix

theorem tmFiber11State15_in_pass1_full :
    tmFiber11StateAt 15 ∈ chainClosureStep tmWord tmFiber11DirectStates [tmFiber11StateAt 0] := by
  simpa [tmFiber11DirectStates] using tmFiber11State15_in_pass1_prefix

theorem tmFiber11State0_in_close :
    tmFiber11StateAt 0 ∈ closeChainFiber tmWord tmFiber11DirectStates tmFiber11DirectStates.length [tmFiber11StateAt 0] := by
  change tmFiber11StateAt 0 ∈ closeChainFiber tmWord tmFiber11DirectStates (15 + 1) [tmFiber11StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber11DirectStates 15 [tmFiber11StateAt 0] (tmFiber11StateAt 0) tmFiber11State0_in_pass1_full

theorem tmFiber11State1_in_close :
    tmFiber11StateAt 1 ∈ closeChainFiber tmWord tmFiber11DirectStates tmFiber11DirectStates.length [tmFiber11StateAt 0] := by
  change tmFiber11StateAt 1 ∈ closeChainFiber tmWord tmFiber11DirectStates (15 + 1) [tmFiber11StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber11DirectStates 15 [tmFiber11StateAt 0] (tmFiber11StateAt 1) tmFiber11State1_in_pass1_full

theorem tmFiber11State2_in_close :
    tmFiber11StateAt 2 ∈ closeChainFiber tmWord tmFiber11DirectStates tmFiber11DirectStates.length [tmFiber11StateAt 0] := by
  change tmFiber11StateAt 2 ∈ closeChainFiber tmWord tmFiber11DirectStates (15 + 1) [tmFiber11StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber11DirectStates 15 [tmFiber11StateAt 0] (tmFiber11StateAt 2) tmFiber11State2_in_pass1_full

theorem tmFiber11State3_in_close :
    tmFiber11StateAt 3 ∈ closeChainFiber tmWord tmFiber11DirectStates tmFiber11DirectStates.length [tmFiber11StateAt 0] := by
  change tmFiber11StateAt 3 ∈ closeChainFiber tmWord tmFiber11DirectStates (15 + 1) [tmFiber11StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber11DirectStates 15 [tmFiber11StateAt 0] (tmFiber11StateAt 3) tmFiber11State3_in_pass1_full

theorem tmFiber11State4_in_close :
    tmFiber11StateAt 4 ∈ closeChainFiber tmWord tmFiber11DirectStates tmFiber11DirectStates.length [tmFiber11StateAt 0] := by
  change tmFiber11StateAt 4 ∈ closeChainFiber tmWord tmFiber11DirectStates (15 + 1) [tmFiber11StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber11DirectStates 15 [tmFiber11StateAt 0] (tmFiber11StateAt 4) tmFiber11State4_in_pass1_full

theorem tmFiber11State5_in_close :
    tmFiber11StateAt 5 ∈ closeChainFiber tmWord tmFiber11DirectStates tmFiber11DirectStates.length [tmFiber11StateAt 0] := by
  change tmFiber11StateAt 5 ∈ closeChainFiber tmWord tmFiber11DirectStates (15 + 1) [tmFiber11StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber11DirectStates 15 [tmFiber11StateAt 0] (tmFiber11StateAt 5) tmFiber11State5_in_pass1_full

theorem tmFiber11State6_in_close :
    tmFiber11StateAt 6 ∈ closeChainFiber tmWord tmFiber11DirectStates tmFiber11DirectStates.length [tmFiber11StateAt 0] := by
  change tmFiber11StateAt 6 ∈ closeChainFiber tmWord tmFiber11DirectStates (15 + 1) [tmFiber11StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber11DirectStates 15 [tmFiber11StateAt 0] (tmFiber11StateAt 6) tmFiber11State6_in_pass1_full

theorem tmFiber11State7_in_close :
    tmFiber11StateAt 7 ∈ closeChainFiber tmWord tmFiber11DirectStates tmFiber11DirectStates.length [tmFiber11StateAt 0] := by
  change tmFiber11StateAt 7 ∈ closeChainFiber tmWord tmFiber11DirectStates (15 + 1) [tmFiber11StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber11DirectStates 15 [tmFiber11StateAt 0] (tmFiber11StateAt 7) tmFiber11State7_in_pass1_full

theorem tmFiber11State8_in_close :
    tmFiber11StateAt 8 ∈ closeChainFiber tmWord tmFiber11DirectStates tmFiber11DirectStates.length [tmFiber11StateAt 0] := by
  change tmFiber11StateAt 8 ∈ closeChainFiber tmWord tmFiber11DirectStates (15 + 1) [tmFiber11StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber11DirectStates 15 [tmFiber11StateAt 0] (tmFiber11StateAt 8) tmFiber11State8_in_pass1_full

theorem tmFiber11State9_in_close :
    tmFiber11StateAt 9 ∈ closeChainFiber tmWord tmFiber11DirectStates tmFiber11DirectStates.length [tmFiber11StateAt 0] := by
  change tmFiber11StateAt 9 ∈ closeChainFiber tmWord tmFiber11DirectStates (15 + 1) [tmFiber11StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber11DirectStates 15 [tmFiber11StateAt 0] (tmFiber11StateAt 9) tmFiber11State9_in_pass1_full

theorem tmFiber11State10_in_close :
    tmFiber11StateAt 10 ∈ closeChainFiber tmWord tmFiber11DirectStates tmFiber11DirectStates.length [tmFiber11StateAt 0] := by
  change tmFiber11StateAt 10 ∈ closeChainFiber tmWord tmFiber11DirectStates (15 + 1) [tmFiber11StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber11DirectStates 15 [tmFiber11StateAt 0] (tmFiber11StateAt 10) tmFiber11State10_in_pass1_full

theorem tmFiber11State11_in_close :
    tmFiber11StateAt 11 ∈ closeChainFiber tmWord tmFiber11DirectStates tmFiber11DirectStates.length [tmFiber11StateAt 0] := by
  change tmFiber11StateAt 11 ∈ closeChainFiber tmWord tmFiber11DirectStates (15 + 1) [tmFiber11StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber11DirectStates 15 [tmFiber11StateAt 0] (tmFiber11StateAt 11) tmFiber11State11_in_pass1_full

theorem tmFiber11State12_in_close :
    tmFiber11StateAt 12 ∈ closeChainFiber tmWord tmFiber11DirectStates tmFiber11DirectStates.length [tmFiber11StateAt 0] := by
  change tmFiber11StateAt 12 ∈ closeChainFiber tmWord tmFiber11DirectStates (15 + 1) [tmFiber11StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber11DirectStates 15 [tmFiber11StateAt 0] (tmFiber11StateAt 12) tmFiber11State12_in_pass1_full

theorem tmFiber11State13_in_close :
    tmFiber11StateAt 13 ∈ closeChainFiber tmWord tmFiber11DirectStates tmFiber11DirectStates.length [tmFiber11StateAt 0] := by
  change tmFiber11StateAt 13 ∈ closeChainFiber tmWord tmFiber11DirectStates (15 + 1) [tmFiber11StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber11DirectStates 15 [tmFiber11StateAt 0] (tmFiber11StateAt 13) tmFiber11State13_in_pass1_full

theorem tmFiber11State14_in_close :
    tmFiber11StateAt 14 ∈ closeChainFiber tmWord tmFiber11DirectStates tmFiber11DirectStates.length [tmFiber11StateAt 0] := by
  change tmFiber11StateAt 14 ∈ closeChainFiber tmWord tmFiber11DirectStates (15 + 1) [tmFiber11StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber11DirectStates 15 [tmFiber11StateAt 0] (tmFiber11StateAt 14) tmFiber11State14_in_pass1_full

theorem tmFiber11State15_in_close :
    tmFiber11StateAt 15 ∈ closeChainFiber tmWord tmFiber11DirectStates tmFiber11DirectStates.length [tmFiber11StateAt 0] := by
  change tmFiber11StateAt 15 ∈ closeChainFiber tmWord tmFiber11DirectStates (15 + 1) [tmFiber11StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber11DirectStates 15 [tmFiber11StateAt 0] (tmFiber11StateAt 15) tmFiber11State15_in_pass1_full

theorem tmFiber11DirectConnected :
    chainFiberConnected tmWord tmFiber11DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber11DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber11State0_in_close
  · subst state
    exact tmFiber11State1_in_close
  · subst state
    exact tmFiber11State2_in_close
  · subst state
    exact tmFiber11State3_in_close
  · subst state
    exact tmFiber11State4_in_close
  · subst state
    exact tmFiber11State5_in_close
  · subst state
    exact tmFiber11State6_in_close
  · subst state
    exact tmFiber11State7_in_close
  · subst state
    exact tmFiber11State8_in_close
  · subst state
    exact tmFiber11State9_in_close
  · subst state
    exact tmFiber11State10_in_close
  · subst state
    exact tmFiber11State11_in_close
  · subst state
    exact tmFiber11State12_in_close
  · subst state
    exact tmFiber11State13_in_close
  · subst state
    exact tmFiber11State14_in_close
  · subst state
    exact tmFiber11State15_in_close
  · cases h

def tmFiber18StateAt (i : Nat) : List TauState :=
  directStates (tmFiber18RowAt i).sourceLeft (tmFiber18RowAt i).sourceRight

def tmFiber18DirectStates : List (List TauState) :=
  [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14, tmFiber18StateAt 15]

theorem tmFiber18ReverseRow_1_ok :
    tmRowReverseValid tmFiber18Key tmFiber18Expected (tmFiber18RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber18Chunk0_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber18Chunk0] at h
  exact h.2

theorem tmFiber18ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber18StateAt 0) (tmFiber18StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber18StateAt 0) (tmFiber18StateAt 1)
    (tmFiber18RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber18Key tmFiber18Expected
        (tmFiber18RowAt 1) (by decide) tmFiber18ReverseRow_1_ok
      simpa [tmFiber18StateAt, tmFiber18RowAt, tmFiber18Rows, listGetD, directRow] using h)

theorem tmFiber18ReverseRow_2_ok :
    tmRowReverseValid tmFiber18Key tmFiber18Expected (tmFiber18RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber18Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber18Chunk1] at h
  exact h.1

theorem tmFiber18ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber18StateAt 0) (tmFiber18StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber18StateAt 0) (tmFiber18StateAt 2)
    (tmFiber18RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber18Key tmFiber18Expected
        (tmFiber18RowAt 2) (by decide) tmFiber18ReverseRow_2_ok
      simpa [tmFiber18StateAt, tmFiber18RowAt, tmFiber18Rows, listGetD, directRow] using h)

theorem tmFiber18ReverseRow_3_ok :
    tmRowReverseValid tmFiber18Key tmFiber18Expected (tmFiber18RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber18Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber18Chunk1] at h
  exact h.2

theorem tmFiber18ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber18StateAt 1) (tmFiber18StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber18StateAt 1) (tmFiber18StateAt 3)
    (tmFiber18RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber18Key tmFiber18Expected
        (tmFiber18RowAt 3) (by decide) tmFiber18ReverseRow_3_ok
      simpa [tmFiber18StateAt, tmFiber18RowAt, tmFiber18Rows, listGetD, directRow] using h)

theorem tmFiber18ReverseRow_4_ok :
    tmRowReverseValid tmFiber18Key tmFiber18Expected (tmFiber18RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber18Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber18Chunk2] at h
  exact h.1

theorem tmFiber18ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber18StateAt 0) (tmFiber18StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber18StateAt 0) (tmFiber18StateAt 4)
    (tmFiber18RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber18Key tmFiber18Expected
        (tmFiber18RowAt 4) (by decide) tmFiber18ReverseRow_4_ok
      simpa [tmFiber18StateAt, tmFiber18RowAt, tmFiber18Rows, listGetD, directRow] using h)

theorem tmFiber18ReverseRow_5_ok :
    tmRowReverseValid tmFiber18Key tmFiber18Expected (tmFiber18RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber18Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber18Chunk2] at h
  exact h.2

theorem tmFiber18ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber18StateAt 1) (tmFiber18StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber18StateAt 1) (tmFiber18StateAt 5)
    (tmFiber18RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber18Key tmFiber18Expected
        (tmFiber18RowAt 5) (by decide) tmFiber18ReverseRow_5_ok
      simpa [tmFiber18StateAt, tmFiber18RowAt, tmFiber18Rows, listGetD, directRow] using h)

theorem tmFiber18ReverseRow_6_ok :
    tmRowReverseValid tmFiber18Key tmFiber18Expected (tmFiber18RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber18Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber18Chunk3] at h
  exact h.1

theorem tmFiber18ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber18StateAt 2) (tmFiber18StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber18StateAt 2) (tmFiber18StateAt 6)
    (tmFiber18RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber18Key tmFiber18Expected
        (tmFiber18RowAt 6) (by decide) tmFiber18ReverseRow_6_ok
      simpa [tmFiber18StateAt, tmFiber18RowAt, tmFiber18Rows, listGetD, directRow] using h)

theorem tmFiber18ReverseRow_7_ok :
    tmRowReverseValid tmFiber18Key tmFiber18Expected (tmFiber18RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber18Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber18Chunk3] at h
  exact h.2

theorem tmFiber18ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber18StateAt 3) (tmFiber18StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber18StateAt 3) (tmFiber18StateAt 7)
    (tmFiber18RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber18Key tmFiber18Expected
        (tmFiber18RowAt 7) (by decide) tmFiber18ReverseRow_7_ok
      simpa [tmFiber18StateAt, tmFiber18RowAt, tmFiber18Rows, listGetD, directRow] using h)

theorem tmFiber18ReverseRow_8_ok :
    tmRowReverseValid tmFiber18Key tmFiber18Expected (tmFiber18RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber18Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber18Chunk4] at h
  exact h.1

theorem tmFiber18ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber18StateAt 0) (tmFiber18StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber18StateAt 0) (tmFiber18StateAt 8)
    (tmFiber18RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber18Key tmFiber18Expected
        (tmFiber18RowAt 8) (by decide) tmFiber18ReverseRow_8_ok
      simpa [tmFiber18StateAt, tmFiber18RowAt, tmFiber18Rows, listGetD, directRow] using h)

theorem tmFiber18ReverseRow_9_ok :
    tmRowReverseValid tmFiber18Key tmFiber18Expected (tmFiber18RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber18Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber18Chunk4] at h
  exact h.2

theorem tmFiber18ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber18StateAt 1) (tmFiber18StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber18StateAt 1) (tmFiber18StateAt 9)
    (tmFiber18RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber18Key tmFiber18Expected
        (tmFiber18RowAt 9) (by decide) tmFiber18ReverseRow_9_ok
      simpa [tmFiber18StateAt, tmFiber18RowAt, tmFiber18Rows, listGetD, directRow] using h)

theorem tmFiber18ReverseRow_10_ok :
    tmRowReverseValid tmFiber18Key tmFiber18Expected (tmFiber18RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber18Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber18Chunk5] at h
  exact h.1

theorem tmFiber18ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber18StateAt 2) (tmFiber18StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber18StateAt 2) (tmFiber18StateAt 10)
    (tmFiber18RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber18Key tmFiber18Expected
        (tmFiber18RowAt 10) (by decide) tmFiber18ReverseRow_10_ok
      simpa [tmFiber18StateAt, tmFiber18RowAt, tmFiber18Rows, listGetD, directRow] using h)

theorem tmFiber18ReverseRow_11_ok :
    tmRowReverseValid tmFiber18Key tmFiber18Expected (tmFiber18RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber18Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber18Chunk5] at h
  exact h.2

theorem tmFiber18ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber18StateAt 3) (tmFiber18StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber18StateAt 3) (tmFiber18StateAt 11)
    (tmFiber18RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber18Key tmFiber18Expected
        (tmFiber18RowAt 11) (by decide) tmFiber18ReverseRow_11_ok
      simpa [tmFiber18StateAt, tmFiber18RowAt, tmFiber18Rows, listGetD, directRow] using h)

theorem tmFiber18ReverseRow_12_ok :
    tmRowReverseValid tmFiber18Key tmFiber18Expected (tmFiber18RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber18Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber18Chunk6] at h
  exact h.1

theorem tmFiber18ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber18StateAt 4) (tmFiber18StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber18StateAt 4) (tmFiber18StateAt 12)
    (tmFiber18RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber18Key tmFiber18Expected
        (tmFiber18RowAt 12) (by decide) tmFiber18ReverseRow_12_ok
      simpa [tmFiber18StateAt, tmFiber18RowAt, tmFiber18Rows, listGetD, directRow] using h)

theorem tmFiber18ReverseRow_13_ok :
    tmRowReverseValid tmFiber18Key tmFiber18Expected (tmFiber18RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber18Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber18Chunk6] at h
  exact h.2

theorem tmFiber18ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber18StateAt 5) (tmFiber18StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber18StateAt 5) (tmFiber18StateAt 13)
    (tmFiber18RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber18Key tmFiber18Expected
        (tmFiber18RowAt 13) (by decide) tmFiber18ReverseRow_13_ok
      simpa [tmFiber18StateAt, tmFiber18RowAt, tmFiber18Rows, listGetD, directRow] using h)

theorem tmFiber18ReverseRow_14_ok :
    tmRowReverseValid tmFiber18Key tmFiber18Expected (tmFiber18RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber18Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber18Chunk7] at h
  exact h.1

theorem tmFiber18ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber18StateAt 6) (tmFiber18StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber18StateAt 6) (tmFiber18StateAt 14)
    (tmFiber18RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber18Key tmFiber18Expected
        (tmFiber18RowAt 14) (by decide) tmFiber18ReverseRow_14_ok
      simpa [tmFiber18StateAt, tmFiber18RowAt, tmFiber18Rows, listGetD, directRow] using h)

theorem tmFiber18ReverseRow_15_ok :
    tmRowReverseValid tmFiber18Key tmFiber18Expected (tmFiber18RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber18Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber18Chunk7] at h
  exact h.2

theorem tmFiber18ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber18StateAt 7) (tmFiber18StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber18StateAt 7) (tmFiber18StateAt 15)
    (tmFiber18RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber18Key tmFiber18Expected
        (tmFiber18RowAt 15) (by decide) tmFiber18ReverseRow_15_ok
      simpa [tmFiber18StateAt, tmFiber18RowAt, tmFiber18Rows, listGetD, directRow] using h)

theorem tmFiber18State0_in_pass1_prefix :
    tmFiber18StateAt 0 ∈ chainClosureStep tmWord [tmFiber18StateAt 0] [tmFiber18StateAt 0] := by
  exact chainClosureStep_mem_of_seen tmWord [tmFiber18StateAt 0] [tmFiber18StateAt 0] (tmFiber18StateAt 0) (by simp)

theorem tmFiber18State1_in_pass1_prefix :
    tmFiber18StateAt 1 ∈ chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1] [tmFiber18StateAt 0] := by
  have hparentBefore :
      tmFiber18StateAt 0 ∈ chainClosureStep tmWord [tmFiber18StateAt 0] [tmFiber18StateAt 0] := by
    exact tmFiber18State0_in_pass1_prefix
  rw [show [tmFiber18StateAt 0, tmFiber18StateAt 1] = [tmFiber18StateAt 0] ++ [tmFiber18StateAt 1] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber18StateAt 1) []
    (chainClosureStep tmWord [tmFiber18StateAt 0] [tmFiber18StateAt 0]) (tmFiber18StateAt 0)
    hparentBefore tmFiber18ReverseSingleStep1

theorem tmFiber18State2_in_pass1_prefix :
    tmFiber18StateAt 2 ∈ chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2] [tmFiber18StateAt 0] := by
  have hparentBefore :
      tmFiber18StateAt 0 ∈ chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1] [tmFiber18StateAt 0] := by
    rw [show [tmFiber18StateAt 0, tmFiber18StateAt 1] = [tmFiber18StateAt 0] ++ [tmFiber18StateAt 1] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber18StateAt 1]
      (chainClosureStep tmWord [tmFiber18StateAt 0] [tmFiber18StateAt 0]) (tmFiber18StateAt 0)
      tmFiber18State0_in_pass1_prefix
  rw [show [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2] = [tmFiber18StateAt 0, tmFiber18StateAt 1] ++ [tmFiber18StateAt 2] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber18StateAt 2) []
    (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1] [tmFiber18StateAt 0]) (tmFiber18StateAt 0)
    hparentBefore tmFiber18ReverseSingleStep2

theorem tmFiber18State3_in_pass1_prefix :
    tmFiber18StateAt 3 ∈ chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3] [tmFiber18StateAt 0] := by
  have hparentBefore :
      tmFiber18StateAt 1 ∈ chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2] [tmFiber18StateAt 0] := by
    rw [show [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2] = [tmFiber18StateAt 0, tmFiber18StateAt 1] ++ [tmFiber18StateAt 2] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber18StateAt 2]
      (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1] [tmFiber18StateAt 0]) (tmFiber18StateAt 1)
      tmFiber18State1_in_pass1_prefix
  rw [show [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3] = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2] ++ [tmFiber18StateAt 3] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber18StateAt 3) []
    (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2] [tmFiber18StateAt 0]) (tmFiber18StateAt 1)
    hparentBefore tmFiber18ReverseSingleStep3

theorem tmFiber18State4_in_pass1_prefix :
    tmFiber18StateAt 4 ∈ chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4] [tmFiber18StateAt 0] := by
  have hparentBefore :
      tmFiber18StateAt 0 ∈ chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3] [tmFiber18StateAt 0] := by
    rw [show [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3] = [tmFiber18StateAt 0] ++ [tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3]
      (chainClosureStep tmWord [tmFiber18StateAt 0] [tmFiber18StateAt 0]) (tmFiber18StateAt 0)
      tmFiber18State0_in_pass1_prefix
  rw [show [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4] = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3] ++ [tmFiber18StateAt 4] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber18StateAt 4) []
    (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3] [tmFiber18StateAt 0]) (tmFiber18StateAt 0)
    hparentBefore tmFiber18ReverseSingleStep4

theorem tmFiber18State5_in_pass1_prefix :
    tmFiber18StateAt 5 ∈ chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5] [tmFiber18StateAt 0] := by
  have hparentBefore :
      tmFiber18StateAt 1 ∈ chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4] [tmFiber18StateAt 0] := by
    rw [show [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4] = [tmFiber18StateAt 0, tmFiber18StateAt 1] ++ [tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4]
      (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1] [tmFiber18StateAt 0]) (tmFiber18StateAt 1)
      tmFiber18State1_in_pass1_prefix
  rw [show [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5] = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4] ++ [tmFiber18StateAt 5] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber18StateAt 5) []
    (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4] [tmFiber18StateAt 0]) (tmFiber18StateAt 1)
    hparentBefore tmFiber18ReverseSingleStep5

theorem tmFiber18State6_in_pass1_prefix :
    tmFiber18StateAt 6 ∈ chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6] [tmFiber18StateAt 0] := by
  have hparentBefore :
      tmFiber18StateAt 2 ∈ chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5] [tmFiber18StateAt 0] := by
    rw [show [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5] = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2] ++ [tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5]
      (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2] [tmFiber18StateAt 0]) (tmFiber18StateAt 2)
      tmFiber18State2_in_pass1_prefix
  rw [show [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6] = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5] ++ [tmFiber18StateAt 6] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber18StateAt 6) []
    (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5] [tmFiber18StateAt 0]) (tmFiber18StateAt 2)
    hparentBefore tmFiber18ReverseSingleStep6

theorem tmFiber18State7_in_pass1_prefix :
    tmFiber18StateAt 7 ∈ chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7] [tmFiber18StateAt 0] := by
  have hparentBefore :
      tmFiber18StateAt 3 ∈ chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6] [tmFiber18StateAt 0] := by
    rw [show [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6] = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3] ++ [tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6]
      (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3] [tmFiber18StateAt 0]) (tmFiber18StateAt 3)
      tmFiber18State3_in_pass1_prefix
  rw [show [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7] = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6] ++ [tmFiber18StateAt 7] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber18StateAt 7) []
    (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6] [tmFiber18StateAt 0]) (tmFiber18StateAt 3)
    hparentBefore tmFiber18ReverseSingleStep7

theorem tmFiber18State8_in_pass1_prefix :
    tmFiber18StateAt 8 ∈ chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8] [tmFiber18StateAt 0] := by
  have hparentBefore :
      tmFiber18StateAt 0 ∈ chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7] [tmFiber18StateAt 0] := by
    rw [show [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7] = [tmFiber18StateAt 0] ++ [tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7]
      (chainClosureStep tmWord [tmFiber18StateAt 0] [tmFiber18StateAt 0]) (tmFiber18StateAt 0)
      tmFiber18State0_in_pass1_prefix
  rw [show [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8] = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7] ++ [tmFiber18StateAt 8] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber18StateAt 8) []
    (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7] [tmFiber18StateAt 0]) (tmFiber18StateAt 0)
    hparentBefore tmFiber18ReverseSingleStep8

theorem tmFiber18State9_in_pass1_prefix :
    tmFiber18StateAt 9 ∈ chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9] [tmFiber18StateAt 0] := by
  have hparentBefore :
      tmFiber18StateAt 1 ∈ chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8] [tmFiber18StateAt 0] := by
    rw [show [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8] = [tmFiber18StateAt 0, tmFiber18StateAt 1] ++ [tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8]
      (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1] [tmFiber18StateAt 0]) (tmFiber18StateAt 1)
      tmFiber18State1_in_pass1_prefix
  rw [show [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9] = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8] ++ [tmFiber18StateAt 9] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber18StateAt 9) []
    (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8] [tmFiber18StateAt 0]) (tmFiber18StateAt 1)
    hparentBefore tmFiber18ReverseSingleStep9

theorem tmFiber18State10_in_pass1_prefix :
    tmFiber18StateAt 10 ∈ chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10] [tmFiber18StateAt 0] := by
  have hparentBefore :
      tmFiber18StateAt 2 ∈ chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9] [tmFiber18StateAt 0] := by
    rw [show [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9] = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2] ++ [tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9]
      (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2] [tmFiber18StateAt 0]) (tmFiber18StateAt 2)
      tmFiber18State2_in_pass1_prefix
  rw [show [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10] = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9] ++ [tmFiber18StateAt 10] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber18StateAt 10) []
    (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9] [tmFiber18StateAt 0]) (tmFiber18StateAt 2)
    hparentBefore tmFiber18ReverseSingleStep10

theorem tmFiber18State11_in_pass1_prefix :
    tmFiber18StateAt 11 ∈ chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11] [tmFiber18StateAt 0] := by
  have hparentBefore :
      tmFiber18StateAt 3 ∈ chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10] [tmFiber18StateAt 0] := by
    rw [show [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10] = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3] ++ [tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10]
      (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3] [tmFiber18StateAt 0]) (tmFiber18StateAt 3)
      tmFiber18State3_in_pass1_prefix
  rw [show [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11] = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10] ++ [tmFiber18StateAt 11] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber18StateAt 11) []
    (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10] [tmFiber18StateAt 0]) (tmFiber18StateAt 3)
    hparentBefore tmFiber18ReverseSingleStep11

theorem tmFiber18State12_in_pass1_prefix :
    tmFiber18StateAt 12 ∈ chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12] [tmFiber18StateAt 0] := by
  have hparentBefore :
      tmFiber18StateAt 4 ∈ chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11] [tmFiber18StateAt 0] := by
    rw [show [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11] = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4] ++ [tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11]
      (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4] [tmFiber18StateAt 0]) (tmFiber18StateAt 4)
      tmFiber18State4_in_pass1_prefix
  rw [show [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12] = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11] ++ [tmFiber18StateAt 12] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber18StateAt 12) []
    (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11] [tmFiber18StateAt 0]) (tmFiber18StateAt 4)
    hparentBefore tmFiber18ReverseSingleStep12

theorem tmFiber18State13_in_pass1_prefix :
    tmFiber18StateAt 13 ∈ chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13] [tmFiber18StateAt 0] := by
  have hparentBefore :
      tmFiber18StateAt 5 ∈ chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12] [tmFiber18StateAt 0] := by
    rw [show [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12] = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5] ++ [tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12]
      (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5] [tmFiber18StateAt 0]) (tmFiber18StateAt 5)
      tmFiber18State5_in_pass1_prefix
  rw [show [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13] = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12] ++ [tmFiber18StateAt 13] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber18StateAt 13) []
    (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12] [tmFiber18StateAt 0]) (tmFiber18StateAt 5)
    hparentBefore tmFiber18ReverseSingleStep13

theorem tmFiber18State14_in_pass1_prefix :
    tmFiber18StateAt 14 ∈ chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14] [tmFiber18StateAt 0] := by
  have hparentBefore :
      tmFiber18StateAt 6 ∈ chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13] [tmFiber18StateAt 0] := by
    rw [show [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13] = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6] ++ [tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13]
      (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6] [tmFiber18StateAt 0]) (tmFiber18StateAt 6)
      tmFiber18State6_in_pass1_prefix
  rw [show [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14] = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13] ++ [tmFiber18StateAt 14] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber18StateAt 14) []
    (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13] [tmFiber18StateAt 0]) (tmFiber18StateAt 6)
    hparentBefore tmFiber18ReverseSingleStep14

theorem tmFiber18State15_in_pass1_prefix :
    tmFiber18StateAt 15 ∈ chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14, tmFiber18StateAt 15] [tmFiber18StateAt 0] := by
  have hparentBefore :
      tmFiber18StateAt 7 ∈ chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14] [tmFiber18StateAt 0] := by
    rw [show [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14] = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7] ++ [tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14]
      (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7] [tmFiber18StateAt 0]) (tmFiber18StateAt 7)
      tmFiber18State7_in_pass1_prefix
  rw [show [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14, tmFiber18StateAt 15] = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14] ++ [tmFiber18StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber18StateAt 15) []
    (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14] [tmFiber18StateAt 0]) (tmFiber18StateAt 7)
    hparentBefore tmFiber18ReverseSingleStep15

theorem tmFiber18State0_in_pass1_full :
    tmFiber18StateAt 0 ∈ chainClosureStep tmWord tmFiber18DirectStates [tmFiber18StateAt 0] := by
  rw [show tmFiber18DirectStates = [tmFiber18StateAt 0] ++ [tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14, tmFiber18StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14, tmFiber18StateAt 15]
    (chainClosureStep tmWord [tmFiber18StateAt 0] [tmFiber18StateAt 0]) (tmFiber18StateAt 0)
    tmFiber18State0_in_pass1_prefix

theorem tmFiber18State1_in_pass1_full :
    tmFiber18StateAt 1 ∈ chainClosureStep tmWord tmFiber18DirectStates [tmFiber18StateAt 0] := by
  rw [show tmFiber18DirectStates = [tmFiber18StateAt 0, tmFiber18StateAt 1] ++ [tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14, tmFiber18StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14, tmFiber18StateAt 15]
    (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1] [tmFiber18StateAt 0]) (tmFiber18StateAt 1)
    tmFiber18State1_in_pass1_prefix

theorem tmFiber18State2_in_pass1_full :
    tmFiber18StateAt 2 ∈ chainClosureStep tmWord tmFiber18DirectStates [tmFiber18StateAt 0] := by
  rw [show tmFiber18DirectStates = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2] ++ [tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14, tmFiber18StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14, tmFiber18StateAt 15]
    (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2] [tmFiber18StateAt 0]) (tmFiber18StateAt 2)
    tmFiber18State2_in_pass1_prefix

theorem tmFiber18State3_in_pass1_full :
    tmFiber18StateAt 3 ∈ chainClosureStep tmWord tmFiber18DirectStates [tmFiber18StateAt 0] := by
  rw [show tmFiber18DirectStates = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3] ++ [tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14, tmFiber18StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14, tmFiber18StateAt 15]
    (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3] [tmFiber18StateAt 0]) (tmFiber18StateAt 3)
    tmFiber18State3_in_pass1_prefix

theorem tmFiber18State4_in_pass1_full :
    tmFiber18StateAt 4 ∈ chainClosureStep tmWord tmFiber18DirectStates [tmFiber18StateAt 0] := by
  rw [show tmFiber18DirectStates = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4] ++ [tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14, tmFiber18StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14, tmFiber18StateAt 15]
    (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4] [tmFiber18StateAt 0]) (tmFiber18StateAt 4)
    tmFiber18State4_in_pass1_prefix

theorem tmFiber18State5_in_pass1_full :
    tmFiber18StateAt 5 ∈ chainClosureStep tmWord tmFiber18DirectStates [tmFiber18StateAt 0] := by
  rw [show tmFiber18DirectStates = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5] ++ [tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14, tmFiber18StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14, tmFiber18StateAt 15]
    (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5] [tmFiber18StateAt 0]) (tmFiber18StateAt 5)
    tmFiber18State5_in_pass1_prefix

theorem tmFiber18State6_in_pass1_full :
    tmFiber18StateAt 6 ∈ chainClosureStep tmWord tmFiber18DirectStates [tmFiber18StateAt 0] := by
  rw [show tmFiber18DirectStates = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6] ++ [tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14, tmFiber18StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14, tmFiber18StateAt 15]
    (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6] [tmFiber18StateAt 0]) (tmFiber18StateAt 6)
    tmFiber18State6_in_pass1_prefix

theorem tmFiber18State7_in_pass1_full :
    tmFiber18StateAt 7 ∈ chainClosureStep tmWord tmFiber18DirectStates [tmFiber18StateAt 0] := by
  rw [show tmFiber18DirectStates = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7] ++ [tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14, tmFiber18StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14, tmFiber18StateAt 15]
    (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7] [tmFiber18StateAt 0]) (tmFiber18StateAt 7)
    tmFiber18State7_in_pass1_prefix

theorem tmFiber18State8_in_pass1_full :
    tmFiber18StateAt 8 ∈ chainClosureStep tmWord tmFiber18DirectStates [tmFiber18StateAt 0] := by
  rw [show tmFiber18DirectStates = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8] ++ [tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14, tmFiber18StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14, tmFiber18StateAt 15]
    (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8] [tmFiber18StateAt 0]) (tmFiber18StateAt 8)
    tmFiber18State8_in_pass1_prefix

theorem tmFiber18State9_in_pass1_full :
    tmFiber18StateAt 9 ∈ chainClosureStep tmWord tmFiber18DirectStates [tmFiber18StateAt 0] := by
  rw [show tmFiber18DirectStates = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9] ++ [tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14, tmFiber18StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14, tmFiber18StateAt 15]
    (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9] [tmFiber18StateAt 0]) (tmFiber18StateAt 9)
    tmFiber18State9_in_pass1_prefix

theorem tmFiber18State10_in_pass1_full :
    tmFiber18StateAt 10 ∈ chainClosureStep tmWord tmFiber18DirectStates [tmFiber18StateAt 0] := by
  rw [show tmFiber18DirectStates = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10] ++ [tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14, tmFiber18StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14, tmFiber18StateAt 15]
    (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10] [tmFiber18StateAt 0]) (tmFiber18StateAt 10)
    tmFiber18State10_in_pass1_prefix

theorem tmFiber18State11_in_pass1_full :
    tmFiber18StateAt 11 ∈ chainClosureStep tmWord tmFiber18DirectStates [tmFiber18StateAt 0] := by
  rw [show tmFiber18DirectStates = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11] ++ [tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14, tmFiber18StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14, tmFiber18StateAt 15]
    (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11] [tmFiber18StateAt 0]) (tmFiber18StateAt 11)
    tmFiber18State11_in_pass1_prefix

theorem tmFiber18State12_in_pass1_full :
    tmFiber18StateAt 12 ∈ chainClosureStep tmWord tmFiber18DirectStates [tmFiber18StateAt 0] := by
  rw [show tmFiber18DirectStates = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12] ++ [tmFiber18StateAt 13, tmFiber18StateAt 14, tmFiber18StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber18StateAt 13, tmFiber18StateAt 14, tmFiber18StateAt 15]
    (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12] [tmFiber18StateAt 0]) (tmFiber18StateAt 12)
    tmFiber18State12_in_pass1_prefix

theorem tmFiber18State13_in_pass1_full :
    tmFiber18StateAt 13 ∈ chainClosureStep tmWord tmFiber18DirectStates [tmFiber18StateAt 0] := by
  rw [show tmFiber18DirectStates = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13] ++ [tmFiber18StateAt 14, tmFiber18StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber18StateAt 14, tmFiber18StateAt 15]
    (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13] [tmFiber18StateAt 0]) (tmFiber18StateAt 13)
    tmFiber18State13_in_pass1_prefix

theorem tmFiber18State14_in_pass1_full :
    tmFiber18StateAt 14 ∈ chainClosureStep tmWord tmFiber18DirectStates [tmFiber18StateAt 0] := by
  rw [show tmFiber18DirectStates = [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14] ++ [tmFiber18StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber18StateAt 15]
    (chainClosureStep tmWord [tmFiber18StateAt 0, tmFiber18StateAt 1, tmFiber18StateAt 2, tmFiber18StateAt 3, tmFiber18StateAt 4, tmFiber18StateAt 5, tmFiber18StateAt 6, tmFiber18StateAt 7, tmFiber18StateAt 8, tmFiber18StateAt 9, tmFiber18StateAt 10, tmFiber18StateAt 11, tmFiber18StateAt 12, tmFiber18StateAt 13, tmFiber18StateAt 14] [tmFiber18StateAt 0]) (tmFiber18StateAt 14)
    tmFiber18State14_in_pass1_prefix

theorem tmFiber18State15_in_pass1_full :
    tmFiber18StateAt 15 ∈ chainClosureStep tmWord tmFiber18DirectStates [tmFiber18StateAt 0] := by
  simpa [tmFiber18DirectStates] using tmFiber18State15_in_pass1_prefix

theorem tmFiber18State0_in_close :
    tmFiber18StateAt 0 ∈ closeChainFiber tmWord tmFiber18DirectStates tmFiber18DirectStates.length [tmFiber18StateAt 0] := by
  change tmFiber18StateAt 0 ∈ closeChainFiber tmWord tmFiber18DirectStates (15 + 1) [tmFiber18StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber18DirectStates 15 [tmFiber18StateAt 0] (tmFiber18StateAt 0) tmFiber18State0_in_pass1_full

theorem tmFiber18State1_in_close :
    tmFiber18StateAt 1 ∈ closeChainFiber tmWord tmFiber18DirectStates tmFiber18DirectStates.length [tmFiber18StateAt 0] := by
  change tmFiber18StateAt 1 ∈ closeChainFiber tmWord tmFiber18DirectStates (15 + 1) [tmFiber18StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber18DirectStates 15 [tmFiber18StateAt 0] (tmFiber18StateAt 1) tmFiber18State1_in_pass1_full

theorem tmFiber18State2_in_close :
    tmFiber18StateAt 2 ∈ closeChainFiber tmWord tmFiber18DirectStates tmFiber18DirectStates.length [tmFiber18StateAt 0] := by
  change tmFiber18StateAt 2 ∈ closeChainFiber tmWord tmFiber18DirectStates (15 + 1) [tmFiber18StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber18DirectStates 15 [tmFiber18StateAt 0] (tmFiber18StateAt 2) tmFiber18State2_in_pass1_full

theorem tmFiber18State3_in_close :
    tmFiber18StateAt 3 ∈ closeChainFiber tmWord tmFiber18DirectStates tmFiber18DirectStates.length [tmFiber18StateAt 0] := by
  change tmFiber18StateAt 3 ∈ closeChainFiber tmWord tmFiber18DirectStates (15 + 1) [tmFiber18StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber18DirectStates 15 [tmFiber18StateAt 0] (tmFiber18StateAt 3) tmFiber18State3_in_pass1_full

theorem tmFiber18State4_in_close :
    tmFiber18StateAt 4 ∈ closeChainFiber tmWord tmFiber18DirectStates tmFiber18DirectStates.length [tmFiber18StateAt 0] := by
  change tmFiber18StateAt 4 ∈ closeChainFiber tmWord tmFiber18DirectStates (15 + 1) [tmFiber18StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber18DirectStates 15 [tmFiber18StateAt 0] (tmFiber18StateAt 4) tmFiber18State4_in_pass1_full

theorem tmFiber18State5_in_close :
    tmFiber18StateAt 5 ∈ closeChainFiber tmWord tmFiber18DirectStates tmFiber18DirectStates.length [tmFiber18StateAt 0] := by
  change tmFiber18StateAt 5 ∈ closeChainFiber tmWord tmFiber18DirectStates (15 + 1) [tmFiber18StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber18DirectStates 15 [tmFiber18StateAt 0] (tmFiber18StateAt 5) tmFiber18State5_in_pass1_full

theorem tmFiber18State6_in_close :
    tmFiber18StateAt 6 ∈ closeChainFiber tmWord tmFiber18DirectStates tmFiber18DirectStates.length [tmFiber18StateAt 0] := by
  change tmFiber18StateAt 6 ∈ closeChainFiber tmWord tmFiber18DirectStates (15 + 1) [tmFiber18StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber18DirectStates 15 [tmFiber18StateAt 0] (tmFiber18StateAt 6) tmFiber18State6_in_pass1_full

theorem tmFiber18State7_in_close :
    tmFiber18StateAt 7 ∈ closeChainFiber tmWord tmFiber18DirectStates tmFiber18DirectStates.length [tmFiber18StateAt 0] := by
  change tmFiber18StateAt 7 ∈ closeChainFiber tmWord tmFiber18DirectStates (15 + 1) [tmFiber18StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber18DirectStates 15 [tmFiber18StateAt 0] (tmFiber18StateAt 7) tmFiber18State7_in_pass1_full

theorem tmFiber18State8_in_close :
    tmFiber18StateAt 8 ∈ closeChainFiber tmWord tmFiber18DirectStates tmFiber18DirectStates.length [tmFiber18StateAt 0] := by
  change tmFiber18StateAt 8 ∈ closeChainFiber tmWord tmFiber18DirectStates (15 + 1) [tmFiber18StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber18DirectStates 15 [tmFiber18StateAt 0] (tmFiber18StateAt 8) tmFiber18State8_in_pass1_full

theorem tmFiber18State9_in_close :
    tmFiber18StateAt 9 ∈ closeChainFiber tmWord tmFiber18DirectStates tmFiber18DirectStates.length [tmFiber18StateAt 0] := by
  change tmFiber18StateAt 9 ∈ closeChainFiber tmWord tmFiber18DirectStates (15 + 1) [tmFiber18StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber18DirectStates 15 [tmFiber18StateAt 0] (tmFiber18StateAt 9) tmFiber18State9_in_pass1_full

theorem tmFiber18State10_in_close :
    tmFiber18StateAt 10 ∈ closeChainFiber tmWord tmFiber18DirectStates tmFiber18DirectStates.length [tmFiber18StateAt 0] := by
  change tmFiber18StateAt 10 ∈ closeChainFiber tmWord tmFiber18DirectStates (15 + 1) [tmFiber18StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber18DirectStates 15 [tmFiber18StateAt 0] (tmFiber18StateAt 10) tmFiber18State10_in_pass1_full

theorem tmFiber18State11_in_close :
    tmFiber18StateAt 11 ∈ closeChainFiber tmWord tmFiber18DirectStates tmFiber18DirectStates.length [tmFiber18StateAt 0] := by
  change tmFiber18StateAt 11 ∈ closeChainFiber tmWord tmFiber18DirectStates (15 + 1) [tmFiber18StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber18DirectStates 15 [tmFiber18StateAt 0] (tmFiber18StateAt 11) tmFiber18State11_in_pass1_full

theorem tmFiber18State12_in_close :
    tmFiber18StateAt 12 ∈ closeChainFiber tmWord tmFiber18DirectStates tmFiber18DirectStates.length [tmFiber18StateAt 0] := by
  change tmFiber18StateAt 12 ∈ closeChainFiber tmWord tmFiber18DirectStates (15 + 1) [tmFiber18StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber18DirectStates 15 [tmFiber18StateAt 0] (tmFiber18StateAt 12) tmFiber18State12_in_pass1_full

theorem tmFiber18State13_in_close :
    tmFiber18StateAt 13 ∈ closeChainFiber tmWord tmFiber18DirectStates tmFiber18DirectStates.length [tmFiber18StateAt 0] := by
  change tmFiber18StateAt 13 ∈ closeChainFiber tmWord tmFiber18DirectStates (15 + 1) [tmFiber18StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber18DirectStates 15 [tmFiber18StateAt 0] (tmFiber18StateAt 13) tmFiber18State13_in_pass1_full

theorem tmFiber18State14_in_close :
    tmFiber18StateAt 14 ∈ closeChainFiber tmWord tmFiber18DirectStates tmFiber18DirectStates.length [tmFiber18StateAt 0] := by
  change tmFiber18StateAt 14 ∈ closeChainFiber tmWord tmFiber18DirectStates (15 + 1) [tmFiber18StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber18DirectStates 15 [tmFiber18StateAt 0] (tmFiber18StateAt 14) tmFiber18State14_in_pass1_full

theorem tmFiber18State15_in_close :
    tmFiber18StateAt 15 ∈ closeChainFiber tmWord tmFiber18DirectStates tmFiber18DirectStates.length [tmFiber18StateAt 0] := by
  change tmFiber18StateAt 15 ∈ closeChainFiber tmWord tmFiber18DirectStates (15 + 1) [tmFiber18StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber18DirectStates 15 [tmFiber18StateAt 0] (tmFiber18StateAt 15) tmFiber18State15_in_pass1_full

theorem tmFiber18DirectConnected :
    chainFiberConnected tmWord tmFiber18DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber18DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber18State0_in_close
  · subst state
    exact tmFiber18State1_in_close
  · subst state
    exact tmFiber18State2_in_close
  · subst state
    exact tmFiber18State3_in_close
  · subst state
    exact tmFiber18State4_in_close
  · subst state
    exact tmFiber18State5_in_close
  · subst state
    exact tmFiber18State6_in_close
  · subst state
    exact tmFiber18State7_in_close
  · subst state
    exact tmFiber18State8_in_close
  · subst state
    exact tmFiber18State9_in_close
  · subst state
    exact tmFiber18State10_in_close
  · subst state
    exact tmFiber18State11_in_close
  · subst state
    exact tmFiber18State12_in_close
  · subst state
    exact tmFiber18State13_in_close
  · subst state
    exact tmFiber18State14_in_close
  · subst state
    exact tmFiber18State15_in_close
  · cases h

def tmFiber19StateAt (i : Nat) : List TauState :=
  directStates (tmFiber19RowAt i).sourceLeft (tmFiber19RowAt i).sourceRight

def tmFiber19DirectStates : List (List TauState) :=
  [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14, tmFiber19StateAt 15]

theorem tmFiber19ReverseRow_1_ok :
    tmRowReverseValid tmFiber19Key tmFiber19Expected (tmFiber19RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber19Chunk0_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber19Chunk0] at h
  exact h.2

theorem tmFiber19ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber19StateAt 0) (tmFiber19StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber19StateAt 0) (tmFiber19StateAt 1)
    (tmFiber19RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber19Key tmFiber19Expected
        (tmFiber19RowAt 1) (by decide) tmFiber19ReverseRow_1_ok
      simpa [tmFiber19StateAt, tmFiber19RowAt, tmFiber19Rows, listGetD, directRow] using h)

theorem tmFiber19ReverseRow_2_ok :
    tmRowReverseValid tmFiber19Key tmFiber19Expected (tmFiber19RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber19Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber19Chunk1] at h
  exact h.1

theorem tmFiber19ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber19StateAt 0) (tmFiber19StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber19StateAt 0) (tmFiber19StateAt 2)
    (tmFiber19RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber19Key tmFiber19Expected
        (tmFiber19RowAt 2) (by decide) tmFiber19ReverseRow_2_ok
      simpa [tmFiber19StateAt, tmFiber19RowAt, tmFiber19Rows, listGetD, directRow] using h)

theorem tmFiber19ReverseRow_3_ok :
    tmRowReverseValid tmFiber19Key tmFiber19Expected (tmFiber19RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber19Chunk1_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber19Chunk1] at h
  exact h.2

theorem tmFiber19ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber19StateAt 1) (tmFiber19StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber19StateAt 1) (tmFiber19StateAt 3)
    (tmFiber19RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber19Key tmFiber19Expected
        (tmFiber19RowAt 3) (by decide) tmFiber19ReverseRow_3_ok
      simpa [tmFiber19StateAt, tmFiber19RowAt, tmFiber19Rows, listGetD, directRow] using h)

theorem tmFiber19ReverseRow_4_ok :
    tmRowReverseValid tmFiber19Key tmFiber19Expected (tmFiber19RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber19Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber19Chunk2] at h
  exact h.1

theorem tmFiber19ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber19StateAt 0) (tmFiber19StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber19StateAt 0) (tmFiber19StateAt 4)
    (tmFiber19RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber19Key tmFiber19Expected
        (tmFiber19RowAt 4) (by decide) tmFiber19ReverseRow_4_ok
      simpa [tmFiber19StateAt, tmFiber19RowAt, tmFiber19Rows, listGetD, directRow] using h)

theorem tmFiber19ReverseRow_5_ok :
    tmRowReverseValid tmFiber19Key tmFiber19Expected (tmFiber19RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber19Chunk2_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber19Chunk2] at h
  exact h.2

theorem tmFiber19ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber19StateAt 1) (tmFiber19StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber19StateAt 1) (tmFiber19StateAt 5)
    (tmFiber19RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber19Key tmFiber19Expected
        (tmFiber19RowAt 5) (by decide) tmFiber19ReverseRow_5_ok
      simpa [tmFiber19StateAt, tmFiber19RowAt, tmFiber19Rows, listGetD, directRow] using h)

theorem tmFiber19ReverseRow_6_ok :
    tmRowReverseValid tmFiber19Key tmFiber19Expected (tmFiber19RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber19Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber19Chunk3] at h
  exact h.1

theorem tmFiber19ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber19StateAt 2) (tmFiber19StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber19StateAt 2) (tmFiber19StateAt 6)
    (tmFiber19RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber19Key tmFiber19Expected
        (tmFiber19RowAt 6) (by decide) tmFiber19ReverseRow_6_ok
      simpa [tmFiber19StateAt, tmFiber19RowAt, tmFiber19Rows, listGetD, directRow] using h)

theorem tmFiber19ReverseRow_7_ok :
    tmRowReverseValid tmFiber19Key tmFiber19Expected (tmFiber19RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber19Chunk3_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber19Chunk3] at h
  exact h.2

theorem tmFiber19ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber19StateAt 3) (tmFiber19StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber19StateAt 3) (tmFiber19StateAt 7)
    (tmFiber19RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber19Key tmFiber19Expected
        (tmFiber19RowAt 7) (by decide) tmFiber19ReverseRow_7_ok
      simpa [tmFiber19StateAt, tmFiber19RowAt, tmFiber19Rows, listGetD, directRow] using h)

theorem tmFiber19ReverseRow_8_ok :
    tmRowReverseValid tmFiber19Key tmFiber19Expected (tmFiber19RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber19Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber19Chunk4] at h
  exact h.1

theorem tmFiber19ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber19StateAt 4) (tmFiber19StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber19StateAt 4) (tmFiber19StateAt 8)
    (tmFiber19RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber19Key tmFiber19Expected
        (tmFiber19RowAt 8) (by decide) tmFiber19ReverseRow_8_ok
      simpa [tmFiber19StateAt, tmFiber19RowAt, tmFiber19Rows, listGetD, directRow] using h)

theorem tmFiber19ReverseRow_9_ok :
    tmRowReverseValid tmFiber19Key tmFiber19Expected (tmFiber19RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber19Chunk4_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber19Chunk4] at h
  exact h.2

theorem tmFiber19ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber19StateAt 5) (tmFiber19StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber19StateAt 5) (tmFiber19StateAt 9)
    (tmFiber19RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber19Key tmFiber19Expected
        (tmFiber19RowAt 9) (by decide) tmFiber19ReverseRow_9_ok
      simpa [tmFiber19StateAt, tmFiber19RowAt, tmFiber19Rows, listGetD, directRow] using h)

theorem tmFiber19ReverseRow_10_ok :
    tmRowReverseValid tmFiber19Key tmFiber19Expected (tmFiber19RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber19Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber19Chunk5] at h
  exact h.1

theorem tmFiber19ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber19StateAt 6) (tmFiber19StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber19StateAt 6) (tmFiber19StateAt 10)
    (tmFiber19RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber19Key tmFiber19Expected
        (tmFiber19RowAt 10) (by decide) tmFiber19ReverseRow_10_ok
      simpa [tmFiber19StateAt, tmFiber19RowAt, tmFiber19Rows, listGetD, directRow] using h)

theorem tmFiber19ReverseRow_11_ok :
    tmRowReverseValid tmFiber19Key tmFiber19Expected (tmFiber19RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber19Chunk5_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber19Chunk5] at h
  exact h.2

theorem tmFiber19ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber19StateAt 7) (tmFiber19StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber19StateAt 7) (tmFiber19StateAt 11)
    (tmFiber19RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber19Key tmFiber19Expected
        (tmFiber19RowAt 11) (by decide) tmFiber19ReverseRow_11_ok
      simpa [tmFiber19StateAt, tmFiber19RowAt, tmFiber19Rows, listGetD, directRow] using h)

theorem tmFiber19ReverseRow_12_ok :
    tmRowReverseValid tmFiber19Key tmFiber19Expected (tmFiber19RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber19Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber19Chunk6] at h
  exact h.1

theorem tmFiber19ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber19StateAt 0) (tmFiber19StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber19StateAt 0) (tmFiber19StateAt 12)
    (tmFiber19RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber19Key tmFiber19Expected
        (tmFiber19RowAt 12) (by decide) tmFiber19ReverseRow_12_ok
      simpa [tmFiber19StateAt, tmFiber19RowAt, tmFiber19Rows, listGetD, directRow] using h)

theorem tmFiber19ReverseRow_13_ok :
    tmRowReverseValid tmFiber19Key tmFiber19Expected (tmFiber19RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber19Chunk6_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber19Chunk6] at h
  exact h.2

theorem tmFiber19ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber19StateAt 1) (tmFiber19StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber19StateAt 1) (tmFiber19StateAt 13)
    (tmFiber19RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber19Key tmFiber19Expected
        (tmFiber19RowAt 13) (by decide) tmFiber19ReverseRow_13_ok
      simpa [tmFiber19StateAt, tmFiber19RowAt, tmFiber19Rows, listGetD, directRow] using h)

theorem tmFiber19ReverseRow_14_ok :
    tmRowReverseValid tmFiber19Key tmFiber19Expected (tmFiber19RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber19Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber19Chunk7] at h
  exact h.1

theorem tmFiber19ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber19StateAt 2) (tmFiber19StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber19StateAt 2) (tmFiber19StateAt 14)
    (tmFiber19RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber19Key tmFiber19Expected
        (tmFiber19RowAt 14) (by decide) tmFiber19ReverseRow_14_ok
      simpa [tmFiber19StateAt, tmFiber19RowAt, tmFiber19Rows, listGetD, directRow] using h)

theorem tmFiber19ReverseRow_15_ok :
    tmRowReverseValid tmFiber19Key tmFiber19Expected (tmFiber19RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber19Chunk7_ok
  simp [GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber19Chunk7] at h
  exact h.2

theorem tmFiber19ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber19StateAt 3) (tmFiber19StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber19StateAt 3) (tmFiber19StateAt 15)
    (tmFiber19RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber19Key tmFiber19Expected
        (tmFiber19RowAt 15) (by decide) tmFiber19ReverseRow_15_ok
      simpa [tmFiber19StateAt, tmFiber19RowAt, tmFiber19Rows, listGetD, directRow] using h)

theorem tmFiber19State0_in_pass1_prefix :
    tmFiber19StateAt 0 ∈ chainClosureStep tmWord [tmFiber19StateAt 0] [tmFiber19StateAt 0] := by
  exact chainClosureStep_mem_of_seen tmWord [tmFiber19StateAt 0] [tmFiber19StateAt 0] (tmFiber19StateAt 0) (by simp)

theorem tmFiber19State1_in_pass1_prefix :
    tmFiber19StateAt 1 ∈ chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1] [tmFiber19StateAt 0] := by
  have hparentBefore :
      tmFiber19StateAt 0 ∈ chainClosureStep tmWord [tmFiber19StateAt 0] [tmFiber19StateAt 0] := by
    exact tmFiber19State0_in_pass1_prefix
  rw [show [tmFiber19StateAt 0, tmFiber19StateAt 1] = [tmFiber19StateAt 0] ++ [tmFiber19StateAt 1] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber19StateAt 1) []
    (chainClosureStep tmWord [tmFiber19StateAt 0] [tmFiber19StateAt 0]) (tmFiber19StateAt 0)
    hparentBefore tmFiber19ReverseSingleStep1

theorem tmFiber19State2_in_pass1_prefix :
    tmFiber19StateAt 2 ∈ chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2] [tmFiber19StateAt 0] := by
  have hparentBefore :
      tmFiber19StateAt 0 ∈ chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1] [tmFiber19StateAt 0] := by
    rw [show [tmFiber19StateAt 0, tmFiber19StateAt 1] = [tmFiber19StateAt 0] ++ [tmFiber19StateAt 1] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber19StateAt 1]
      (chainClosureStep tmWord [tmFiber19StateAt 0] [tmFiber19StateAt 0]) (tmFiber19StateAt 0)
      tmFiber19State0_in_pass1_prefix
  rw [show [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2] = [tmFiber19StateAt 0, tmFiber19StateAt 1] ++ [tmFiber19StateAt 2] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber19StateAt 2) []
    (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1] [tmFiber19StateAt 0]) (tmFiber19StateAt 0)
    hparentBefore tmFiber19ReverseSingleStep2

theorem tmFiber19State3_in_pass1_prefix :
    tmFiber19StateAt 3 ∈ chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3] [tmFiber19StateAt 0] := by
  have hparentBefore :
      tmFiber19StateAt 1 ∈ chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2] [tmFiber19StateAt 0] := by
    rw [show [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2] = [tmFiber19StateAt 0, tmFiber19StateAt 1] ++ [tmFiber19StateAt 2] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber19StateAt 2]
      (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1] [tmFiber19StateAt 0]) (tmFiber19StateAt 1)
      tmFiber19State1_in_pass1_prefix
  rw [show [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3] = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2] ++ [tmFiber19StateAt 3] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber19StateAt 3) []
    (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2] [tmFiber19StateAt 0]) (tmFiber19StateAt 1)
    hparentBefore tmFiber19ReverseSingleStep3

theorem tmFiber19State4_in_pass1_prefix :
    tmFiber19StateAt 4 ∈ chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4] [tmFiber19StateAt 0] := by
  have hparentBefore :
      tmFiber19StateAt 0 ∈ chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3] [tmFiber19StateAt 0] := by
    rw [show [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3] = [tmFiber19StateAt 0] ++ [tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3]
      (chainClosureStep tmWord [tmFiber19StateAt 0] [tmFiber19StateAt 0]) (tmFiber19StateAt 0)
      tmFiber19State0_in_pass1_prefix
  rw [show [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4] = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3] ++ [tmFiber19StateAt 4] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber19StateAt 4) []
    (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3] [tmFiber19StateAt 0]) (tmFiber19StateAt 0)
    hparentBefore tmFiber19ReverseSingleStep4

theorem tmFiber19State5_in_pass1_prefix :
    tmFiber19StateAt 5 ∈ chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5] [tmFiber19StateAt 0] := by
  have hparentBefore :
      tmFiber19StateAt 1 ∈ chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4] [tmFiber19StateAt 0] := by
    rw [show [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4] = [tmFiber19StateAt 0, tmFiber19StateAt 1] ++ [tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4]
      (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1] [tmFiber19StateAt 0]) (tmFiber19StateAt 1)
      tmFiber19State1_in_pass1_prefix
  rw [show [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5] = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4] ++ [tmFiber19StateAt 5] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber19StateAt 5) []
    (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4] [tmFiber19StateAt 0]) (tmFiber19StateAt 1)
    hparentBefore tmFiber19ReverseSingleStep5

theorem tmFiber19State6_in_pass1_prefix :
    tmFiber19StateAt 6 ∈ chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6] [tmFiber19StateAt 0] := by
  have hparentBefore :
      tmFiber19StateAt 2 ∈ chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5] [tmFiber19StateAt 0] := by
    rw [show [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5] = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2] ++ [tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5]
      (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2] [tmFiber19StateAt 0]) (tmFiber19StateAt 2)
      tmFiber19State2_in_pass1_prefix
  rw [show [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6] = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5] ++ [tmFiber19StateAt 6] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber19StateAt 6) []
    (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5] [tmFiber19StateAt 0]) (tmFiber19StateAt 2)
    hparentBefore tmFiber19ReverseSingleStep6

theorem tmFiber19State7_in_pass1_prefix :
    tmFiber19StateAt 7 ∈ chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7] [tmFiber19StateAt 0] := by
  have hparentBefore :
      tmFiber19StateAt 3 ∈ chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6] [tmFiber19StateAt 0] := by
    rw [show [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6] = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3] ++ [tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6]
      (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3] [tmFiber19StateAt 0]) (tmFiber19StateAt 3)
      tmFiber19State3_in_pass1_prefix
  rw [show [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7] = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6] ++ [tmFiber19StateAt 7] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber19StateAt 7) []
    (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6] [tmFiber19StateAt 0]) (tmFiber19StateAt 3)
    hparentBefore tmFiber19ReverseSingleStep7

theorem tmFiber19State8_in_pass1_prefix :
    tmFiber19StateAt 8 ∈ chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8] [tmFiber19StateAt 0] := by
  have hparentBefore :
      tmFiber19StateAt 4 ∈ chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7] [tmFiber19StateAt 0] := by
    rw [show [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7] = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4] ++ [tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7]
      (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4] [tmFiber19StateAt 0]) (tmFiber19StateAt 4)
      tmFiber19State4_in_pass1_prefix
  rw [show [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8] = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7] ++ [tmFiber19StateAt 8] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber19StateAt 8) []
    (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7] [tmFiber19StateAt 0]) (tmFiber19StateAt 4)
    hparentBefore tmFiber19ReverseSingleStep8

theorem tmFiber19State9_in_pass1_prefix :
    tmFiber19StateAt 9 ∈ chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9] [tmFiber19StateAt 0] := by
  have hparentBefore :
      tmFiber19StateAt 5 ∈ chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8] [tmFiber19StateAt 0] := by
    rw [show [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8] = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5] ++ [tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8]
      (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5] [tmFiber19StateAt 0]) (tmFiber19StateAt 5)
      tmFiber19State5_in_pass1_prefix
  rw [show [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9] = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8] ++ [tmFiber19StateAt 9] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber19StateAt 9) []
    (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8] [tmFiber19StateAt 0]) (tmFiber19StateAt 5)
    hparentBefore tmFiber19ReverseSingleStep9

theorem tmFiber19State10_in_pass1_prefix :
    tmFiber19StateAt 10 ∈ chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10] [tmFiber19StateAt 0] := by
  have hparentBefore :
      tmFiber19StateAt 6 ∈ chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9] [tmFiber19StateAt 0] := by
    rw [show [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9] = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6] ++ [tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9]
      (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6] [tmFiber19StateAt 0]) (tmFiber19StateAt 6)
      tmFiber19State6_in_pass1_prefix
  rw [show [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10] = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9] ++ [tmFiber19StateAt 10] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber19StateAt 10) []
    (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9] [tmFiber19StateAt 0]) (tmFiber19StateAt 6)
    hparentBefore tmFiber19ReverseSingleStep10

theorem tmFiber19State11_in_pass1_prefix :
    tmFiber19StateAt 11 ∈ chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11] [tmFiber19StateAt 0] := by
  have hparentBefore :
      tmFiber19StateAt 7 ∈ chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10] [tmFiber19StateAt 0] := by
    rw [show [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10] = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7] ++ [tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10]
      (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7] [tmFiber19StateAt 0]) (tmFiber19StateAt 7)
      tmFiber19State7_in_pass1_prefix
  rw [show [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11] = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10] ++ [tmFiber19StateAt 11] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber19StateAt 11) []
    (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10] [tmFiber19StateAt 0]) (tmFiber19StateAt 7)
    hparentBefore tmFiber19ReverseSingleStep11

theorem tmFiber19State12_in_pass1_prefix :
    tmFiber19StateAt 12 ∈ chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12] [tmFiber19StateAt 0] := by
  have hparentBefore :
      tmFiber19StateAt 0 ∈ chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11] [tmFiber19StateAt 0] := by
    rw [show [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11] = [tmFiber19StateAt 0] ++ [tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11]
      (chainClosureStep tmWord [tmFiber19StateAt 0] [tmFiber19StateAt 0]) (tmFiber19StateAt 0)
      tmFiber19State0_in_pass1_prefix
  rw [show [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12] = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11] ++ [tmFiber19StateAt 12] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber19StateAt 12) []
    (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11] [tmFiber19StateAt 0]) (tmFiber19StateAt 0)
    hparentBefore tmFiber19ReverseSingleStep12

theorem tmFiber19State13_in_pass1_prefix :
    tmFiber19StateAt 13 ∈ chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13] [tmFiber19StateAt 0] := by
  have hparentBefore :
      tmFiber19StateAt 1 ∈ chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12] [tmFiber19StateAt 0] := by
    rw [show [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12] = [tmFiber19StateAt 0, tmFiber19StateAt 1] ++ [tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12]
      (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1] [tmFiber19StateAt 0]) (tmFiber19StateAt 1)
      tmFiber19State1_in_pass1_prefix
  rw [show [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13] = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12] ++ [tmFiber19StateAt 13] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber19StateAt 13) []
    (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12] [tmFiber19StateAt 0]) (tmFiber19StateAt 1)
    hparentBefore tmFiber19ReverseSingleStep13

theorem tmFiber19State14_in_pass1_prefix :
    tmFiber19StateAt 14 ∈ chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14] [tmFiber19StateAt 0] := by
  have hparentBefore :
      tmFiber19StateAt 2 ∈ chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13] [tmFiber19StateAt 0] := by
    rw [show [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13] = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2] ++ [tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13]
      (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2] [tmFiber19StateAt 0]) (tmFiber19StateAt 2)
      tmFiber19State2_in_pass1_prefix
  rw [show [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14] = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13] ++ [tmFiber19StateAt 14] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber19StateAt 14) []
    (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13] [tmFiber19StateAt 0]) (tmFiber19StateAt 2)
    hparentBefore tmFiber19ReverseSingleStep14

theorem tmFiber19State15_in_pass1_prefix :
    tmFiber19StateAt 15 ∈ chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14, tmFiber19StateAt 15] [tmFiber19StateAt 0] := by
  have hparentBefore :
      tmFiber19StateAt 3 ∈ chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14] [tmFiber19StateAt 0] := by
    rw [show [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14] = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3] ++ [tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14]
      (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3] [tmFiber19StateAt 0]) (tmFiber19StateAt 3)
      tmFiber19State3_in_pass1_prefix
  rw [show [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14, tmFiber19StateAt 15] = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14] ++ [tmFiber19StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber19StateAt 15) []
    (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14] [tmFiber19StateAt 0]) (tmFiber19StateAt 3)
    hparentBefore tmFiber19ReverseSingleStep15

theorem tmFiber19State0_in_pass1_full :
    tmFiber19StateAt 0 ∈ chainClosureStep tmWord tmFiber19DirectStates [tmFiber19StateAt 0] := by
  rw [show tmFiber19DirectStates = [tmFiber19StateAt 0] ++ [tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14, tmFiber19StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14, tmFiber19StateAt 15]
    (chainClosureStep tmWord [tmFiber19StateAt 0] [tmFiber19StateAt 0]) (tmFiber19StateAt 0)
    tmFiber19State0_in_pass1_prefix

theorem tmFiber19State1_in_pass1_full :
    tmFiber19StateAt 1 ∈ chainClosureStep tmWord tmFiber19DirectStates [tmFiber19StateAt 0] := by
  rw [show tmFiber19DirectStates = [tmFiber19StateAt 0, tmFiber19StateAt 1] ++ [tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14, tmFiber19StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14, tmFiber19StateAt 15]
    (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1] [tmFiber19StateAt 0]) (tmFiber19StateAt 1)
    tmFiber19State1_in_pass1_prefix

theorem tmFiber19State2_in_pass1_full :
    tmFiber19StateAt 2 ∈ chainClosureStep tmWord tmFiber19DirectStates [tmFiber19StateAt 0] := by
  rw [show tmFiber19DirectStates = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2] ++ [tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14, tmFiber19StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14, tmFiber19StateAt 15]
    (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2] [tmFiber19StateAt 0]) (tmFiber19StateAt 2)
    tmFiber19State2_in_pass1_prefix

theorem tmFiber19State3_in_pass1_full :
    tmFiber19StateAt 3 ∈ chainClosureStep tmWord tmFiber19DirectStates [tmFiber19StateAt 0] := by
  rw [show tmFiber19DirectStates = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3] ++ [tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14, tmFiber19StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14, tmFiber19StateAt 15]
    (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3] [tmFiber19StateAt 0]) (tmFiber19StateAt 3)
    tmFiber19State3_in_pass1_prefix

theorem tmFiber19State4_in_pass1_full :
    tmFiber19StateAt 4 ∈ chainClosureStep tmWord tmFiber19DirectStates [tmFiber19StateAt 0] := by
  rw [show tmFiber19DirectStates = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4] ++ [tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14, tmFiber19StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14, tmFiber19StateAt 15]
    (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4] [tmFiber19StateAt 0]) (tmFiber19StateAt 4)
    tmFiber19State4_in_pass1_prefix

theorem tmFiber19State5_in_pass1_full :
    tmFiber19StateAt 5 ∈ chainClosureStep tmWord tmFiber19DirectStates [tmFiber19StateAt 0] := by
  rw [show tmFiber19DirectStates = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5] ++ [tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14, tmFiber19StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14, tmFiber19StateAt 15]
    (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5] [tmFiber19StateAt 0]) (tmFiber19StateAt 5)
    tmFiber19State5_in_pass1_prefix

theorem tmFiber19State6_in_pass1_full :
    tmFiber19StateAt 6 ∈ chainClosureStep tmWord tmFiber19DirectStates [tmFiber19StateAt 0] := by
  rw [show tmFiber19DirectStates = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6] ++ [tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14, tmFiber19StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14, tmFiber19StateAt 15]
    (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6] [tmFiber19StateAt 0]) (tmFiber19StateAt 6)
    tmFiber19State6_in_pass1_prefix

theorem tmFiber19State7_in_pass1_full :
    tmFiber19StateAt 7 ∈ chainClosureStep tmWord tmFiber19DirectStates [tmFiber19StateAt 0] := by
  rw [show tmFiber19DirectStates = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7] ++ [tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14, tmFiber19StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14, tmFiber19StateAt 15]
    (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7] [tmFiber19StateAt 0]) (tmFiber19StateAt 7)
    tmFiber19State7_in_pass1_prefix

theorem tmFiber19State8_in_pass1_full :
    tmFiber19StateAt 8 ∈ chainClosureStep tmWord tmFiber19DirectStates [tmFiber19StateAt 0] := by
  rw [show tmFiber19DirectStates = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8] ++ [tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14, tmFiber19StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14, tmFiber19StateAt 15]
    (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8] [tmFiber19StateAt 0]) (tmFiber19StateAt 8)
    tmFiber19State8_in_pass1_prefix

theorem tmFiber19State9_in_pass1_full :
    tmFiber19StateAt 9 ∈ chainClosureStep tmWord tmFiber19DirectStates [tmFiber19StateAt 0] := by
  rw [show tmFiber19DirectStates = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9] ++ [tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14, tmFiber19StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14, tmFiber19StateAt 15]
    (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9] [tmFiber19StateAt 0]) (tmFiber19StateAt 9)
    tmFiber19State9_in_pass1_prefix

theorem tmFiber19State10_in_pass1_full :
    tmFiber19StateAt 10 ∈ chainClosureStep tmWord tmFiber19DirectStates [tmFiber19StateAt 0] := by
  rw [show tmFiber19DirectStates = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10] ++ [tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14, tmFiber19StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14, tmFiber19StateAt 15]
    (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10] [tmFiber19StateAt 0]) (tmFiber19StateAt 10)
    tmFiber19State10_in_pass1_prefix

theorem tmFiber19State11_in_pass1_full :
    tmFiber19StateAt 11 ∈ chainClosureStep tmWord tmFiber19DirectStates [tmFiber19StateAt 0] := by
  rw [show tmFiber19DirectStates = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11] ++ [tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14, tmFiber19StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14, tmFiber19StateAt 15]
    (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11] [tmFiber19StateAt 0]) (tmFiber19StateAt 11)
    tmFiber19State11_in_pass1_prefix

theorem tmFiber19State12_in_pass1_full :
    tmFiber19StateAt 12 ∈ chainClosureStep tmWord tmFiber19DirectStates [tmFiber19StateAt 0] := by
  rw [show tmFiber19DirectStates = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12] ++ [tmFiber19StateAt 13, tmFiber19StateAt 14, tmFiber19StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber19StateAt 13, tmFiber19StateAt 14, tmFiber19StateAt 15]
    (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12] [tmFiber19StateAt 0]) (tmFiber19StateAt 12)
    tmFiber19State12_in_pass1_prefix

theorem tmFiber19State13_in_pass1_full :
    tmFiber19StateAt 13 ∈ chainClosureStep tmWord tmFiber19DirectStates [tmFiber19StateAt 0] := by
  rw [show tmFiber19DirectStates = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13] ++ [tmFiber19StateAt 14, tmFiber19StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber19StateAt 14, tmFiber19StateAt 15]
    (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13] [tmFiber19StateAt 0]) (tmFiber19StateAt 13)
    tmFiber19State13_in_pass1_prefix

theorem tmFiber19State14_in_pass1_full :
    tmFiber19StateAt 14 ∈ chainClosureStep tmWord tmFiber19DirectStates [tmFiber19StateAt 0] := by
  rw [show tmFiber19DirectStates = [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14] ++ [tmFiber19StateAt 15] by rfl]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber19StateAt 15]
    (chainClosureStep tmWord [tmFiber19StateAt 0, tmFiber19StateAt 1, tmFiber19StateAt 2, tmFiber19StateAt 3, tmFiber19StateAt 4, tmFiber19StateAt 5, tmFiber19StateAt 6, tmFiber19StateAt 7, tmFiber19StateAt 8, tmFiber19StateAt 9, tmFiber19StateAt 10, tmFiber19StateAt 11, tmFiber19StateAt 12, tmFiber19StateAt 13, tmFiber19StateAt 14] [tmFiber19StateAt 0]) (tmFiber19StateAt 14)
    tmFiber19State14_in_pass1_prefix

theorem tmFiber19State15_in_pass1_full :
    tmFiber19StateAt 15 ∈ chainClosureStep tmWord tmFiber19DirectStates [tmFiber19StateAt 0] := by
  simpa [tmFiber19DirectStates] using tmFiber19State15_in_pass1_prefix

theorem tmFiber19State0_in_close :
    tmFiber19StateAt 0 ∈ closeChainFiber tmWord tmFiber19DirectStates tmFiber19DirectStates.length [tmFiber19StateAt 0] := by
  change tmFiber19StateAt 0 ∈ closeChainFiber tmWord tmFiber19DirectStates (15 + 1) [tmFiber19StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber19DirectStates 15 [tmFiber19StateAt 0] (tmFiber19StateAt 0) tmFiber19State0_in_pass1_full

theorem tmFiber19State1_in_close :
    tmFiber19StateAt 1 ∈ closeChainFiber tmWord tmFiber19DirectStates tmFiber19DirectStates.length [tmFiber19StateAt 0] := by
  change tmFiber19StateAt 1 ∈ closeChainFiber tmWord tmFiber19DirectStates (15 + 1) [tmFiber19StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber19DirectStates 15 [tmFiber19StateAt 0] (tmFiber19StateAt 1) tmFiber19State1_in_pass1_full

theorem tmFiber19State2_in_close :
    tmFiber19StateAt 2 ∈ closeChainFiber tmWord tmFiber19DirectStates tmFiber19DirectStates.length [tmFiber19StateAt 0] := by
  change tmFiber19StateAt 2 ∈ closeChainFiber tmWord tmFiber19DirectStates (15 + 1) [tmFiber19StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber19DirectStates 15 [tmFiber19StateAt 0] (tmFiber19StateAt 2) tmFiber19State2_in_pass1_full

theorem tmFiber19State3_in_close :
    tmFiber19StateAt 3 ∈ closeChainFiber tmWord tmFiber19DirectStates tmFiber19DirectStates.length [tmFiber19StateAt 0] := by
  change tmFiber19StateAt 3 ∈ closeChainFiber tmWord tmFiber19DirectStates (15 + 1) [tmFiber19StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber19DirectStates 15 [tmFiber19StateAt 0] (tmFiber19StateAt 3) tmFiber19State3_in_pass1_full

theorem tmFiber19State4_in_close :
    tmFiber19StateAt 4 ∈ closeChainFiber tmWord tmFiber19DirectStates tmFiber19DirectStates.length [tmFiber19StateAt 0] := by
  change tmFiber19StateAt 4 ∈ closeChainFiber tmWord tmFiber19DirectStates (15 + 1) [tmFiber19StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber19DirectStates 15 [tmFiber19StateAt 0] (tmFiber19StateAt 4) tmFiber19State4_in_pass1_full

theorem tmFiber19State5_in_close :
    tmFiber19StateAt 5 ∈ closeChainFiber tmWord tmFiber19DirectStates tmFiber19DirectStates.length [tmFiber19StateAt 0] := by
  change tmFiber19StateAt 5 ∈ closeChainFiber tmWord tmFiber19DirectStates (15 + 1) [tmFiber19StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber19DirectStates 15 [tmFiber19StateAt 0] (tmFiber19StateAt 5) tmFiber19State5_in_pass1_full

theorem tmFiber19State6_in_close :
    tmFiber19StateAt 6 ∈ closeChainFiber tmWord tmFiber19DirectStates tmFiber19DirectStates.length [tmFiber19StateAt 0] := by
  change tmFiber19StateAt 6 ∈ closeChainFiber tmWord tmFiber19DirectStates (15 + 1) [tmFiber19StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber19DirectStates 15 [tmFiber19StateAt 0] (tmFiber19StateAt 6) tmFiber19State6_in_pass1_full

theorem tmFiber19State7_in_close :
    tmFiber19StateAt 7 ∈ closeChainFiber tmWord tmFiber19DirectStates tmFiber19DirectStates.length [tmFiber19StateAt 0] := by
  change tmFiber19StateAt 7 ∈ closeChainFiber tmWord tmFiber19DirectStates (15 + 1) [tmFiber19StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber19DirectStates 15 [tmFiber19StateAt 0] (tmFiber19StateAt 7) tmFiber19State7_in_pass1_full

theorem tmFiber19State8_in_close :
    tmFiber19StateAt 8 ∈ closeChainFiber tmWord tmFiber19DirectStates tmFiber19DirectStates.length [tmFiber19StateAt 0] := by
  change tmFiber19StateAt 8 ∈ closeChainFiber tmWord tmFiber19DirectStates (15 + 1) [tmFiber19StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber19DirectStates 15 [tmFiber19StateAt 0] (tmFiber19StateAt 8) tmFiber19State8_in_pass1_full

theorem tmFiber19State9_in_close :
    tmFiber19StateAt 9 ∈ closeChainFiber tmWord tmFiber19DirectStates tmFiber19DirectStates.length [tmFiber19StateAt 0] := by
  change tmFiber19StateAt 9 ∈ closeChainFiber tmWord tmFiber19DirectStates (15 + 1) [tmFiber19StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber19DirectStates 15 [tmFiber19StateAt 0] (tmFiber19StateAt 9) tmFiber19State9_in_pass1_full

theorem tmFiber19State10_in_close :
    tmFiber19StateAt 10 ∈ closeChainFiber tmWord tmFiber19DirectStates tmFiber19DirectStates.length [tmFiber19StateAt 0] := by
  change tmFiber19StateAt 10 ∈ closeChainFiber tmWord tmFiber19DirectStates (15 + 1) [tmFiber19StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber19DirectStates 15 [tmFiber19StateAt 0] (tmFiber19StateAt 10) tmFiber19State10_in_pass1_full

theorem tmFiber19State11_in_close :
    tmFiber19StateAt 11 ∈ closeChainFiber tmWord tmFiber19DirectStates tmFiber19DirectStates.length [tmFiber19StateAt 0] := by
  change tmFiber19StateAt 11 ∈ closeChainFiber tmWord tmFiber19DirectStates (15 + 1) [tmFiber19StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber19DirectStates 15 [tmFiber19StateAt 0] (tmFiber19StateAt 11) tmFiber19State11_in_pass1_full

theorem tmFiber19State12_in_close :
    tmFiber19StateAt 12 ∈ closeChainFiber tmWord tmFiber19DirectStates tmFiber19DirectStates.length [tmFiber19StateAt 0] := by
  change tmFiber19StateAt 12 ∈ closeChainFiber tmWord tmFiber19DirectStates (15 + 1) [tmFiber19StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber19DirectStates 15 [tmFiber19StateAt 0] (tmFiber19StateAt 12) tmFiber19State12_in_pass1_full

theorem tmFiber19State13_in_close :
    tmFiber19StateAt 13 ∈ closeChainFiber tmWord tmFiber19DirectStates tmFiber19DirectStates.length [tmFiber19StateAt 0] := by
  change tmFiber19StateAt 13 ∈ closeChainFiber tmWord tmFiber19DirectStates (15 + 1) [tmFiber19StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber19DirectStates 15 [tmFiber19StateAt 0] (tmFiber19StateAt 13) tmFiber19State13_in_pass1_full

theorem tmFiber19State14_in_close :
    tmFiber19StateAt 14 ∈ closeChainFiber tmWord tmFiber19DirectStates tmFiber19DirectStates.length [tmFiber19StateAt 0] := by
  change tmFiber19StateAt 14 ∈ closeChainFiber tmWord tmFiber19DirectStates (15 + 1) [tmFiber19StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber19DirectStates 15 [tmFiber19StateAt 0] (tmFiber19StateAt 14) tmFiber19State14_in_pass1_full

theorem tmFiber19State15_in_close :
    tmFiber19StateAt 15 ∈ closeChainFiber tmWord tmFiber19DirectStates tmFiber19DirectStates.length [tmFiber19StateAt 0] := by
  change tmFiber19StateAt 15 ∈ closeChainFiber tmWord tmFiber19DirectStates (15 + 1) [tmFiber19StateAt 0]
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber19DirectStates 15 [tmFiber19StateAt 0] (tmFiber19StateAt 15) tmFiber19State15_in_pass1_full

theorem tmFiber19DirectConnected :
    chainFiberConnected tmWord tmFiber19DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber19DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber19State0_in_close
  · subst state
    exact tmFiber19State1_in_close
  · subst state
    exact tmFiber19State2_in_close
  · subst state
    exact tmFiber19State3_in_close
  · subst state
    exact tmFiber19State4_in_close
  · subst state
    exact tmFiber19State5_in_close
  · subst state
    exact tmFiber19State6_in_close
  · subst state
    exact tmFiber19State7_in_close
  · subst state
    exact tmFiber19State8_in_close
  · subst state
    exact tmFiber19State9_in_close
  · subst state
    exact tmFiber19State10_in_close
  · subst state
    exact tmFiber19State11_in_close
  · subst state
    exact tmFiber19State12_in_close
  · subst state
    exact tmFiber19State13_in_close
  · subst state
    exact tmFiber19State14_in_close
  · subst state
    exact tmFiber19State15_in_close
  · cases h

end GoertzelLemma818LengthTwoTMShape16Bridge

end Mettapedia.GraphTheory.FourColor
