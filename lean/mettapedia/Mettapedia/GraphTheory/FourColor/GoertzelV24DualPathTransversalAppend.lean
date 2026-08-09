import Mettapedia.GraphTheory.FourColor.GoertzelV24DualPathTransversal

/-!
# Crossings of concatenated facial-dual paths

The two source transversals used by the annular splice are joined into a
closed dual loop.  This file proves the finite bookkeeping fact needed to
read that loop back as its two original interfaces: every step in an appended
dual walk retains the same crossed primal edge as the corresponding step of
one summand.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DualPathTransversal

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open SimpleGraph

variable {F E : Type*} [Fintype F] [DecidableEq F]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- A step in the left summand of an appended facial-dual walk crosses the
same primal edge after the append. -/
theorem dualWalkCrossingEdge_append_left
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {start middle finish : AmbientFace allFaces}
    (left : (interiorDualGraph faceBoundary allFaces).Walk start middle)
    (right : (interiorDualGraph faceBoundary allFaces).Walk middle finish)
    (step : Fin left.length) :
    dualWalkCrossingEdge faceBoundary allFaces hunique (left.append right)
        ⟨step.val, by
          rw [SimpleGraph.Walk.length_append]
          omega⟩ =
      dualWalkCrossingEdge faceBoundary allFaces hunique left step := by
  let appendedStep : Fin (left.append right).length :=
    ⟨step.val, by
      rw [SimpleGraph.Walk.length_append]
      omega⟩
  change dualWalkCrossingEdge faceBoundary allFaces hunique
      (left.append right) appendedStep =
    dualWalkCrossingEdge faceBoundary allFaces hunique left step
  have hleft :
      (left.append right).getVert appendedStep.val = left.getVert step.val := by
    rw [SimpleGraph.Walk.getVert_append]
    simp [appendedStep, step.isLt]
  have hright :
      (left.append right).getVert (appendedStep.val + 1) =
        left.getVert (step.val + 1) := by
    rw [SimpleGraph.Walk.getVert_append]
    by_cases hnext : step.val + 1 < left.length
    · simp [appendedStep, hnext]
    · have hlast : step.val + 1 = left.length := by omega
      simp [appendedStep, hlast]
  have hshared :
      dualWalkCrossingEdge faceBoundary allFaces hunique
          (left.append right) appendedStep ∈
        sharedInteriorEdges faceBoundary allFaces
          (left.getVert step.val).1 (left.getVert (step.val + 1)).1 := by
    simpa [dualWalkCrossingEdge, hleft, hright] using
      (sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_sharedInteriorEdges
        faceBoundary allFaces hunique
        ((left.append right).adj_getVert_succ appendedStep.isLt))
  symm
  exact sharedInteriorEdgeOfAdjOfPairwiseUnique_eq_of_mem_sharedInteriorEdges
    faceBoundary allFaces hunique (left.adj_getVert_succ step.isLt) hshared

/-- A step in the right summand of an appended facial-dual walk crosses the
same primal edge after the append. -/
theorem dualWalkCrossingEdge_append_right
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {start middle finish : AmbientFace allFaces}
    (left : (interiorDualGraph faceBoundary allFaces).Walk start middle)
    (right : (interiorDualGraph faceBoundary allFaces).Walk middle finish)
    (step : Fin right.length) :
    dualWalkCrossingEdge faceBoundary allFaces hunique (left.append right)
        ⟨left.length + step.val, by
          rw [SimpleGraph.Walk.length_append]
          omega⟩ =
      dualWalkCrossingEdge faceBoundary allFaces hunique right step := by
  let appendedStep : Fin (left.append right).length :=
    ⟨left.length + step.val, by
      rw [SimpleGraph.Walk.length_append]
      omega⟩
  change dualWalkCrossingEdge faceBoundary allFaces hunique
      (left.append right) appendedStep =
    dualWalkCrossingEdge faceBoundary allFaces hunique right step
  have hnotLeft : ¬ left.length + step.val < left.length := by omega
  have hleft :
      (left.append right).getVert appendedStep.val = right.getVert step.val := by
    rw [SimpleGraph.Walk.getVert_append]
    simp [appendedStep, hnotLeft]
  have hright :
      (left.append right).getVert (appendedStep.val + 1) =
        right.getVert (step.val + 1) := by
    rw [SimpleGraph.Walk.getVert_append]
    have hnotNext : ¬ left.length + step.val + 1 < left.length := by omega
    have hsub : left.length + step.val + 1 - left.length = step.val + 1 := by
      omega
    simp [appendedStep, hnotNext, hsub]
  have hshared :
      dualWalkCrossingEdge faceBoundary allFaces hunique
          (left.append right) appendedStep ∈
        sharedInteriorEdges faceBoundary allFaces
          (right.getVert step.val).1 (right.getVert (step.val + 1)).1 := by
    simpa [dualWalkCrossingEdge, hleft, hright] using
      (sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_sharedInteriorEdges
        faceBoundary allFaces hunique
        ((left.append right).adj_getVert_succ appendedStep.isLt))
  symm
  exact sharedInteriorEdgeOfAdjOfPairwiseUnique_eq_of_mem_sharedInteriorEdges
    faceBoundary allFaces hunique (right.adj_getVert_succ step.isLt) hshared

/-- The finite primal support of an appended facial-dual walk is exactly the
union of the supports of its two summands. -/
theorem dualWalkCrossingEdges_append
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {start middle finish : AmbientFace allFaces}
    (left : (interiorDualGraph faceBoundary allFaces).Walk start middle)
    (right : (interiorDualGraph faceBoundary allFaces).Walk middle finish) :
    dualWalkCrossingEdges faceBoundary allFaces hunique (left.append right) =
      dualWalkCrossingEdges faceBoundary allFaces hunique left ∪
        dualWalkCrossingEdges faceBoundary allFaces hunique right := by
  ext edge
  simp only [mem_dualWalkCrossingEdges_iff, Finset.mem_union]
  constructor
  · rintro ⟨step, hstep⟩
    by_cases hleft : step.val < left.length
    · left
      let leftStep : Fin left.length := ⟨step.val, hleft⟩
      refine ⟨leftStep, ?_⟩
      calc
        dualWalkCrossingEdge faceBoundary allFaces hunique left leftStep =
            dualWalkCrossingEdge faceBoundary allFaces hunique (left.append right)
              ⟨leftStep.val, by
                rw [SimpleGraph.Walk.length_append]
                omega⟩ :=
          (dualWalkCrossingEdge_append_left faceBoundary allFaces hunique
            left right leftStep).symm
        _ = edge := by simpa [leftStep] using hstep
    · right
      have hleftLe : left.length ≤ step.val := Nat.le_of_not_gt hleft
      have hstepLt : step.val < left.length + right.length := by
        simpa using step.isLt
      let rightStep : Fin right.length := ⟨step.val - left.length, by
        omega⟩
      refine ⟨rightStep, ?_⟩
      calc
        dualWalkCrossingEdge faceBoundary allFaces hunique right rightStep =
            dualWalkCrossingEdge faceBoundary allFaces hunique (left.append right)
              ⟨left.length + rightStep.val, by
                rw [SimpleGraph.Walk.length_append]
                omega⟩ :=
          (dualWalkCrossingEdge_append_right faceBoundary allFaces hunique
            left right rightStep).symm
        _ = edge := by
          simpa [rightStep, Nat.add_sub_of_le hleftLe] using hstep
  · rintro (⟨leftStep, hstep⟩ | ⟨rightStep, hstep⟩)
    · refine ⟨⟨leftStep.val, by
          rw [SimpleGraph.Walk.length_append]
          omega⟩, ?_⟩
      calc
        dualWalkCrossingEdge faceBoundary allFaces hunique (left.append right)
            ⟨leftStep.val, by
              rw [SimpleGraph.Walk.length_append]
              omega⟩ =
            dualWalkCrossingEdge faceBoundary allFaces hunique left leftStep :=
          dualWalkCrossingEdge_append_left faceBoundary allFaces hunique
            left right leftStep
        _ = edge := hstep
    · refine ⟨⟨left.length + rightStep.val, by
          rw [SimpleGraph.Walk.length_append]
          omega⟩, ?_⟩
      calc
        dualWalkCrossingEdge faceBoundary allFaces hunique (left.append right)
            ⟨left.length + rightStep.val, by
              rw [SimpleGraph.Walk.length_append]
              omega⟩ =
            dualWalkCrossingEdge faceBoundary allFaces hunique right rightStep :=
          dualWalkCrossingEdge_append_right faceBoundary allFaces hunique
            left right rightStep
        _ = edge := hstep

/-- Reversing a facial-dual walk reverses the order of its crossings but not
the primal edge at any corresponding position. -/
theorem dualWalkCrossingEdge_reverse
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    (step : Fin walk.length) :
    dualWalkCrossingEdge faceBoundary allFaces hunique walk.reverse
        ⟨walk.length - (step.val + 1), by
          rw [SimpleGraph.Walk.length_reverse]
          omega⟩ =
      dualWalkCrossingEdge faceBoundary allFaces hunique walk step := by
  let reverseStep : Fin walk.reverse.length :=
    ⟨walk.length - (step.val + 1), by
      rw [SimpleGraph.Walk.length_reverse]
      omega⟩
  change dualWalkCrossingEdge faceBoundary allFaces hunique walk.reverse
      reverseStep =
    dualWalkCrossingEdge faceBoundary allFaces hunique walk step
  have hleft : walk.reverse.getVert reverseStep.val =
      walk.getVert (step.val + 1) := by
    rw [SimpleGraph.Walk.getVert_reverse]
    congr 1
    simp [reverseStep]
    omega
  have hright : walk.reverse.getVert (reverseStep.val + 1) =
      walk.getVert step.val := by
    rw [SimpleGraph.Walk.getVert_reverse]
    congr 1
    simp [reverseStep]
    omega
  have hshared :
      dualWalkCrossingEdge faceBoundary allFaces hunique walk step ∈
        sharedInteriorEdges faceBoundary allFaces
          (walk.reverse.getVert reverseStep.val).1
          (walk.reverse.getVert (reverseStep.val + 1)).1 := by
    simpa [dualWalkCrossingEdge, hleft, hright, sharedInteriorEdges, and_comm] using
      (sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_sharedInteriorEdges
        faceBoundary allFaces hunique (walk.adj_getVert_succ step.isLt))
  exact sharedInteriorEdgeOfAdjOfPairwiseUnique_eq_of_mem_sharedInteriorEdges
    faceBoundary allFaces hunique
      (walk.reverse.adj_getVert_succ reverseStep.isLt) hshared

/-- Read a reversed facial-dual step back at its original position.  This is
the converse orientation of `dualWalkCrossingEdge_reverse`. -/
theorem dualWalkCrossingEdge_unreverse
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    (reverseStep : Fin walk.reverse.length) :
    dualWalkCrossingEdge faceBoundary allFaces hunique walk
        ⟨walk.length - (reverseStep.val + 1), by
          have hreverseLt : reverseStep.val < walk.length := by
            simpa using reverseStep.isLt
          omega⟩ =
      dualWalkCrossingEdge faceBoundary allFaces hunique walk.reverse reverseStep := by
  let originalStep : Fin walk.length :=
    ⟨walk.length - (reverseStep.val + 1), by
      have hreverseLt : reverseStep.val < walk.length := by
        simpa using reverseStep.isLt
      omega⟩
  change dualWalkCrossingEdge faceBoundary allFaces hunique walk originalStep =
    dualWalkCrossingEdge faceBoundary allFaces hunique walk.reverse reverseStep
  have hreverseLt : reverseStep.val < walk.length := by
    simpa using reverseStep.isLt
  have hleft : walk.reverse.getVert reverseStep.val =
      walk.getVert (originalStep.val + 1) := by
    rw [SimpleGraph.Walk.getVert_reverse]
    congr 1
    dsimp [originalStep]
    omega
  have hright : walk.reverse.getVert (reverseStep.val + 1) =
      walk.getVert originalStep.val := by
    rw [SimpleGraph.Walk.getVert_reverse]
  have hshared :
      dualWalkCrossingEdge faceBoundary allFaces hunique walk.reverse reverseStep ∈
        sharedInteriorEdges faceBoundary allFaces
          (walk.getVert originalStep.val).1
          (walk.getVert (originalStep.val + 1)).1 := by
    have hreverseShared :=
      sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_sharedInteriorEdges
        faceBoundary allFaces hunique
          (walk.reverse.adj_getVert_succ reverseStep.isLt)
    change dualWalkCrossingEdge faceBoundary allFaces hunique walk.reverse
      reverseStep ∈ _ at hreverseShared
    rcases (mem_sharedInteriorEdges_iff faceBoundary allFaces).1 hreverseShared with
      ⟨hinterior, hleftFace, hrightFace⟩
    exact (mem_sharedInteriorEdges_iff faceBoundary allFaces).2
      ⟨hinterior, by simpa [hright] using hrightFace,
        by simpa [hleft] using hleftFace⟩
  exact sharedInteriorEdgeOfAdjOfPairwiseUnique_eq_of_mem_sharedInteriorEdges
    faceBoundary allFaces hunique (walk.adj_getVert_succ originalStep.isLt) hshared

/-- Reversal preserves the finite support of a facial-dual transversal. -/
theorem dualWalkCrossingEdges_reverse
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish) :
    dualWalkCrossingEdges faceBoundary allFaces hunique walk.reverse =
      dualWalkCrossingEdges faceBoundary allFaces hunique walk := by
  apply Finset.Subset.antisymm
  · intro edge hedge
    rcases (mem_dualWalkCrossingEdges_iff faceBoundary allFaces hunique
      walk.reverse edge).1 hedge with ⟨reverseStep, hstep⟩
    let originalStep : Fin walk.length :=
      ⟨walk.length - (reverseStep.val + 1), by
        have hreverseLt : reverseStep.val < walk.length := by
          simpa using reverseStep.isLt
        omega⟩
    refine (mem_dualWalkCrossingEdges_iff faceBoundary allFaces hunique
      walk edge).2 ⟨originalStep, ?_⟩
    exact (dualWalkCrossingEdge_unreverse faceBoundary allFaces hunique
      walk reverseStep).trans hstep
  · intro edge hedge
    rcases (mem_dualWalkCrossingEdges_iff faceBoundary allFaces hunique
      walk edge).1 hedge with ⟨step, hstep⟩
    let reverseStep : Fin walk.reverse.length :=
      ⟨walk.length - (step.val + 1), by
        rw [SimpleGraph.Walk.length_reverse]
        omega⟩
    refine (mem_dualWalkCrossingEdges_iff faceBoundary allFaces hunique
      walk.reverse edge).2 ⟨reverseStep, ?_⟩
    calc
      dualWalkCrossingEdge faceBoundary allFaces hunique walk.reverse reverseStep =
          dualWalkCrossingEdge faceBoundary allFaces hunique walk step := by
        simpa [reverseStep] using
          dualWalkCrossingEdge_reverse faceBoundary allFaces hunique walk step
      _ = edge := hstep

end

end GoertzelV24DualPathTransversal

end Mettapedia.GraphTheory.FourColor
