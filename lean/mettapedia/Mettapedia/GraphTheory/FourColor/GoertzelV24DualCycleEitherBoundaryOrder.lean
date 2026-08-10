import Mettapedia.GraphTheory.FourColor.GoertzelV24DualCycleTargetSide

/-!
# Either orientation of a simple facial-dual wall

A simple facial-dual loop is an unoriented geometric boundary.  When its
crossed primal edges are the exact boundary of a deleted region, the retained
boundary can follow the loop in either coherent direction.  This module proves
the complementary source-face case explicitly.  It lets a source layer use
the orientation furnished by its literal formation instead of baking an
arbitrary direction into the splice.

No profile, catalogue, or covering-style reduction is involved here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DualCycleEitherBoundaryOrder

open GoertzelV24DualCycleBoundaryFaceOrientation
open GoertzelV24ComplementaryRegionBoundaryOrder
open GoertzelV24DualCycleBond
open GoertzelV24DualCycleDeletedBoundaryOrder
open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DualCycleTargetSide
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The complementary concrete orientation datum: a retained boundary dart
faces the source face, rather than the target face, of its dual-loop step. -/
def BoundaryDartsUseDualCycleSourceFaces
    (data : Data G)
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Walk start start)
    (deleted : Finset V)
    (boundaryAt : Fin walk.length →
      BoundaryDart data.toRotationSystem (deletedRegionKeep deleted)) : Prop :=
  ∀ step,
    dartOrbitFace data.toRotationSystem (boundaryAt step).1.1 =
      (walk.getVert step.val).1

/-- If the literal source-face dart of every dual step is retained, it is the
unique retained boundary dart of that crossed edge. -/
theorem boundaryDartsUseDualCycleSourceFaces_of_sourceFaceDarts_kept
    (data : Data G)
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (walk : (interiorDualGraph (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Walk start start)
    (deleted : Finset V)
    (hboundary : vertexSetCrossingEdges data.toRotationSystem deleted =
      dualWalkCrossingEdges (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk)
    (boundaryAt : Fin walk.length →
      BoundaryDart data.toRotationSystem (deletedRegionKeep deleted))
    (hboundaryEdge : ∀ step,
      data.toRotationSystem.edgeOf (boundaryAt step).1.1 =
        dualWalkCrossingEdge (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk step)
    (hkept : ∀ step,
      deletedRegionKeep deleted
        (data.toRotationSystem.vertOf
          (dualWalkSourceFaceDart hunique walk step))) :
    BoundaryDartsUseDualCycleSourceFaces data walk deleted boundaryAt := by
  intro step
  let sourceDart := dualWalkSourceFaceDart hunique walk step
  have hsourceEdge : data.toRotationSystem.edgeOf sourceDart =
      dualWalkCrossingEdge (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk step := by
    exact dualWalkSourceFaceDart_edge hunique walk step
  have hcrossing : data.toRotationSystem.edgeOf sourceDart ∈
      vertexSetCrossingEdges data.toRotationSystem deleted := by
    rw [hboundary]
    exact (mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
      (data.toRotationSystem.edgeOf sourceDart)).2 ⟨step, hsourceEdge.symm⟩
  have hsourceKept : deletedRegionKeep deleted
      (data.toRotationSystem.vertOf sourceDart) := by
    simpa [sourceDart] using hkept step
  have hsourceAlphaNotKept : ¬ deletedRegionKeep deleted
      (data.toRotationSystem.vertOf (data.toRotationSystem.alpha sourceDart)) := by
    intro halphaKept
    rcases (mem_vertexSetCrossingEdges_iff data.toRotationSystem deleted
      (data.toRotationSystem.edgeOf sourceDart)).1 hcrossing with
      ⟨inner, hinnerEndpoint, hinnerDeleted, _outer, _houterEndpoint, _houterKept⟩
    have hsourceOn : sourceDart ∈
        data.toRotationSystem.dartsOn (data.toRotationSystem.edgeOf sourceDart) := by
      simp
    have hpairs := data.toRotationSystem.endpoints_eq_pair_of_mem hsourceOn
    rw [hpairs] at hinnerEndpoint
    simp only [Finset.mem_insert, Finset.mem_singleton] at hinnerEndpoint
    have hsourceNotDeleted : data.toRotationSystem.vertOf sourceDart ∉ deleted := by
      simpa [deletedRegionKeep] using hsourceKept
    have halphaNotDeleted : data.toRotationSystem.vertOf
        (data.toRotationSystem.alpha sourceDart) ∉ deleted := by
      simpa [deletedRegionKeep] using halphaKept
    rcases hinnerEndpoint with hinner | hinner
    · exact hsourceNotDeleted (hinner ▸ hinnerDeleted)
    · exact halphaNotDeleted (hinner ▸ hinnerDeleted)
  let sourceBoundary : BoundaryDart data.toRotationSystem
      (deletedRegionKeep deleted) :=
    ⟨⟨sourceDart, hsourceKept⟩, hsourceAlphaNotKept⟩
  have hboundaryDart : boundaryAt step = sourceBoundary := by
    apply boundaryDart_eq_of_edgeOf_eq data.toRotationSystem
      (deletedRegionKeep deleted)
    calc
      data.toRotationSystem.edgeOf (boundaryAt step).1.1 =
          dualWalkCrossingEdge (orbitFaceBoundary data.toRotationSystem)
            (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk step :=
        hboundaryEdge step
      _ = data.toRotationSystem.edgeOf sourceBoundary.1.1 := by
        exact hsourceEdge.symm
  rw [hboundaryDart]
  change dartOrbitFace data.toRotationSystem sourceDart = _
  exact dualWalkSourceFaceDart_face hunique walk step

/-- With retained boundary darts facing the source faces of a simple dual
cycle, the deleted-side boundary successor follows the previous dual crossing.
This is the exact inverse-orientation counterpart of
`deletedBoundarySuccessor_eq_next_dualCycleCrossing`. -/
theorem deletedBoundarySuccessor_eq_prev_dualCycleCrossing
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Walk start start)
    (hcycle : walk.IsCycle) (deleted : Finset V)
    (hboundary : vertexSetCrossingEdges data.toRotationSystem deleted =
      dualWalkCrossingEdges
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk)
    (boundaryAt : Fin walk.length →
      BoundaryDart data.toRotationSystem (deletedRegionKeep deleted))
    (hboundaryEdge : ∀ step,
      data.toRotationSystem.edgeOf (boundaryAt step).1.1 =
        dualWalkCrossingEdge
          (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk step)
    (hsourceFace : BoundaryDartsUseDualCycleSourceFaces
      data walk deleted boundaryAt)
    (step : Fin walk.length) :
    deletedRegionBoundarySuccessor data.toRotationSystem deleted (boundaryAt step) =
      boundaryAt ((finRotate walk.length)⁻¹ step) := by
  classical
  let crossing := dualWalkCrossingEdge
    (orbitFaceBoundary data.toRotationSystem)
    (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
  let removed := dualWalkCrossingEdges
    (orbitFaceBoundary data.toRotationSystem)
    (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
  let previous : Fin walk.length := (finRotate walk.length)⁻¹ step
  let face := (walk.getVert step.val).1
  let target := deletedRegionBoundarySuccessor
    data.toRotationSystem deleted (boundaryAt step)
  have htwoLength : 2 ≤ walk.length :=
    le_trans (by omega) hcycle.three_le_length
  have hrotateNe : finRotate walk.length previous ≠ previous := by
    rw [← Equiv.Perm.mem_support,
      support_finRotate_of_le htwoLength]
    exact Finset.mem_univ _
  have hpreviousNext : finRotate walk.length previous = step := by
    simpa [previous] using (finRotate walk.length).apply_symm_apply step
  have hcrossingInjective : Function.Injective crossing :=
    dualWalkCrossingEdge_injective_of_isCycle
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      (orbitFace_incidence_le_two data.toRotationSystem) hunique walk hcycle
  have hsourcePreviousNe : crossing step ≠ crossing previous := by
    intro hedges
    have hstepPrevious : step = previous := hcrossingInjective hedges
    exact hrotateNe (hpreviousNext.trans hstepPrevious)
  have htargetNe : target ≠ boundaryAt step := by
    exact deletedBoundarySuccessor_ne_of_twoSided data htwoSided deleted
      (boundaryAt step)
  have htargetEdgeNe : data.toRotationSystem.edgeOf target.1.1 ≠ crossing step := by
    intro hedge
    apply htargetNe
    apply boundaryDart_eq_of_edgeOf_eq data.toRotationSystem
      (deletedRegionKeep deleted)
    calc
      data.toRotationSystem.edgeOf target.1.1 = crossing step := hedge
      _ = data.toRotationSystem.edgeOf (boundaryAt step).1.1 :=
        (hboundaryEdge step).symm
  have htargetInBoundary : data.toRotationSystem.edgeOf target.1.1 ∈
      vertexSetCrossingEdges data.toRotationSystem deleted := by
    exact boundaryDart_edge_mem_vertexSetCrossingEdges
      data.toRotationSystem deleted target
  have htargetInRemoved : data.toRotationSystem.edgeOf target.1.1 ∈ removed := by
    rw [hboundary] at htargetInBoundary
    simpa only [removed] using htargetInBoundary
  have htargetAlphaFace :
      dartOrbitFace data.toRotationSystem
          (data.toRotationSystem.alpha target.1.1) = face := by
    calc
      dartOrbitFace data.toRotationSystem
          (data.toRotationSystem.alpha target.1.1) =
          dartOrbitFace data.toRotationSystem (boundaryAt step).1.1 := by
        exact (Quotient.sound
          (deletedRegionBoundarySuccessor_sameAmbientFace_alpha
            data.toRotationSystem deleted (boundaryAt step))).symm
      _ = face := hsourceFace step
  have htargetInFace : data.toRotationSystem.edgeOf target.1.1 ∈
      orbitFaceBoundary data.toRotationSystem face := by
    rw [← data.toRotationSystem.edge_alpha target.1.1,
      ← htargetAlphaFace]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace
      data.toRotationSystem (data.toRotationSystem.alpha target.1.1)
  have hsourceInRemoved : crossing step ∈ removed := by
    exact (mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
      (crossing step)).2 ⟨step, rfl⟩
  have hpreviousInRemoved : crossing previous ∈ removed := by
    exact (mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
      (crossing previous)).2 ⟨previous, rfl⟩
  have hsourceInFace : crossing step ∈
      orbitFaceBoundary data.toRotationSystem face := by
    exact dualWalkCrossingEdge_mem_leftFace
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk step
  have hpreviousInFace : crossing previous ∈
      orbitFaceBoundary data.toRotationSystem face := by
    have hmem := dualWalkCrossingEdge_mem_rightFace
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk previous
    rw [getVert_succ_eq_getVert_finRotate walk hcycle previous,
      hpreviousNext] at hmem
    exact hmem
  let removedAtFace := removed ∩ orbitFaceBoundary data.toRotationSystem face
  have hremovedAtFaceCardLe : removedAtFace.card ≤ 2 := by
    exact card_dualWalkCrossingEdges_inter_faceBoundary_le_two_of_isCycle
      data hunique walk hcycle face
  have hpairSubset : {crossing step, crossing previous} ⊆ removedAtFace := by
    intro edge hedge
    rw [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl
    · exact Finset.mem_inter.2 ⟨hsourceInRemoved, hsourceInFace⟩
    · exact Finset.mem_inter.2 ⟨hpreviousInRemoved, hpreviousInFace⟩
  have hpairCard : ({crossing step, crossing previous} : Finset G.edgeSet).card = 2 :=
    Finset.card_pair hsourcePreviousNe
  have hremovedAtFaceCard : removedAtFace.card = 2 := by
    have hlower : 2 ≤ removedAtFace.card := by
      rw [← hpairCard]
      exact Finset.card_le_card hpairSubset
    omega
  have hpairEq : ({crossing step, crossing previous} : Finset G.edgeSet) =
      removedAtFace := by
    apply Finset.eq_of_subset_of_card_le hpairSubset
    omega
  have htargetInPair : data.toRotationSystem.edgeOf target.1.1 ∈
      ({crossing step, crossing previous} : Finset G.edgeSet) := by
    rw [hpairEq]
    exact Finset.mem_inter.2 ⟨htargetInRemoved, htargetInFace⟩
  rw [Finset.mem_insert, Finset.mem_singleton] at htargetInPair
  rcases htargetInPair with hsource | hprevious
  · exact False.elim (htargetEdgeNe hsource)
  · apply boundaryDart_eq_of_edgeOf_eq data.toRotationSystem
      (deletedRegionKeep deleted)
    calc
      data.toRotationSystem.edgeOf target.1.1 = crossing previous := hprevious
      _ = data.toRotationSystem.edgeOf (boundaryAt previous).1.1 :=
        (hboundaryEdge previous).symm

/-- The preceding local calculation upgrades to the full inverse cyclic
boundary order whenever the concrete boundary enumeration is exhaustive. -/
theorem deletedBoundarySuccessor_eq_prev_dualCycleBoundaryOrder
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Walk start start)
    (hcycle : walk.IsCycle) (deleted : Finset V)
    (hboundary : vertexSetCrossingEdges data.toRotationSystem deleted =
      dualWalkCrossingEdges
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk)
    (boundaryAt : Fin walk.length →
      BoundaryDart data.toRotationSystem (deletedRegionKeep deleted))
    (hboundaryAt : Function.Bijective boundaryAt)
    (hboundaryEdge : ∀ step,
      data.toRotationSystem.edgeOf (boundaryAt step).1.1 =
        dualWalkCrossingEdge
          (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk step)
    (hsourceFace : BoundaryDartsUseDualCycleSourceFaces
      data walk deleted boundaryAt) :
    deletedRegionBoundarySuccessor data.toRotationSystem deleted =
      (Equiv.ofBijective boundaryAt hboundaryAt).permCongr
        (finRotate walk.length)⁻¹ := by
  apply Equiv.ext
  intro boundary
  obtain ⟨step, hstep⟩ := hboundaryAt.2 boundary
  subst boundary
  rw [deletedBoundarySuccessor_eq_prev_dualCycleCrossing
    data htwoSided walk hcycle deleted hboundary boundaryAt hboundaryEdge
    hsourceFace step]
  simp

/-- If no target-face dart of the crossed loop lies on the retained side,
then every literal source-face dart does.  This is just the two-endpoint law
for a crossing edge, made explicit for the source/target incidence darts. -/
theorem sourceFaceDarts_kept_of_targetFaceDarts_not_kept
    (data : Data G)
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Walk start start)
    (deleted : Finset V)
    (hboundary : vertexSetCrossingEdges data.toRotationSystem deleted =
      dualWalkCrossingEdges
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk)
    (hnotKept : ∀ step,
      ¬ deletedRegionKeep deleted
        (data.toRotationSystem.vertOf
          (dualWalkTargetFaceDart hunique walk step))) :
    ∀ step,
      deletedRegionKeep deleted
        (data.toRotationSystem.vertOf
          (dualWalkSourceFaceDart hunique walk step)) := by
  intro step
  by_contra hsourceNotKept
  let sourceDart := dualWalkSourceFaceDart hunique walk step
  have hsourceEdge : data.toRotationSystem.edgeOf sourceDart =
      dualWalkCrossingEdge (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk step := by
    exact dualWalkSourceFaceDart_edge hunique walk step
  have hcrossing : data.toRotationSystem.edgeOf sourceDart ∈
      vertexSetCrossingEdges data.toRotationSystem deleted := by
    rw [hboundary]
    exact (mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
      (data.toRotationSystem.edgeOf sourceDart)).2 ⟨step, hsourceEdge.symm⟩
  have halphaNotKept : ¬ deletedRegionKeep deleted
      (data.toRotationSystem.vertOf (data.toRotationSystem.alpha sourceDart)) := by
    intro halphaKept
    apply hnotKept step
    have htarget : dualWalkTargetFaceDart hunique walk step =
        data.toRotationSystem.alpha sourceDart := by
      dsimp [sourceDart]
      exact dualWalkTargetFaceDart_eq_alpha_sourceFaceDart hunique walk step
    rw [htarget]
    exact halphaKept
  rcases (mem_vertexSetCrossingEdges_iff data.toRotationSystem deleted
      (data.toRotationSystem.edgeOf sourceDart)).1 hcrossing with
    ⟨_inner, _hinnerEndpoint, _hinnerDeleted,
      outer, houterEndpoint, houterKept⟩
  have hsourceOn : sourceDart ∈
      data.toRotationSystem.dartsOn (data.toRotationSystem.edgeOf sourceDart) := by
    simp
  have hpairs := data.toRotationSystem.endpoints_eq_pair_of_mem hsourceOn
  rw [hpairs] at houterEndpoint
  simp only [Finset.mem_insert, Finset.mem_singleton] at houterEndpoint
  rcases houterEndpoint with houter | houter
  · exact hsourceNotKept (houter ▸ houterKept)
  · exact halphaNotKept (houter ▸ houterKept)

end

end GoertzelV24DualCycleEitherBoundaryOrder

end Mettapedia.GraphTheory.FourColor
