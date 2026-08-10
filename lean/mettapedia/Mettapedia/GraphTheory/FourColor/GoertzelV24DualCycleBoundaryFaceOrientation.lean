import Mettapedia.GraphTheory.FourColor.GoertzelV24DualCycleDeletedBoundaryOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrientedAnnularCrosscut

/-!
# Facial side data for a deleted dual cycle

A facial-dual step has two literal dart sides.  This module exposes the dart
on its target face and proves the small but essential conversion used by the
crosscut splice: if those target-facing darts lie on the retained graph side,
then the computed boundary darts are exactly those target-facing darts.

This is generic rotation-system geometry.  It does not choose a profile or a
configuration catalogue.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DualCycleBoundaryFaceOrientation

open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24DualCycleDeletedBoundaryOrder
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- A primal dart realizing the target facial side of one step of an arbitrary
facial-dual walk.  The witness comes from the actual target face occurrence,
not from a freely chosen endpoint of the crossed edge. -/
theorem exists_dualWalkTargetFaceDart
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (walk : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start finish)
    (step : Fin walk.length) :
    ∃ dart : RS.D,
      dart ∈ orbitFaceDarts RS (walk.getVert (step.val + 1)).1 ∧
        RS.edgeOf dart = dualWalkCrossingEdge (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS)) hunique walk step := by
  exact (mem_orbitFaceBoundary_iff RS
    (walk.getVert (step.val + 1)).1
    (dualWalkCrossingEdge (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk step)).1
        (dualWalkCrossingEdge_mem_rightFace (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS)) hunique walk step)

/-- The chosen target-face dart for one facial-dual step. -/
noncomputable def dualWalkTargetFaceDart
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (walk : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start finish)
    (step : Fin walk.length) : RS.D :=
  Classical.choose (exists_dualWalkTargetFaceDart hunique walk step)

/-- The selected dart lies on the target face of its dual step. -/
theorem dualWalkTargetFaceDart_face
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (walk : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start finish)
    (step : Fin walk.length) :
    dartOrbitFace RS (dualWalkTargetFaceDart hunique walk step) =
      (walk.getVert (step.val + 1)).1 := by
  exact (mem_orbitFaceDarts_iff RS
    (walk.getVert (step.val + 1)).1
    (dualWalkTargetFaceDart hunique walk step)).1
      (Classical.choose_spec (exists_dualWalkTargetFaceDart hunique walk step)).1

/-- The selected target-face dart crosses exactly the primal edge of its
facial-dual step. -/
theorem dualWalkTargetFaceDart_edge
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (walk : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start finish)
    (step : Fin walk.length) :
    RS.edgeOf (dualWalkTargetFaceDart hunique walk step) =
      dualWalkCrossingEdge (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) hunique walk step :=
  (Classical.choose_spec (exists_dualWalkTargetFaceDart hunique walk step)).2

/-- If the target-facing dart of every crossed edge is retained, then it is
the unique outward boundary dart of that edge.  Consequently the computed
deleted boundary uses the target faces of the dual cycle. -/
theorem boundaryDartsUseDualCycleTargetFaces_of_targetFaceDarts_kept
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
          (dualWalkTargetFaceDart hunique walk step))) :
    BoundaryDartsUseDualCycleTargetFaces data walk deleted boundaryAt := by
  intro step
  let targetDart := dualWalkTargetFaceDart hunique walk step
  have htargetEdge : data.toRotationSystem.edgeOf targetDart =
      dualWalkCrossingEdge (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk step := by
    exact dualWalkTargetFaceDart_edge hunique walk step
  have hcrossing : data.toRotationSystem.edgeOf targetDart ∈
      vertexSetCrossingEdges data.toRotationSystem deleted := by
    rw [hboundary]
    exact (mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
      (data.toRotationSystem.edgeOf targetDart)).2 ⟨step, htargetEdge.symm⟩
  have htargetKept : deletedRegionKeep deleted
      (data.toRotationSystem.vertOf targetDart) := by
    simpa [targetDart] using hkept step
  have htargetAlphaNotKept : ¬ deletedRegionKeep deleted
      (data.toRotationSystem.vertOf (data.toRotationSystem.alpha targetDart)) := by
    intro halphaKept
    rcases (mem_vertexSetCrossingEdges_iff data.toRotationSystem deleted
      (data.toRotationSystem.edgeOf targetDart)).1 hcrossing with
      ⟨inner, hinnerEndpoint, hinnerDeleted, _outer, _houterEndpoint, _houterKept⟩
    have htargetOn : targetDart ∈
        data.toRotationSystem.dartsOn (data.toRotationSystem.edgeOf targetDart) := by
      simp
    have hpairs := data.toRotationSystem.endpoints_eq_pair_of_mem htargetOn
    rw [hpairs] at hinnerEndpoint
    simp only [Finset.mem_insert, Finset.mem_singleton] at hinnerEndpoint
    have htargetNotDeleted : data.toRotationSystem.vertOf targetDart ∉ deleted := by
      simpa [deletedRegionKeep] using htargetKept
    have halphaNotDeleted :
        data.toRotationSystem.vertOf (data.toRotationSystem.alpha targetDart) ∉ deleted := by
      simpa [deletedRegionKeep] using halphaKept
    rcases hinnerEndpoint with hinner | hinner
    · exact htargetNotDeleted (hinner ▸ hinnerDeleted)
    · exact halphaNotDeleted (hinner ▸ hinnerDeleted)
  let targetBoundary : BoundaryDart data.toRotationSystem
      (deletedRegionKeep deleted) :=
    ⟨⟨targetDart, htargetKept⟩, htargetAlphaNotKept⟩
  have hboundaryDart : boundaryAt step = targetBoundary := by
    apply boundaryDart_eq_of_edgeOf_eq data.toRotationSystem
      (deletedRegionKeep deleted)
    calc
      data.toRotationSystem.edgeOf (boundaryAt step).1.1 =
          dualWalkCrossingEdge (orbitFaceBoundary data.toRotationSystem)
            (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk step :=
        hboundaryEdge step
      _ = data.toRotationSystem.edgeOf targetBoundary.1.1 := by
        exact htargetEdge.symm
  rw [hboundaryDart]
  change dartOrbitFace data.toRotationSystem targetDart = _
  exact dualWalkTargetFaceDart_face hunique walk step

end

end GoertzelV24DualCycleBoundaryFaceOrientation

end Mettapedia.GraphTheory.FourColor
