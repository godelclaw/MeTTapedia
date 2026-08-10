import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutConnectedSides
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferPrimalCutBond
import Mettapedia.GraphTheory.FourColor.GoertzelV24ComplementaryRegionBoundaryOrder

/-!
# Deleted-boundary order from a simple facial-dual cycle

The compositional crosscut splice uses two open source transversals.  Their
concatenation is a simple cycle in the facial dual.  This module proves the
local rotation-system fact that turns that dual cycle into the actual boundary
successor of the deleted primal region: at a boundary dart facing the target
face of a dual step, the next deleted-boundary dart crosses the next dual edge.

The target-face orientation is intentionally an explicit hypothesis here.  It
is a concrete incidence statement to be constructed from the source layer
formation, not a semantic profile assumption.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DualCycleDeletedBoundaryOrder

open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24ComplementaryRegionBoundaryOrder
open GoertzelV24DualCycleBond
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] GoertzelV24DualCycleSeparator.graphEdgeSetDecidableEq

/-- A concrete retained-side boundary enumeration follows the target face of
each step of a facial-dual cycle.  This is the local orientation datum needed
to read the dual-cycle order as the computed deleted-region boundary order. -/
def BoundaryDartsUseDualCycleTargetFaces
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
      (walk.getVert (step.val + 1)).1

/-- A simple dual cycle has no fixed deleted-boundary successor in a two-sided
map.  A fixed point would put the two orientations of one edge on one face. -/
theorem deletedBoundarySuccessor_ne_of_twoSided
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (deleted : Finset V)
    (boundary : BoundaryDart data.toRotationSystem (deletedRegionKeep deleted)) :
    deletedRegionBoundarySuccessor data.toRotationSystem deleted boundary ≠ boundary := by
  intro hfixed
  apply htwoSided boundary.1.1
  change Quotient.mk (Equiv.Perm.SameCycle.setoid data.toRotationSystem.phi)
      boundary.1.1 =
    Quotient.mk (Equiv.Perm.SameCycle.setoid data.toRotationSystem.phi)
      (data.toRotationSystem.alpha boundary.1.1)
  apply Quotient.sound
  change data.toRotationSystem.phi.SameCycle boundary.1.1
    (data.toRotationSystem.alpha boundary.1.1)
  simpa [hfixed] using
    (deletedRegionBoundarySuccessor_sameAmbientFace_alpha
      data.toRotationSystem deleted boundary)

/-- If a simple facial-dual cycle is the exact edge boundary of a deleted
vertex region, the computed deleted-boundary successor follows its next dual
crossing whenever the concrete retained boundary darts use the corresponding
target faces.  The proof is finite: a touched face contains the present and
next dual crossing, while simplicity permits at most those two crossings. -/
theorem deletedBoundarySuccessor_eq_next_dualCycleCrossing
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
    (htargetFace : BoundaryDartsUseDualCycleTargetFaces
      data walk deleted boundaryAt)
    (step : Fin walk.length) :
    deletedRegionBoundarySuccessor data.toRotationSystem deleted (boundaryAt step) =
      boundaryAt (finRotate walk.length step) := by
  classical
  let crossing := dualWalkCrossingEdge
    (orbitFaceBoundary data.toRotationSystem)
    (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
  let removed := dualWalkCrossingEdges
    (orbitFaceBoundary data.toRotationSystem)
    (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
  let face := (walk.getVert (step.val + 1)).1
  let target := deletedRegionBoundarySuccessor
    data.toRotationSystem deleted (boundaryAt step)
  have htwoLength : 2 ≤ walk.length :=
    le_trans (by omega) hcycle.three_le_length
  have hrotateNe : finRotate walk.length step ≠ step := by
    rw [← Equiv.Perm.mem_support,
      support_finRotate_of_le htwoLength]
    exact Finset.mem_univ _
  have hcrossingInjective : Function.Injective crossing :=
    dualWalkCrossingEdge_injective_of_isCycle
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      (orbitFace_incidence_le_two data.toRotationSystem) hunique walk hcycle
  have hsourceNextNe : crossing step ≠ crossing (finRotate walk.length step) := by
    intro hedges
    exact hrotateNe (hcrossingInjective hedges.symm)
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
      _ = face := htargetFace step
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
  have hnextInRemoved : crossing (finRotate walk.length step) ∈ removed := by
    exact (mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
      (crossing (finRotate walk.length step))).2
        ⟨finRotate walk.length step, rfl⟩
  have hsourceInFace : crossing step ∈
      orbitFaceBoundary data.toRotationSystem face := by
    exact dualWalkCrossingEdge_mem_rightFace
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk step
  have hnextInFace : crossing (finRotate walk.length step) ∈
      orbitFaceBoundary data.toRotationSystem face := by
    have hmem := dualWalkCrossingEdge_mem_leftFace
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
      (finRotate walk.length step)
    rw [← getVert_succ_eq_getVert_finRotate walk hcycle step] at hmem
    exact hmem
  let removedAtFace := removed ∩ orbitFaceBoundary data.toRotationSystem face
  have hremovedAtFaceCardLe : removedAtFace.card ≤ 2 := by
    exact card_dualWalkCrossingEdges_inter_faceBoundary_le_two_of_isCycle
      data hunique walk hcycle face
  have hpairSubset : {crossing step, crossing (finRotate walk.length step)} ⊆
      removedAtFace := by
    intro edge hedge
    rw [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl
    · exact Finset.mem_inter.2 ⟨hsourceInRemoved, hsourceInFace⟩
    · exact Finset.mem_inter.2 ⟨hnextInRemoved, hnextInFace⟩
  have hpairCard : ({crossing step, crossing (finRotate walk.length step)} :
      Finset G.edgeSet).card = 2 :=
    Finset.card_pair hsourceNextNe
  have hremovedAtFaceCard : removedAtFace.card = 2 := by
    have hlower : 2 ≤ removedAtFace.card := by
      rw [← hpairCard]
      exact Finset.card_le_card hpairSubset
    omega
  have hpairEq : ({crossing step, crossing (finRotate walk.length step)} :
      Finset G.edgeSet) =
      removedAtFace := by
    apply Finset.eq_of_subset_of_card_le hpairSubset
    omega
  have htargetInPair : data.toRotationSystem.edgeOf target.1.1 ∈
      ({crossing step, crossing (finRotate walk.length step)} :
        Finset G.edgeSet) := by
    rw [hpairEq]
    exact Finset.mem_inter.2 ⟨htargetInRemoved, htargetInFace⟩
  rw [Finset.mem_insert, Finset.mem_singleton] at htargetInPair
  rcases htargetInPair with hsource | hnext
  · exact False.elim (htargetEdgeNe hsource)
  · apply boundaryDart_eq_of_edgeOf_eq data.toRotationSystem
      (deletedRegionKeep deleted)
    calc
      data.toRotationSystem.edgeOf target.1.1 =
          crossing (finRotate walk.length step) := hnext
      _ = data.toRotationSystem.edgeOf
          (boundaryAt (finRotate walk.length step)).1.1 :=
        (hboundaryEdge (finRotate walk.length step)).symm

/-- If the concrete retained boundary darts enumerate every boundary port,
the local dual-cycle successor calculation upgrades to an equality of whole
boundary permutations.  This is the exact finite bridge from a source layer
formation to the order premise of the planar splice; no topological
``homeomorphism'' is left implicit. -/
theorem deletedBoundarySuccessor_eq_dualCycleBoundaryOrder
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
    (htargetFace : BoundaryDartsUseDualCycleTargetFaces
      data walk deleted boundaryAt) :
    deletedRegionBoundarySuccessor data.toRotationSystem deleted =
      (Equiv.ofBijective boundaryAt hboundaryAt).permCongr
        (finRotate walk.length) := by
  apply Equiv.ext
  intro boundary
  obtain ⟨step, hstep⟩ := hboundaryAt.2 boundary
  subst boundary
  rw [deletedBoundarySuccessor_eq_next_dualCycleCrossing
    data htwoSided walk hcycle deleted hboundary boundaryAt hboundaryEdge
    htargetFace step]
  simp

end

end GoertzelV24DualCycleDeletedBoundaryOrder

end Mettapedia.GraphTheory.FourColor
