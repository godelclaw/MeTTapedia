import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedDualCycleSeparator
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferPrimalCutBond

/-!
# Exact boundary of a framed facial-dual cycle

A simple facial-dual cycle already disconnects a connected spherical
rotation system.  The generic separator construction previously exposed only
a component with a nonempty boundary, while individual corridor modules
reproved that the boundary is saturated.  This file records the saturation
once for an arbitrary simple dual cycle.

The result is the graph-facing bridge needed by a corridor-prefix boundary:
after the geometric layer construction produces a genuine dual cycle, its
crossed primal edges are exactly the boundary of one literal deletion
component.  No profile or colouring hypothesis occurs here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedDualCycleExactBoundary

open GoertzelV24DualCycleBond
open GoertzelV24DualPathTransversal
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteEdgeDeletion
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24FramedDualCycleSeparator
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- A simple facial-dual cycle in a connected spherical graph has a deletion
component whose graph-computed boundary is exactly the set of primal edges
crossed by the cycle.  Thus a constructed dual layer is already a saturated
literal shore; saturation is not an additional splice hypothesis. -/
theorem exists_component_exactBoundary_of_dualCycle
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (heuler : (Fintype.card V : Int) - Fintype.card G.edgeSet +
      Fintype.card (OrbitFace data.toRotationSystem) = 2)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)))
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem))).Walk start start)
    (hcycle : walk.IsCycle) :
    let removed := dualWalkCrossingEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
    ∃ component :
        (G.deleteEdges
          (GoertzelV24FiniteDeletionCyclicCut.edgeFinsetValueSet removed)).ConnectedComponent,
      GoertzelV24FiniteDeletionCyclicCut.componentCrossingEdges
        removed component = removed := by
  dsimp only
  let removed := dualWalkCrossingEdges
    (orbitFaceBoundary data.toRotationSystem)
    (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
  rcases exists_componentCrossingEdges_nonempty_of_dualCycle
      data hdual hconnected heuler hunique walk hcycle with
    ⟨component, hboundaryNonempty⟩
  refine ⟨component, ?_⟩
  have hcomponentBoundary :
      GoertzelV24FiniteDeletionCyclicCut.componentCrossingEdges
          removed component =
        crossingEdgeFinset G (fun vertex => vertex ∈ component.supp) := by
    ext edge
    rw [GoertzelV24FiniteDeletionCyclicCut.mem_componentCrossingEdges_iff,
      GoertzelV24CubicSmallBoundaryCycle.mem_crossingEdgeFinset_iff]
  have hsubset :
      crossingEdgeFinset G (fun vertex => vertex ∈ component.supp) ⊆
        removed := by
    rw [← hcomponentBoundary]
    exact
      GoertzelV24FiniteDeletionCyclicCut.componentCrossingEdges_subset_removed
        removed component
  have hnonempty :
      (crossingEdgeFinset G
        (fun vertex => vertex ∈ component.supp)).Nonempty := by
    rw [← hcomponentBoundary]
    exact hboundaryNonempty
  have hsaturated :=
    crossingEdgeFinset_eq_dualWalkCrossingEdges_of_isCycle_of_subset
      data htwoSided hunique walk hcycle
        (fun vertex => vertex ∈ component.supp) hsubset hnonempty
  rw [hcomponentBoundary]
  exact hsaturated

/-- A simple facial-dual cycle has two connected literal vertex sides, and
the boundary of either deletion component is the whole crossed-edge set.

The extra conclusion is not a Jordan-curve assumption.  Parity saturation
applies to every deletion component.  Since one crossed edge has only two
endpoints, all components other than a chosen one must therefore coincide;
`induce_complement_connected_of_component_boundary_saturation` packages this
finite graph argument. -/
theorem exists_component_exactBoundary_connectedSides_of_dualCycle
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (heuler : (Fintype.card V : Int) - Fintype.card G.edgeSet +
      Fintype.card (OrbitFace data.toRotationSystem) = 2)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)))
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem))).Walk start start)
    (hcycle : walk.IsCycle) :
    let removed := dualWalkCrossingEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
    ∃ component :
        (G.deleteEdges
          (GoertzelV24FiniteDeletionCyclicCut.edgeFinsetValueSet removed)).ConnectedComponent,
      GoertzelV24FiniteDeletionCyclicCut.componentCrossingEdges
          removed component = removed ∧
        (G.induce (fun vertex => vertex ∈ component.supp)).Connected ∧
        (G.induce (fun vertex => vertex ∉ component.supp)).Connected := by
  dsimp only
  let removed := dualWalkCrossingEdges
    (orbitFaceBoundary data.toRotationSystem)
    (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
  rcases exists_componentCrossingEdges_nonempty_of_dualCycle
      data hdual hconnected heuler hunique walk hcycle with
    ⟨component, hcomponentNonempty⟩
  have hsaturation
      (other :
        (G.deleteEdges
          (GoertzelV24FiniteDeletionCyclicCut.edgeFinsetValueSet removed)).ConnectedComponent) :
      GoertzelV24FiniteDeletionCyclicCut.componentCrossingEdges
          removed other = removed := by
    have hotherBoundary :
        GoertzelV24FiniteDeletionCyclicCut.componentCrossingEdges
            removed other =
          crossingEdgeFinset G (fun vertex => vertex ∈ other.supp) := by
      ext edge
      rw [GoertzelV24FiniteDeletionCyclicCut.mem_componentCrossingEdges_iff,
        GoertzelV24CubicSmallBoundaryCycle.mem_crossingEdgeFinset_iff]
    have hsubset :
        crossingEdgeFinset G (fun vertex => vertex ∈ other.supp) ⊆
          removed := by
      rw [← hotherBoundary]
      exact
        GoertzelV24FiniteDeletionCyclicCut.componentCrossingEdges_subset_removed
          removed other
    have hnonempty :
        (crossingEdgeFinset G
          (fun vertex => vertex ∈ other.supp)).Nonempty := by
      rw [← hotherBoundary]
      by_cases heq : other = component
      · simpa [heq] using hcomponentNonempty
      · exact
          GoertzelV24FiniteDeletionCyclicCut.componentCrossingEdges_nonempty_of_distinct
            hconnected removed other component heq
    have hsaturated :=
      crossingEdgeFinset_eq_dualWalkCrossingEdges_of_isCycle_of_subset
        data htwoSided hunique walk hcycle
          (fun vertex => vertex ∈ other.supp) hsubset hnonempty
    rw [hotherBoundary]
    exact hsaturated
  have hboundary := hsaturation component
  have hremovedNonempty : removed.Nonempty := by
    rw [← hboundary]
    exact hcomponentNonempty
  refine ⟨component, hboundary, ?_, ?_⟩
  · exact
      GoertzelV24FiniteDeletionCyclicCut.connected_induce_component
        removed component
  · exact
      GoertzelV24FiniteDeletionCyclicCut.induce_complement_connected_of_component_boundary_saturation
        removed component hremovedNonempty hsaturation

end

end GoertzelV24FramedDualCycleExactBoundary

end Mettapedia.GraphTheory.FourColor
