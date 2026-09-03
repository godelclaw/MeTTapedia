import Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching
import Mettapedia.GraphTheory.FourColor.Compositional.FiveEdgeCutBoundaryOrder

/-!
# Physical noncrossing on an exact cyclic five-edge cut

This file connects the exact-five-cut geometry to the arity-generic physical
Kempe matching theorem.  The cyclic boundary coordinates and both connected
shores are derived from the exact cut rather than carried as interface
hypotheses.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace FiveEdgeCutPhysicalNoncrossing

open BoundaryKempeSwitch
open CyclicBoundaryMatching
open FiveEdgeCutBoundaryOrder
open FiveEdgeCutBoundaryPrerequisites
open GoertzelV24CyclicExactCutConnectedSides
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexagonPairingTargetAwareBoundary
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PortTangleGluing
open GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24ThreeEdgeCutMinimality
open GoertzelV24VertexSideOpenTangle
open GoertzelV24VertexSidePrimalKempeTrail
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- Every coloring of the retained shore of an exact cyclic five-edge cut
has a literal bichromatic boundary mate whose chords do not cross in the
facial cyclic order. -/
theorem exists_physicalMateInCoordinates_noncrossing_of_exactCyclicFiveCut
    (graphData : Data G)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 5)
    (cut : ExactSizedCyclicEdgeCut G 5)
    (outer : RetainedDart graphData.toRotationSystem
      (deletedRegionKeep (exactCutVertexSide cut)))
    (coloring : Coloring (vertexSidePortTangle graphData
      (deletedRegionKeep (exactCutVertexSide cut)) outer))
    (hproper : IsProper coloring) (pair : TaitColorPair) :
    ∃ boundaryOrder : Fin 5 ≃
        BoundaryDart graphData.toRotationSystem
          (deletedRegionKeep (exactCutVertexSide cut)),
      boundaryOrder.permCongr (finRotate 5) =
          retainedRegionBoundarySuccessor graphData.toRotationSystem
            (deletedRegionKeep (exactCutVertexSide cut)) ∧
        CyclicBoundaryMatching.IsNoncrossingMatching
          (physicalMateInCoordinates boundaryOrder
            (vertexSidePortTangle graphData
              (deletedRegionKeep (exactCutVertexSide cut)) outer)
            (isCubic_vertexSidePortTangle graphData
              (deletedRegionKeep (exactCutVertexSide cut)) outer
              hsphere.cubic)
            coloring hproper pair) := by
  have hsides := induce_both_sides_connected_of_card_eq_five
    hconnected hcyclic cut
  rcases exists_retainedBoundaryOrder_of_exactCyclicFiveCut
      graphData hsphere htwoSided hconnected hrotation hcyclic cut with
    ⟨boundaryOrder, horder⟩
  have hprimal :
      (rotationPrimalGraph graphData.toRotationSystem).Connected := by
    rw [rotationPrimalGraph_toRotationSystem_eq]
    exact hconnected
  have hdual := orbitFaceInteriorDual_connected
    graphData.toRotationSystem hsphere.cubic hprimal hrotation
  have hcomplementConnected :
      (G.induce {vertex |
        ¬deletedRegionKeep (exactCutVertexSide cut) vertex}).Connected := by
    have hpredicate :
        {vertex | ¬deletedRegionKeep (exactCutVertexSide cut) vertex} =
          {vertex | cut.side vertex} := by
      ext vertex
      change (¬vertex ∉ exactCutVertexSide cut) ↔ cut.side vertex
      rw [not_not, mem_exactCutVertexSide_iff]
    rw [hpredicate]
    exact hsides.1
  refine ⟨boundaryOrder, horder, ?_⟩
  exact physicalMateInCoordinates_isNoncrossing_five
    graphData htwoSided hdual hconnected hsphere hsphere.cubic hrotation
    (deletedRegionKeep (exactCutVertexSide cut)) hcomplementConnected
    boundaryOrder horder outer coloring hproper pair

end

end FiveEdgeCutPhysicalNoncrossing

end Mettapedia.GraphTheory.FourColor.Compositional
