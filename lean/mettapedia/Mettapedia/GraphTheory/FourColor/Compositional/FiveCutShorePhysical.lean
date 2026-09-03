import Mettapedia.GraphTheory.FourColor.Compositional.FiveCutShoreLanguage
import Mettapedia.GraphTheory.FourColor.Compositional.FiveEdgeCutPhysicalNoncrossing

/-!
# The boundary language of the retained shore of an exact five-cut

The shore-language bridge asks for one geometric input: noncrossing of the
physical bichromatic mate in fixed cyclic boundary coordinates.  On the
retained shore of an exact cyclic five-edge cut, that input is supplied by
the graph-backed noncrossing theorem at any boundary order pinned by the
facial first-return successor.  The retained shore therefore carries a
`BoundaryLanguage` in every pinned coordinate system.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace Compositional

namespace FiveCutShorePhysical

open BoundaryKempeSwitch
open CyclicBoundaryMatching
open FiveCutShoreLanguage
open FiveCutWordHeart
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
open GoertzelV24PortTanglePhysicalKempeClosure
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24VertexSideOpenTangle
open GoertzelV24VertexSidePrimalKempeTrail
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- Noncrossing of the physical mate on the retained shore, at one fixed
boundary order pinned by the facial successor, for every colouring. -/
theorem noncrossing_retainedShore
    (graphData : Data G)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 5)
    (cut : ExactSizedCyclicEdgeCut G 5)
    (outer : RetainedDart graphData.toRotationSystem
      (deletedRegionKeep (exactCutVertexSide cut)))
    (boundaryOrder : Fin 5 ≃ BoundaryDart graphData.toRotationSystem
      (deletedRegionKeep (exactCutVertexSide cut)))
    (hpin : boundaryOrder.permCongr (finRotate 5) =
      retainedRegionBoundarySuccessor graphData.toRotationSystem
        (deletedRegionKeep (exactCutVertexSide cut)))
    (coloring : Coloring (vertexSidePortTangle graphData
      (deletedRegionKeep (exactCutVertexSide cut)) outer))
    (hproper : IsProper coloring) (pair : TaitColorPair) :
    IsNoncrossingMatching
      (physicalMateInCoordinates boundaryOrder
        (vertexSidePortTangle graphData
          (deletedRegionKeep (exactCutVertexSide cut)) outer)
        (isCubic_vertexSidePortTangle graphData
          (deletedRegionKeep (exactCutVertexSide cut)) outer hsphere.cubic)
        coloring hproper pair) := by
  have hsides := induce_both_sides_connected_of_exactSized
    hconnected hcyclic cut
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
  exact physicalMateInCoordinates_isNoncrossing_five
    graphData htwoSided hdual hconnected hsphere hsphere.cubic hrotation
    (deletedRegionKeep (exactCutVertexSide cut)) hcomplementConnected
    boundaryOrder hpin outer coloring hproper pair

/-- **The retained shore carries a boundary language** in every pinned
cyclic coordinate system: admissible, colour-closed, and chain-closed under
involutive noncrossing mates. -/
theorem boundaryLanguage_retainedShore
    (graphData : Data G)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 5)
    (cut : ExactSizedCyclicEdgeCut G 5)
    (outer : RetainedDart graphData.toRotationSystem
      (deletedRegionKeep (exactCutVertexSide cut)))
    (boundaryOrder : Fin 5 ≃ BoundaryDart graphData.toRotationSystem
      (deletedRegionKeep (exactCutVertexSide cut)))
    (hpin : boundaryOrder.permCongr (finRotate 5) =
      retainedRegionBoundarySuccessor graphData.toRotationSystem
        (deletedRegionKeep (exactCutVertexSide cut))) :
    BoundaryLanguage (shoreLanguage boundaryOrder
      (vertexSidePortTangle graphData
        (deletedRegionKeep (exactCutVertexSide cut)) outer)) :=
  FiveCutShoreLanguage.boundaryLanguage_shoreLanguage boundaryOrder
    (vertexSidePortTangle graphData
      (deletedRegionKeep (exactCutVertexSide cut)) outer)
    (isCubic_vertexSidePortTangle graphData
      (deletedRegionKeep (exactCutVertexSide cut)) outer hsphere.cubic)
    (fun coloring hproper pair =>
      noncrossing_retainedShore graphData hsphere htwoSided hconnected
        hrotation hcyclic cut outer boundaryOrder hpin coloring hproper pair)

end

end FiveCutShorePhysical

end Compositional

end Mettapedia.GraphTheory.FourColor
