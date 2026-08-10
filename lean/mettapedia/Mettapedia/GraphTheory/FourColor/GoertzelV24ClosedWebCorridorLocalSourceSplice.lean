import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutSpliceBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebCorridorLayer
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebCrosscutHoleBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24FourEdgeCutGluing
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferPrimalCutCollar

/-!
# Source-crosscut boundary data for a Cell-3 local layer

A Cell-3 local layer pair is not merely a drawing in the facial dual.  Its
checked dual loop determines a primal deletion component with the exact cut
boundary, oriented crossing ports, an outer retained side, and an actually
removed vertex.  This file constructs that geometric splice input directly
from the closed-web source carrier.

It deliberately stops at geometry.  The later profile calculation must still
prove that equal source profiles preserve the closed-web-at-good-word witness.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularCrosscut
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebCorridorLocalSourceSpliceEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

attribute [local instance]
  collarFiniteGraphLocallyFinite
  GoertzelV24DualCycleSeparator.graphEdgeSetDecidableEq

namespace Instance

namespace LocalLayerPair

/-- The two literal Cell-3 local layers determine the complete geometric
boundary package required by the open splice.  The component and removed
vertex are constructed from the simple source dual loop, rather than supplied
as an interface premise. -/
theorem sourceCrosscutBoundaryData_nonempty_of_minimal
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (minimal : GraphBackedVertexMinimalTaitCounterexample
      web.annular.cellulation.rotation) :
    Nonempty (SeparatedAlignedSimpleDualCrosscuts.SourceCrosscutBoundaryData
      web.annular.cellulation.rotation
      (layers.separatedLocalLayerPair
        (web.pairwiseUniqueSharedInteriorEdges_of_minimal minimal))) := by
  let htwoSided := web.facesTwoSided_of_minimal minimal
  let hunique := web.pairwiseUniqueSharedInteriorEdges_of_minimal minimal
  let hsphere : OrbitSphericalCubicMapData
      web.annular.cellulation.rotation.toRotationSystem := {
    cubic := minimal.spherical.cubic
    euler := web.annular.cellulation.euler
  }
  exact SeparatedAlignedSimpleDualCrosscuts.exists_sourceCrosscutBoundaryData
    web.annular.cellulation.rotation htwoSided
    web.annular.cellulation.fullOrbitFaceInteriorDual_connected
    web.annular.cellulation.connected hsphere
    (layers.separatedLocalLayerPair hunique)

/-- The canonical source-derived deletion side of a literal Cell-3 layer
tile.  The choice hides only the already-proved separator construction; all
boundary facts remain visible through the resulting data. -/
noncomputable def sourceCrosscutBoundaryData_of_minimal
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (minimal : GraphBackedVertexMinimalTaitCounterexample
      web.annular.cellulation.rotation) :
    SeparatedAlignedSimpleDualCrosscuts.SourceCrosscutBoundaryData
      web.annular.cellulation.rotation
      (layers.separatedLocalLayerPair
        (web.pairwiseUniqueSharedInteriorEdges_of_minimal minimal)) :=
  Classical.choice (layers.sourceCrosscutBoundaryData_nonempty_of_minimal minimal)

/-- The primal edges crossed by a literal Cell-3 local layer avoid the
designated inner-hole boundary.  This is a concrete incidence consequence of
the source layer being wholly annular-interior; it does not yet claim that the
inner hole lies on the chosen retained component. -/
theorem sourceCrosscutPrimalCutEdges_disjoint_innerHoleBoundary_of_minimal
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (minimal : GraphBackedVertexMinimalTaitCounterexample
      web.annular.cellulation.rotation) :
    Disjoint
      ((layers.separatedLocalLayerPair
        (web.pairwiseUniqueSharedInteriorEdges_of_minimal minimal)).primalCutEdges
          web.annular.cellulation.rotation)
      (orbitFaceBoundary web.annular.RS web.annular.cellulation.innerHole) := by
  exact Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebCrosscutHoleBoundary.ClosedWebAnnularEmbedding.dualWalkCrossingEdges_disjoint_innerHoleBoundary_of_support_internal
      web.annular
      (layers.separatedLocalLayerPair
        (web.pairwiseUniqueSharedInteriorEdges_of_minimal minimal)).dualLoop
      (by
        intro face hface
        exact layers.separatedLocalLayerPair_dualLoop_support_internal
          (web.pairwiseUniqueSharedInteriorEdges_of_minimal minimal) face hface)

/-- The same literal Cell-3 separator also avoids the designated outer-hole
boundary.  Together with the inner-boundary result this is the incidence
part of the source's requirement that named holes are not cut through. -/
theorem sourceCrosscutPrimalCutEdges_disjoint_outerHoleBoundary_of_minimal
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (minimal : GraphBackedVertexMinimalTaitCounterexample
      web.annular.cellulation.rotation) :
    Disjoint
      ((layers.separatedLocalLayerPair
        (web.pairwiseUniqueSharedInteriorEdges_of_minimal minimal)).primalCutEdges
          web.annular.cellulation.rotation)
      (orbitFaceBoundary web.annular.RS web.annular.cellulation.outerHole) := by
  exact Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebCrosscutHoleBoundary.ClosedWebAnnularEmbedding.dualWalkCrossingEdges_disjoint_outerHoleBoundary_of_support_internal
    web.annular
    (layers.separatedLocalLayerPair
      (web.pairwiseUniqueSharedInteriorEdges_of_minimal minimal)).dualLoop
    (by
      intro face hface
      exact layers.separatedLocalLayerPair_dualLoop_support_internal
        (web.pairwiseUniqueSharedInteriorEdges_of_minimal minimal) face hface)

/-- The literal two-tile layer loop is a genuine four-edge separator with a
two-vertex collar on one side.  This is a local geometric characterization,
not the eventual profile-repeat splice: the global construction must still
choose two separated equal-profile layer boundaries. -/
theorem exists_primalCut_adjacent_pair_collar_of_minimal
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (minimal : GraphBackedVertexMinimalTaitCounterexample
      web.annular.cellulation.rotation) :
    let pair := layers.separatedLocalLayerPair
      (web.pairwiseUniqueSharedInteriorEdges_of_minimal minimal)
    ∃ component :
        (G.deleteEdges (pair.primalCut web.annular.cellulation.rotation)).ConnectedComponent,
      ∃ first second : V,
        first ≠ second ∧ component.supp = {first, second} ∧
          G.Adj first second ∧
          GoertzelV24CubicSmallBoundaryCycle.crossingEdgeFinset G
              (fun vertex => vertex ∈ component.supp) =
            pair.primalCutEdges web.annular.cellulation.rotation ∧
          ∃ internalEdge : G.edgeSet,
            internalEdge.1 = s(first, second) ∧
              internalEdge ∉ pair.primalCutEdges web.annular.cellulation.rotation ∧
              (pair.primalCutEdges web.annular.cellulation.rotation ∩
                incidentEdgeFinset G first).card = 2 ∧
              (pair.primalCutEdges web.annular.cellulation.rotation ∩
                incidentEdgeFinset G second).card = 2 := by
  dsimp
  let htwoSided := web.facesTwoSided_of_minimal minimal
  let hunique := web.pairwiseUniqueSharedInteriorEdges_of_minimal minimal
  let hsphere : OrbitSphericalCubicMapData
      web.annular.cellulation.rotation.toRotationSystem := {
    cubic := minimal.spherical.cubic
    euler := web.annular.cellulation.euler
  }
  have hregular : G.IsRegularOfDegree 3 :=
    web.annular.cellulation.rotation.toRotationSystem_isCubic_iff.mp
      minimal.spherical.cubic
  have hconnected : G.Connected :=
    web.connected
  have hcyclic : CyclicallyFiveEdgeConnected G :=
    _root_.Mettapedia.GraphTheory.FourColor.GoertzelV24FourEdgeCutGluing.cyclicallyFiveEdgeConnected_of_vertexMinimalTaitCounterexample
      web.annular.cellulation.rotation minimal
  have hdelete :
      ¬ (G.deleteEdges
        ((layers.separatedLocalLayerPair hunique).primalCut
          web.annular.cellulation.rotation)).Connected :=
    (layers.separatedLocalLayerPair hunique).primalCut_not_connected
      web.annular.cellulation.rotation htwoSided
      web.annular.cellulation.fullOrbitFaceInteriorDual_connected hconnected hsphere
  simpa only [SeparatedAlignedSimpleDualCrosscuts.primalCut,
    SeparatedAlignedSimpleDualCrosscuts.primalCutEdges] using
    _root_.Mettapedia.GraphTheory.FourColor.GoertzelV24DualCycleSeparator.exists_primalCut_adjacent_pair_collar_of_isCycle_of_length_eq_four
      web.annular.cellulation.rotation hregular hconnected hcyclic htwoSided hunique
      (layers.separatedLocalLayerPair hunique).dualLoop
      (layers.separatedLocalLayerPair_dualLoop_isCycle hunique)
      (layers.separatedLocalLayerPair_dualLoop_length_eq_four hunique) hdelete

end LocalLayerPair

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
