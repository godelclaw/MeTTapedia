import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutSpliceBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebCorridorLayer
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebCrosscutHoleBoundary

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

end LocalLayerPair

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
