import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerFiniteCellCarrier
import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundedCarrierGraphFamilyCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexSlabConnectivityProfile

/-!
# Finite tracked-connectivity code for one literal source Cell

On the non-cyclic branch, the preceding module bounds the regional edge
carrier of the actual source-local Cell by six.  This file transports all
three tracked two-color graphs on that common carrier and retains the four
literal source-crosscut ports in left-then-right order.

This is only the tracked-connectivity coordinate of a one-Cell support
letter.  It does not identify the complete five-coordinate profile update:
in particular, the finite coding of face continuation, port incidence, and
capped face progress remains separate.  Nor does it discard the cyclic
branch of `sourceLocalLayerCellRegion_card_le_six_or_hasCycleOnSide`.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularCrosscut
open GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CorridorProfile
open GoertzelV24DualPathTransversal
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24RotationVertexCutProfile
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerFiniteTrackedLetterEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- The retained source component complementary to the literal local Cell. -/
noncomputable def sourceLocalLayerRetainedVertexSide
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) : Finset V :=
  let pair :=
    (sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
      hunique
  let boundary := sourceLocalLayerPairCrosscutBoundaryData corridor hunique
    leftInterior hnext
  pair.componentSide boundary.component

/-- The source-local Cell side is literally the finite complement of the
retained deletion component used by the ordered crosscut boundary. -/
theorem sourceLocalLayerCellVertexSide_eq_retained_compl
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    sourceLocalLayerCellVertexSide corridor hunique leftInterior hnext =
      (sourceLocalLayerRetainedVertexSide corridor hunique leftInterior hnext)ᶜ := by
  ext vertex
  simp [sourceLocalLayerCellVertexSide, sourceLocalLayerRetainedVertexSide]

/-- The ordered source boundary of a local Cell has exactly four ports. -/
theorem sourceLocalLayerRetainedCrossing_card_eq_four
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    Fintype.card (VertexSetCrossingEdge web.annular.RS
      (sourceLocalLayerRetainedVertexSide corridor hunique
        leftInterior hnext)) = 4 := by
  let layers := sourceLocalLayerPair corridor hunique leftInterior hnext
  let pair := layers.separatedLocalLayerPair hunique
  let boundary := sourceLocalLayerPairCrosscutBoundaryData corridor hunique
    leftInterior hnext
  change Fintype.card (VertexSetCrossingEdge web.annular.RS
      (pair.componentSide boundary.component)) = 4
  rw [pair.componentSide_crossingCard_eq_interfaceWidths
    web.annular.cellulation.rotation boundary.component
      boundary.component_boundary]
  simp [pair, layers, LocalLayerPair.separatedLocalLayerPair,
    LocalLayerPair.firstLayer, LocalLayerPair.secondLayer,
    LocalLayerPair.firstWalk, LocalLayerPair.secondWalk]

/-- The four source-ordered boundary edges, regarded as vertices of the
bounded regional edge carrier on the Cell side. -/
noncomputable def sourceLocalLayerCellPort
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    Fin 4 → {edge // edge ∈ vertexSetRegionEdges web.annular.RS
      (sourceLocalLayerCellVertexSide corridor hunique leftInterior hnext)} :=
  fun index => by
    let layers := sourceLocalLayerPair corridor hunique leftInterior hnext
    let pair := layers.separatedLocalLayerPair hunique
    let boundary := sourceLocalLayerPairCrosscutBoundaryData corridor hunique
      leftInterior hnext
    let retained := sourceLocalLayerRetainedVertexSide corridor hunique
      leftInterior hnext
    let crossing : VertexSetCrossingEdge web.annular.RS retained :=
      pair.sourceCrosscutBoundaryIndexing web.annular.cellulation.rotation boundary
        (Fin.cast
          (sourceLocalLayerRetainedCrossing_card_eq_four
            corridor hunique leftInterior hnext).symm index)
    refine ⟨crossing.1, ?_⟩
    apply vertexSetCrossingEdges_subset_regionEdges
    rw [sourceLocalLayerCellVertexSide_eq_retained_compl,
      vertexSetCrossingEdges_compl]
    exact crossing.2

/-- The common six-edge code for all three tracked-color graphs on one
literal source Cell.  The four distinguished points follow the actual two
source transversals, not an arbitrary enumeration of the carrier. -/
noncomputable def sourceLocalLayerCellTrackedFamilyCode
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength)
    (hfinite : (vertexSetRegionEdges web.annular.RS
      (sourceLocalLayerCellVertexSide corridor hunique
        leftInterior hnext)).card ≤ 6) :
    BoundedCarrierGraphFamilyCode 6 4 TrackedColorPair :=
  let region := vertexSetRegionEdges web.annular.RS
    (sourceLocalLayerCellVertexSide corridor hunique leftInterior hnext)
  boundedCarrierGraphFamilyCode region 6 4 hfinite
    (sourceLocalLayerCellPort corridor hunique leftInterior hnext)
    (fun pair =>
      let colors := trackedColorPairColors pair
      regionalTrackedEdgeGraph web.annular.RS region coloring
        colors.1 colors.2)

/-- The finite letter stores the literal regional carrier size, not merely a
loose six-element padding. -/
theorem sourceLocalLayerCellTrackedFamilyCode_vertexCount_eq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength)
    (hfinite : (vertexSetRegionEdges web.annular.RS
      (sourceLocalLayerCellVertexSide corridor hunique
        leftInterior hnext)).card ≤ 6) :
    (sourceLocalLayerCellTrackedFamilyCode corridor hunique leftInterior hnext
      hfinite).vertexCount.val =
      (vertexSetRegionEdges web.annular.RS
        (sourceLocalLayerCellVertexSide corridor hunique
          leftInterior hnext)).card := by
  rfl

/-- Every tracked adjacency on the literal regional carrier is represented
exactly by the corresponding member of the finite graph family. -/
theorem sourceLocalLayerCellTrackedFamilyCode_adj_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength)
    (hfinite : (vertexSetRegionEdges web.annular.RS
      (sourceLocalLayerCellVertexSide corridor hunique
        leftInterior hnext)).card ≤ 6)
    (pair : TrackedColorPair)
    (first second : {edge // edge ∈ vertexSetRegionEdges web.annular.RS
      (sourceLocalLayerCellVertexSide corridor hunique leftInterior hnext)}) :
    ((sourceLocalLayerCellTrackedFamilyCode corridor hunique leftInterior hnext
      hfinite).graph pair).Adj
        (carrierCoordinate _ first) (carrierCoordinate _ second) ↔
      (regionalTrackedEdgeGraph web.annular.RS
        (vertexSetRegionEdges web.annular.RS
          (sourceLocalLayerCellVertexSide corridor hunique leftInterior hnext))
        coloring (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Adj first.1 second.1 := by
  exact boundedCarrierGraphFamilyCode_adj_iff _ 6 4 hfinite
    (sourceLocalLayerCellPort corridor hunique leftInterior hnext)
    (fun trackedPair =>
      let colors := trackedColorPairColors trackedPair
      regionalTrackedEdgeGraph web.annular.RS _ coloring colors.1 colors.2)
    pair first second

/-- The finite code preserves complete regional tracked reachability, not
only individual adjacency bits. -/
theorem sourceLocalLayerCellTrackedFamilyCode_reachable_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength)
    (hfinite : (vertexSetRegionEdges web.annular.RS
      (sourceLocalLayerCellVertexSide corridor hunique
        leftInterior hnext)).card ≤ 6)
    (pair : TrackedColorPair)
    (first second : {edge // edge ∈ vertexSetRegionEdges web.annular.RS
      (sourceLocalLayerCellVertexSide corridor hunique leftInterior hnext)}) :
    ((sourceLocalLayerCellTrackedFamilyCode corridor hunique leftInterior hnext
      hfinite).graph pair).Reachable
        (carrierCoordinate _ first) (carrierCoordinate _ second) ↔
      (regionalTrackedEdgeGraph web.annular.RS
        (vertexSetRegionEdges web.annular.RS
          (sourceLocalLayerCellVertexSide corridor hunique leftInterior hnext))
        coloring (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Reachable first.1 second.1 := by
  refine boundedCarrierGraphFamilyCode_reachable_iff_of_support_subset
    _ 6 4 hfinite
    (sourceLocalLayerCellPort corridor hunique leftInterior hnext)
    (fun trackedPair =>
      let colors := trackedColorPairColors trackedPair
      regionalTrackedEdgeGraph web.annular.RS _ coloring colors.1 colors.2)
    pair ?_ first second
  intro edge hedge
  rcases hedge with ⟨other, hadj⟩
  exact hadj.2.1

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
