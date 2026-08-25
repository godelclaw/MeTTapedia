import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerFiniteTrackedLetter
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialPrefixRegion
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalFacialPentagonCapPairNoSmallCut
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphRotationEndpointInjective

/-!
# Finite literal Cell carrier in the two-cap source laboratory

The generic opened-annulus analysis leaves one honest alternative: the
four-edge wall of a literal corridor Cell may enclose a cycle.  On the
two-cap opening of a closed graph-backed vertex-minimal counterexample that
alternative is impossible.  Both named holes lie on the retained side of
the wall, so the cyclic Cell would be a one-sided cut of cardinality four;
closing the two facial caps pulls it back to the closed carrier, where
cyclic five-edge-connectivity excludes it.

Thus every literal Cell in this source laboratory has a graph-independent
regional edge carrier of cardinality at most six.  This removes the cyclic
escape branch needed by the finite Cell-letter construction.  It does not
claim that an arbitrary abstract Addendum-V frontier is a two-cap opening;
that source-formation comparison remains a separate obligation.  The indexed
corollary below applies the same bound at every offset of the actual
heterogeneous source word; it does not quotient those letters by orientation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24MinimalFacialPentagonCapPairLocalCellCarrier

open GoertzelV24AnnularCrosscut
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebHoleBoundaryOrder
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24CubicFourEdgeConnectedSides
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24MinimalFacialPentagonCapPairNoSmallCut
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SimpleGraphRotationEndpointInjective
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section


local instance openedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- A literal Cell side in the two-cap minimal-counterexample laboratory
cannot contain a cycle.  Its exact four-edge wall would otherwise be a
one-sided cut with both named holes on the retained side, contradicting the
closed carrier's cyclic five-edge-connectivity after cap closure. -/
theorem not_sourceLocalLayerCell_hasCycleOnSide
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    ¬ HasCycleOnSide
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph
      (fun vertex => vertex ∈
        sourceLocalLayerCellVertexSide corridor hunique leftInterior hnext) := by
  intro hcycle
  let capPair := caps.toFacialPentagonCapPair.toPentagonCapPair
  let side := sourceLocalLayerCellVertexSide corridor hunique leftInterior hnext
  apply false_of_openGraph_oneSidedCut graphData minimal caps
    (crossingEdgeFinset capPair.openGraph (fun vertex => vertex ∈ side))
    (fun vertex => vertex ∈ side)
  · intro edge
    exact mem_crossingEdgeFinset_iff
      (G := capPair.openGraph) (fun vertex => vertex ∈ side) edge
  · have hcard :=
      sourceLocalLayerCellVertexSide_crossingEdgeFinset_card_eq_four
        corridor hunique leftInterior hnext
    simpa [side, capPair] using hcard.le
  · simpa [side, capPair] using hcycle
  · intro step
    change ¬ (capPair.boundaryData.innerStub step ∈ side)
    intro hinside
    let pair :=
      (sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
        hunique
    let boundary := sourceLocalLayerPairCrosscutBoundaryData corridor hunique
      leftInterior hnext
    have hnotKept : capPair.boundaryData.innerStub step ∉
        pair.componentSide boundary.component := by
      simpa [side, sourceLocalLayerCellVertexSide, pair, boundary] using
        hinside
    apply hnotKept
    have hkept :=
      sourceLocalLayerPair_innerHole_vertex_mem_componentSide_of_radialEscape
        corridor hunique leftInterior hnext
        (innerBoundaryDart capPair.boundaryData web.boundary_wellFormed step)
        (innerBoundaryDart_on_innerHole web.annular
          web.boundary_wellFormed step)
    simpa [pair, boundary] using hkept
  · intro step
    change ¬ (capPair.boundaryData.outerStub step ∈ side)
    intro hinside
    let pair :=
      (sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
        hunique
    let boundary := sourceLocalLayerPairCrosscutBoundaryData corridor hunique
      leftInterior hnext
    have hnotKept : capPair.boundaryData.outerStub step ∉
        pair.componentSide boundary.component := by
      simpa [side, sourceLocalLayerCellVertexSide, pair, boundary] using
        hinside
    apply hnotKept
    have hkept := sourceLocalLayerPair_outerHole_vertex_mem_componentSide
      corridor hunique leftInterior hnext
      (outerBoundaryDart capPair.boundaryData web.boundary_wellFormed step)
      (outerBoundaryDart_on_outerHole web.annular
        web.boundary_wellFormed step)
    simpa [pair, boundary] using hkept

/-- The literal Cell side in the two-cap source laboratory has exactly two
vertices.  This is the sharp form of the finite-carrier result: four crossing
ports surround a two-vertex side. -/
theorem sourceLocalLayerCellVertexSide_card_eq_two
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    (sourceLocalLayerCellVertexSide corridor hunique
      leftInterior hnext).card = 2 := by
  rcases sourceLocalLayerCellVertexSide_card_eq_two_or_hasCycleOnSide
      corridor hunique leftInterior hnext with hcycle | hcard
  · exact (not_sourceLocalLayerCell_hasCycleOnSide graphData minimal caps coloring web
      corridor hunique leftInterior hnext hcycle).elim
  · exact hcard

/-- Indexed form of the exact two-vertex Cell-side theorem. -/
theorem sourceLocalLayerCellVertexSideAt_card_eq_two
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    (sourceLocalLayerCellVertexSide corridor hunique
      (sourceLocalLayerInteriorAt offset)
      (sourceLocalLayerInteriorAt_hasNext offset)).card = 2 :=
  sourceLocalLayerCellVertexSide_card_eq_two graphData minimal caps coloring web
    corridor hunique (sourceLocalLayerInteriorAt offset)
      (sourceLocalLayerInteriorAt_hasNext offset)

/-- The non-crossing part of an indexed Cell region is subsingleton: two
regional edges which do not cross the four-port boundary are the same literal
edge. -/
theorem sourceLocalLayerCellRegionAt_internalEdge_subsingleton
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    {first second :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet}
    (hfirstRegion : first ∈ sourceLocalLayerCellRegionAt corridor hunique offset)
    (hfirstNotCrossing : first ∉ vertexSetCrossingEdges web.annular.RS
      (sourceLocalLayerCellVertexSide corridor hunique
        (sourceLocalLayerInteriorAt offset)
        (sourceLocalLayerInteriorAt_hasNext offset)))
    (hsecondRegion : second ∈ sourceLocalLayerCellRegionAt corridor hunique offset)
    (hsecondNotCrossing : second ∉ vertexSetCrossingEdges web.annular.RS
      (sourceLocalLayerCellVertexSide corridor hunique
        (sourceLocalLayerInteriorAt offset)
        (sourceLocalLayerInteriorAt_hasNext offset))) :
    first = second := by
  let side := sourceLocalLayerCellVertexSide corridor hunique
    (sourceLocalLayerInteriorAt offset)
    (sourceLocalLayerInteriorAt_hasNext offset)
  have hregion : sourceLocalLayerCellRegionAt corridor hunique offset =
      vertexSetRegionEdges web.annular.RS side := by
    have hside := sourceLocalLayerCellVertexSide_eq_retained_compl
      corridor hunique (sourceLocalLayerInteriorAt offset)
        (sourceLocalLayerInteriorAt_hasNext offset)
    exact congrArg (vertexSetRegionEdges web.annular.RS) hside.symm
  apply edge_eq_of_mem_region_not_mem_crossing_of_card_eq_two
    web.annular.RS (endpoints_injective web.annular.cellulation.rotation)
      side
  · simpa [side] using sourceLocalLayerCellVertexSideAt_card_eq_two
      graphData minimal caps coloring web corridor hunique offset
  · simpa [hregion] using hfirstRegion
  · simpa [side] using hfirstNotCrossing
  · simpa [hregion] using hsecondRegion
  · simpa [side] using hsecondNotCrossing

/-- The exact two-vertex Cell has at most five regional edges: its four
source-ordered crossing ports and at most one edge internal to the Cell side.
This sharpens the earlier degree-count bound of six without choosing or
assuming an internal edge. -/
theorem sourceLocalLayerCellRegionAt_card_le_five
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 5 := by
  let side := sourceLocalLayerCellVertexSide corridor hunique
    (sourceLocalLayerInteriorAt offset)
    (sourceLocalLayerInteriorAt_hasNext offset)
  let region := sourceLocalLayerCellRegionAt corridor hunique offset
  let crossing := vertexSetCrossingEdges web.annular.RS side
  let internal := region.filter fun edge => edge ∉ crossing
  have hregion : region = vertexSetRegionEdges web.annular.RS side := by
    have hside := sourceLocalLayerCellVertexSide_eq_retained_compl
      corridor hunique (sourceLocalLayerInteriorAt offset)
        (sourceLocalLayerInteriorAt_hasNext offset)
    exact congrArg (vertexSetRegionEdges web.annular.RS) hside.symm
  have hcrossingSubset : crossing ⊆ region := by
    rw [hregion]
    exact vertexSetCrossingEdges_subset_regionEdges web.annular.RS side
  have hcover : region ⊆ crossing ∪ internal := by
    intro edge hedge
    by_cases hcrossing : edge ∈ crossing
    · exact Finset.mem_union_left _ hcrossing
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hedge, hcrossing⟩)
  have hcrossingCard : crossing.card = 4 := by
    rw [show crossing = vertexSetCrossingEdges web.annular.RS
        (sourceLocalLayerRetainedVertexSide corridor hunique
          (sourceLocalLayerInteriorAt offset)
          (sourceLocalLayerInteriorAt_hasNext offset)) by
      simp only [crossing, side,
        sourceLocalLayerCellVertexSide_eq_retained_compl,
        vertexSetCrossingEdges_compl]]
    rw [← card_vertexSetCrossingEdge]
    exact sourceLocalLayerRetainedCrossing_card_eq_four corridor hunique
      (sourceLocalLayerInteriorAt offset)
      (sourceLocalLayerInteriorAt_hasNext offset)
  have hinternalCard : internal.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro first hfirst second hsecond
    rcases Finset.mem_filter.1 hfirst with ⟨hfirstRegion, hfirstNotCrossing⟩
    rcases Finset.mem_filter.1 hsecond with
      ⟨hsecondRegion, hsecondNotCrossing⟩
    exact sourceLocalLayerCellRegionAt_internalEdge_subsingleton graphData
      minimal caps coloring web corridor hunique offset hfirstRegion
        hfirstNotCrossing hsecondRegion hsecondNotCrossing
  calc
    region.card ≤ (crossing ∪ internal).card := Finset.card_le_card hcover
    _ ≤ crossing.card + internal.card := Finset.card_union_le _ _
    _ ≤ 5 := by omega

/-- In the literal two-cap opening of a closed minimal carrier, every
source-local Cell has at most six regional edges.  The proof eliminates the
cyclic side of the generic dichotomy by pulling its exact four-edge boundary
back to the closed graph. -/
theorem sourceLocalLayerCellRegion_card_le_six
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    (vertexSetRegionEdges web.annular.RS
      (sourceLocalLayerCellVertexSide corridor hunique
        leftInterior hnext)).card ≤ 6 := by
  let side := sourceLocalLayerCellVertexSide corridor hunique leftInterior hnext
  rcases sourceLocalLayerCellRegion_card_le_six_or_hasCycleOnSide
      corridor hunique leftInterior hnext with hcycle | hfinite
  · exact (not_sourceLocalLayerCell_hasCycleOnSide graphData minimal caps coloring web
      corridor hunique leftInterior hnext hcycle).elim
  · simpa [side] using hfinite

/-- Indexed form of the six-edge bound on the literal heterogeneous source
word.  Its Cell carrier is the same complementary vertex-side region as in
the local theorem above. -/
theorem sourceLocalLayerCellRegionAt_card_le_six
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6 := by
  have hcard :=
    sourceLocalLayerCellRegion_card_le_six graphData minimal caps coloring web
      corridor hunique (sourceLocalLayerInteriorAt offset)
        (sourceLocalLayerInteriorAt_hasNext offset)
  rw [sourceLocalLayerCellVertexSide_eq_retained_compl] at hcard
  simpa [sourceLocalLayerCellRegionAt, sourceLocalLayerPairAt,
    sourceLocalLayerBoundaryAt, sourceLocalLayerRetainedVertexSide,
    SeparatedAlignedSimpleDualCrosscuts.sourceCrosscutComplementBoundaryProfileData,
    GoertzelV24RotationBoundaryFaceCutProfile.vertexSetBoundaryGraphCutDataWithIndexing] using
    hcard

/-- The four distinguished positions of an indexed Cell, in source order:
the two incoming crossings followed by the two outgoing crossings. -/
noncomputable def sourceLocalLayerCellPortAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    Fin 4 → {edge // edge ∈ sourceLocalLayerCellRegionAt corridor hunique offset} :=
  fun index => by
    let localPort :=
      GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation.sourceLocalLayerCellPort
        corridor hunique (sourceLocalLayerInteriorAt offset)
          (sourceLocalLayerInteriorAt_hasNext offset) index
    refine ⟨localPort.1, ?_⟩
    have hregion : sourceLocalLayerCellRegionAt corridor hunique offset =
        vertexSetRegionEdges web.annular.RS
          (sourceLocalLayerCellVertexSide corridor hunique
            (sourceLocalLayerInteriorAt offset)
            (sourceLocalLayerInteriorAt_hasNext offset)) := by
      rw [sourceLocalLayerCellVertexSide_eq_retained_compl]
      rfl
    rw [hregion]
    exact localPort.2

/-- The indexed literal word carries an exact six-slot tracked-family code at
every offset.  The code is indexed by the physical Cell, not only by its
coarse orientation. -/
noncomputable def sourceLocalLayerCellTrackedFamilyCodeAt
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    BoundedCarrierGraphFamilyCode 6 4
      GoertzelV24CorridorProfile.TrackedColorPair :=
  boundedCarrierGraphFamilyCode
    (sourceLocalLayerCellRegionAt corridor hunique offset) 6 4
    (sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps coloring web
      corridor hunique offset)
    (sourceLocalLayerCellPortAt corridor hunique offset)
    (fun pair => regionalTrackedEdgeGraph web.annular.RS
      (sourceLocalLayerCellRegionAt corridor hunique offset) coloring
      (trackedColorPairColors pair).1 (trackedColorPairColors pair).2)

/-- Decoding the indexed code preserves complete tracked reachability on the
literal Cell region, in both directions. -/
theorem sourceLocalLayerCellTrackedFamilyCodeAt_reachable_iff
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (pair : GoertzelV24CorridorProfile.TrackedColorPair)
    (first second : {edge // edge ∈
      sourceLocalLayerCellRegionAt corridor hunique offset}) :
    ((sourceLocalLayerCellTrackedFamilyCodeAt graphData minimal caps coloring web
      corridor hunique offset).graph pair).Reachable
        (carrierCoordinate _ first) (carrierCoordinate _ second) ↔
      (regionalTrackedEdgeGraph web.annular.RS
        (sourceLocalLayerCellRegionAt corridor hunique offset)
        coloring (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Reachable first.1 second.1 := by
  refine boundedCarrierGraphFamilyCode_reachable_iff_of_support_subset
    (sourceLocalLayerCellRegionAt corridor hunique offset) 6 4
    (sourceLocalLayerCellRegionAt_card_le_six graphData minimal caps coloring web
      corridor hunique offset)
    (sourceLocalLayerCellPortAt corridor hunique offset)
    (fun trackedPair => regionalTrackedEdgeGraph web.annular.RS
      (sourceLocalLayerCellRegionAt corridor hunique offset) coloring
      (trackedColorPairColors trackedPair).1
        (trackedColorPairColors trackedPair).2)
    pair ?_ first second
  intro edge hedge
  rcases hedge with ⟨other, hadj⟩
  exact hadj.2.1

/-- The preceding unconditional bound instantiates the existing common
six-slot code for all three tracked colour-pair graphs of the literal Cell. -/
noncomputable def sourceLocalLayerCellTrackedFamilyCode
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    BoundedCarrierGraphFamilyCode 6 4
      GoertzelV24CorridorProfile.TrackedColorPair :=
  GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation.sourceLocalLayerCellTrackedFamilyCode
    corridor hunique leftInterior hnext
      (sourceLocalLayerCellRegion_card_le_six graphData minimal caps coloring web
        corridor hunique leftInterior hnext)

/-- The unconditional laboratory code preserves complete regional tracked
reachability, not merely adjacency or a cardinality bound. -/
theorem sourceLocalLayerCellTrackedFamilyCode_reachable_iff
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength)
    (pair : GoertzelV24CorridorProfile.TrackedColorPair)
    (first second : {edge // edge ∈ vertexSetRegionEdges web.annular.RS
      (sourceLocalLayerCellVertexSide corridor hunique leftInterior hnext)}) :
    ((sourceLocalLayerCellTrackedFamilyCode graphData minimal caps coloring web
      corridor hunique leftInterior hnext).graph pair).Reachable
        (carrierCoordinate _ first) (carrierCoordinate _ second) ↔
      (regionalTrackedEdgeGraph web.annular.RS
        (vertexSetRegionEdges web.annular.RS
          (sourceLocalLayerCellVertexSide corridor hunique leftInterior hnext))
        coloring (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Reachable first.1 second.1 := by
  simpa [sourceLocalLayerCellTrackedFamilyCode] using
    (GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation.sourceLocalLayerCellTrackedFamilyCode_reachable_iff
      corridor hunique leftInterior hnext
        (sourceLocalLayerCellRegion_card_le_six graphData minimal caps coloring web
          corridor hunique leftInterior hnext)
      pair first second)

end

end GoertzelV24MinimalFacialPentagonCapPairLocalCellCarrier

end Mettapedia.GraphTheory.FourColor
