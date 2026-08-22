import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerFiniteTrackedLetter
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialPrefixRegion
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalFacialPentagonCapPairNoSmallCut

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
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24OpenRegionRotation.retainedVertexDecidableEq
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq

local instance openedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

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
  let capPair := caps.toFacialPentagonCapPair.toPentagonCapPair
  let side := sourceLocalLayerCellVertexSide corridor hunique leftInterior hnext
  rcases sourceLocalLayerCellRegion_card_le_six_or_hasCycleOnSide
      corridor hunique leftInterior hnext with hcycle | hfinite
  · exfalso
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
    · simpa [side] using hcycle
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
