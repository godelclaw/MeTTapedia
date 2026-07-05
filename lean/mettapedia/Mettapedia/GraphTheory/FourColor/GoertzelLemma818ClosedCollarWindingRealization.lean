import Mettapedia.GraphTheory.FourColor.CyclicEdgeCut
import Mettapedia.GraphTheory.FourColor.GoertzelDefinition48
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarWinding

namespace Mettapedia.GraphTheory.FourColor

/-!
# Closed-collar winding witness realization interface

This module pins the first geometric obstruction found by the direct
realization audit for the `tau,tau::rrbb` winding-freedom witness.  The
witness remains a valid closed-collar winding-freedom witness, but the direct
closed-collar graph has parallel endpoint edges, so it cannot already be the
simple endpoint model required by the normal-form route.
-/

namespace GoertzelLemma818ClosedCollarWindingRealization

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarWinding

def closedCollarEdgesHaveSameUnorderedEndpoints
    (orients : List TauOrient) (e f : ChainEdge) : Bool :=
  let ep := closedCollarEdgeEndpoints orients e
  let fp := closedCollarEdgeEndpoints orients f
  ((ep.1 == fp.1) && (ep.2 == fp.2)) ||
    ((ep.1 == fp.2) && (ep.2 == fp.1))

def closedCollarHasParallelEndpointEdges (orients : List TauOrient) : Prop :=
  ∃ e f,
    e ∈ closedCollarEdges orients ∧
      f ∈ closedCollarEdges orients ∧
      e ≠ f ∧
      closedCollarEdgesHaveSameUnorderedEndpoints orients e f = true

def closedCollarSimpleEndpointRealization (orients : List TauOrient) : Prop :=
  ¬ closedCollarHasParallelEndpointEdges orients

def windingFreedomParallelEdgeA : ChainEdge :=
  { occ := 0, edge := TauEdge.B5 }

def windingFreedomParallelEdgeB : ChainEdge :=
  { occ := 0, edge := TauEdge.B6 }

theorem windingFreedomParallelEdgeA_mem :
    windingFreedomParallelEdgeA ∈ closedCollarEdges windingFreedomWord := by
  decide

theorem windingFreedomParallelEdgeB_mem :
    windingFreedomParallelEdgeB ∈ closedCollarEdges windingFreedomWord := by
  decide

theorem windingFreedomParallelEdges_distinct :
    windingFreedomParallelEdgeA ≠ windingFreedomParallelEdgeB := by
  decide

theorem windingFreedomParallelEdges_same_endpoints :
    closedCollarEdgesHaveSameUnorderedEndpoints windingFreedomWord
      windingFreedomParallelEdgeA windingFreedomParallelEdgeB = true := by
  decide

theorem windingFreedomWord_hasParallelEndpointEdges :
    closedCollarHasParallelEndpointEdges windingFreedomWord := by
  exact
    ⟨windingFreedomParallelEdgeA, windingFreedomParallelEdgeB,
      windingFreedomParallelEdgeA_mem, windingFreedomParallelEdgeB_mem,
      windingFreedomParallelEdges_distinct,
      windingFreedomParallelEdges_same_endpoints⟩

theorem windingFreedomWord_not_simpleEndpointRealization :
    ¬ closedCollarSimpleEndpointRealization windingFreedomWord := by
  intro hsimple
  exact hsimple windingFreedomWord_hasParallelEndpointEdges

def ClosedCollarWindingFreedomWitnessRealizationData : Prop :=
  windingFreedomWord ∈ closedCollarL1Words ∧
    windingFreedomKey ∈ colorAssignments4 ∧
    windingFreedomStateNoWinding ∈
      closedCollarFiber windingFreedomWord windingFreedomKey ∧
    windingFreedomStateWithWinding ∈
      closedCollarFiber windingFreedomWord windingFreedomKey ∧
    closedCollarAggregateCutParityProfile windingFreedomWord
        windingFreedomStateNoWinding =
      closedCollarAggregateCutParityProfile windingFreedomWord
        windingFreedomStateWithWinding ∧
    closedCollarWindingProfile windingFreedomWord
        windingFreedomStateNoWinding ≠
      closedCollarWindingProfile windingFreedomWord
        windingFreedomStateWithWinding

theorem closedCollarWindingFreedomWitnessRealizationData :
    ClosedCollarWindingFreedomWitnessRealizationData := by
  refine
    ⟨?_, ?_, windingFreedom_stateNoWinding_mem,
      windingFreedom_stateWithWinding_mem, ?_, windingFreedom_profiles_differ⟩
  · decide
  · decide
  · exact
      windingFreedom_aggregateParity_same.1.trans
        windingFreedom_aggregateParity_same.2.symm

/--
Graph-facing realization interface for the winding-freedom witness in an
embedded annular collar.  The finite closed-collar witness supplies the
abstract winding data; this structure names the geometric data that a genuine
minimal-counterexample annulus would additionally have to provide.
-/
structure ClosedCollarWindingFreedomAnnularRealization
    (G : SimpleGraph V) where
  outerBoundary : Finset V
  innerBoundary : Finset V
  radialCut : Finset G.edgeSet
  collarEdges : Finset G.edgeSet
  collarCells : Finset (Finset V)
  outerBoundaryEdges : Finset G.edgeSet
  noWindingColoring : G.EdgeColoring Color
  withWindingColoring : G.EdgeColoring Color
  noWindingTait : IsTaitEdgeColoring G noWindingColoring
  withWindingTait : IsTaitEdgeColoring G withWindingColoring
  outerBoundary_nonempty : outerBoundary.Nonempty
  innerBoundary_nonempty : innerBoundary.Nonempty
  outer_inner_disjoint : ∀ v, v ∈ outerBoundary → v ∉ innerBoundary
  radialCut_nonempty : radialCut.Nonempty
  collarEdges_nonempty : collarEdges.Nonempty
  radialCut_subset_collarEdges : radialCut ⊆ collarEdges
  outerBoundaryEdges_subset_collarEdges : outerBoundaryEdges ⊆ collarEdges
  outerBoundary_fixed :
    ∀ e : G.edgeSet, e ∈ outerBoundaryEdges →
      noWindingColoring e = withWindingColoring e
  aggregateCutParityNoWinding : List ((Color × Color) × Bool)
  aggregateCutParityWithWinding : List ((Color × Color) × Bool)
  windingProfileNoWinding : List ((Color × Color) × ClosedCollarWindingCounts)
  windingProfileWithWinding : List ((Color × Color) × ClosedCollarWindingCounts)
  aggregateCutParity_agrees :
    aggregateCutParityNoWinding = aggregateCutParityWithWinding
  windingProfile_differs :
    windingProfileNoWinding ≠ windingProfileWithWinding
  realizesCoreWitness : ClosedCollarWindingFreedomWitnessRealizationData

/--
Normal-form hypotheses for an annular realization of the winding-freedom
witness.  Only cyclic five-edge-connectivity is already connected to a reusable
graph theorem here; the remaining fields record the serious geometric regime
that later work must discharge rather than hiding it inside a lab verdict.
-/
structure ClosedCollarWindingFreedomNormalFormRealization
    (G : SimpleGraph V) where
  annular : ClosedCollarWindingFreedomAnnularRealization G
  cyclicallyFiveEdgeConnected : CyclicallyFiveEdgeConnected G
  cubicBridgelessTaitSetting : Prop
  dualTriangulationNormalForm : Prop
  noSmallSeparatingCuts : Prop
  cap5FreeWhereNeeded : Prop
  actualCollarEmbeddingConstraints : Prop
  hcubicBridgelessTaitSetting : cubicBridgelessTaitSetting
  hdualTriangulationNormalForm : dualTriangulationNormalForm
  hnoSmallSeparatingCuts : noSmallSeparatingCuts
  hcap5FreeWhereNeeded : cap5FreeWhereNeeded
  hactualCollarEmbeddingConstraints : actualCollarEmbeddingConstraints

/--
The direct finite winding-freedom witness is not an honest simple endpoint
normal-form realization.  This is a first-blocker statement for the direct
witness only; it does not rule out a later filler or subdivision search.
-/
def ClosedCollarWindingFreedomDirectWitnessBlockedBySimpleNormalForm : Prop :=
  ClosedCollarWindingFreedomWitnessRealizationData ∧
    closedCollarHasParallelEndpointEdges windingFreedomWord ∧
    ¬ closedCollarSimpleEndpointRealization windingFreedomWord

theorem closedCollarWindingFreedomDirectWitnessBlockedBySimpleNormalForm :
    ClosedCollarWindingFreedomDirectWitnessBlockedBySimpleNormalForm := by
  exact
    ⟨closedCollarWindingFreedomWitnessRealizationData,
      windingFreedomWord_hasParallelEndpointEdges,
      windingFreedomWord_not_simpleEndpointRealization⟩

/--
Numerical interface for a local cubic two-pole replacement of a parallel
bundle.  The two old endpoint vertices contribute two side-internal incident
edges each, every new internal vertex is cubic, and all those incidences are
counted by the side-internal edge count.
-/
structure LocalTwoPoleReplacementStats where
  internalVertexCount : Nat
  sideEdgeCount : Nat
  handshaking :
    2 * sideEdgeCount = 3 * internalVertexCount + 4

/--
The tree bound for the side of a local two-pole replacement with two terminal
vertices and `internalVertexCount` new vertices.  Exceeding this bound is the
rank-count certificate that a connected side contains a cycle.
-/
def LocalTwoPoleReplacementSideExceedsTreeBound
    (stats : LocalTwoPoleReplacementStats) : Prop :=
  stats.internalVertexCount + 1 < stats.sideEdgeCount

theorem localTwoPoleReplacementSideExceedsTreeBound
    (stats : LocalTwoPoleReplacementStats) :
    LocalTwoPoleReplacementSideExceedsTreeBound stats := by
  unfold LocalTwoPoleReplacementSideExceedsTreeBound
  have htwice :
      2 * (stats.internalVertexCount + 1) <
        2 * stats.sideEdgeCount := by
    have hhand := stats.handshaking
    omega
  exact Nat.lt_of_mul_lt_mul_left htwice

def LocalTwoPoleDesingularizationCannotRemoveCyclicTwoCut : Prop :=
  ∀ stats : LocalTwoPoleReplacementStats,
    LocalTwoPoleReplacementSideExceedsTreeBound stats

theorem localTwoPoleDesingularizationCannotRemoveCyclicTwoCut :
    LocalTwoPoleDesingularizationCannotRemoveCyclicTwoCut := by
  intro stats
  exact localTwoPoleReplacementSideExceedsTreeBound stats

/--
Summary counts for the bounded simple cubic four-terminal patch search.  The
search deletes the two parallel endpoint bundles in the `tau,tau::rrbb`
witness, inserts a simple cubic patch with at most four new internal vertices,
tests both radial orders at the closing terminal, and requires every state in
the fixed-boundary fiber to extend with the same winding profile.
-/
structure ClosedCollarSimplePatchSearchCounts where
  maxInternalVertices : Nat
  patchTopologyCount : Nat
  radialOrderCaseCount : Nat
  profilePreservingCaseCount : Nat
  normalFormPrefixPassingProfileCaseCount : Nat
  planarFirstBlockerCount : Nat
  cyclicCutFirstBlockerCount : Nat

def closedCollarSimplePatchSearchLe4Counts :
    ClosedCollarSimplePatchSearchCounts where
  maxInternalVertices := 4
  patchTopologyCount := 6114
  radialOrderCaseCount := 12228
  profilePreservingCaseCount := 108
  normalFormPrefixPassingProfileCaseCount := 0
  planarFirstBlockerCount := 96
  cyclicCutFirstBlockerCount := 12

/--
Bounded simple-patch verdict for the winding-freedom witness.  Up to four new
internal patch vertices, the witness is not killed by simple cubic replacement:
108 cases preserve the full component-level winding profile.  None of those
cases passes the tested normal-form prefix; the first blockers split between
planarity and cyclic edge cuts of size at most four.
-/
def ClosedCollarWindingFreedomSimplePatchSearchLe4BlockedByNormalFormPrefix :
    Prop :=
  ClosedCollarWindingFreedomWitnessRealizationData ∧
    closedCollarSimplePatchSearchLe4Counts.maxInternalVertices = 4 ∧
    closedCollarSimplePatchSearchLe4Counts.patchTopologyCount = 6114 ∧
    closedCollarSimplePatchSearchLe4Counts.radialOrderCaseCount = 12228 ∧
    closedCollarSimplePatchSearchLe4Counts.profilePreservingCaseCount = 108 ∧
    closedCollarSimplePatchSearchLe4Counts.normalFormPrefixPassingProfileCaseCount = 0 ∧
    closedCollarSimplePatchSearchLe4Counts.planarFirstBlockerCount = 96 ∧
    closedCollarSimplePatchSearchLe4Counts.cyclicCutFirstBlockerCount = 12 ∧
    closedCollarSimplePatchSearchLe4Counts.planarFirstBlockerCount +
        closedCollarSimplePatchSearchLe4Counts.cyclicCutFirstBlockerCount =
      closedCollarSimplePatchSearchLe4Counts.profilePreservingCaseCount

theorem closedCollarWindingFreedomSimplePatchSearchLe4BlockedByNormalFormPrefix :
    ClosedCollarWindingFreedomSimplePatchSearchLe4BlockedByNormalFormPrefix := by
  refine
    ⟨closedCollarWindingFreedomWitnessRealizationData,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/--
Counts for a resumable exact-size simple-patch search slice.  These are not
exhaustive verdicts for the whole exact-size space; they pin archived slices
with explicit start and next-start indices.
-/
structure ClosedCollarSimplePatchSliceCounts where
  internalVertexCount : Nat
  patchStartIndex : Nat
  patchTopologyLimit : Nat
  nextPatchStartIndex : Nat
  processedPatchTopologyCount : Nat
  radialOrderCaseCount : Nat
  profilePreservingCaseCount : Nat
  normalFormPrefixPassingProfileCaseCount : Nat
  planarFirstBlockerCount : Nat

def closedCollarSimplePatchN6Slice0_50000Counts :
    ClosedCollarSimplePatchSliceCounts where
  internalVertexCount := 6
  patchStartIndex := 0
  patchTopologyLimit := 50000
  nextPatchStartIndex := 50000
  processedPatchTopologyCount := 50000
  radialOrderCaseCount := 100000
  profilePreservingCaseCount := 0
  normalFormPrefixPassingProfileCaseCount := 0
  planarFirstBlockerCount := 0

def closedCollarSimplePatchN6Slice50000_100000Counts :
    ClosedCollarSimplePatchSliceCounts where
  internalVertexCount := 6
  patchStartIndex := 50000
  patchTopologyLimit := 50000
  nextPatchStartIndex := 100000
  processedPatchTopologyCount := 50000
  radialOrderCaseCount := 100000
  profilePreservingCaseCount := 3744
  normalFormPrefixPassingProfileCaseCount := 0
  planarFirstBlockerCount := 3744

def closedCollarSimplePatchN6Slice100000_150000Counts :
    ClosedCollarSimplePatchSliceCounts where
  internalVertexCount := 6
  patchStartIndex := 100000
  patchTopologyLimit := 50000
  nextPatchStartIndex := 150000
  processedPatchTopologyCount := 50000
  radialOrderCaseCount := 100000
  profilePreservingCaseCount := 4180
  normalFormPrefixPassingProfileCaseCount := 0
  planarFirstBlockerCount := 4180

def closedCollarSimplePatchN6First150000ProcessedCount : Nat :=
  closedCollarSimplePatchN6Slice0_50000Counts.processedPatchTopologyCount +
    closedCollarSimplePatchN6Slice50000_100000Counts.processedPatchTopologyCount +
      closedCollarSimplePatchN6Slice100000_150000Counts.processedPatchTopologyCount

def closedCollarSimplePatchN6First150000RadialOrderCount : Nat :=
  closedCollarSimplePatchN6Slice0_50000Counts.radialOrderCaseCount +
    closedCollarSimplePatchN6Slice50000_100000Counts.radialOrderCaseCount +
      closedCollarSimplePatchN6Slice100000_150000Counts.radialOrderCaseCount

def closedCollarSimplePatchN6First150000ProfilePreservingCount : Nat :=
  closedCollarSimplePatchN6Slice0_50000Counts.profilePreservingCaseCount +
    closedCollarSimplePatchN6Slice50000_100000Counts.profilePreservingCaseCount +
      closedCollarSimplePatchN6Slice100000_150000Counts.profilePreservingCaseCount

def closedCollarSimplePatchN6First150000NormalFormPrefixPassingCount : Nat :=
  closedCollarSimplePatchN6Slice0_50000Counts.normalFormPrefixPassingProfileCaseCount +
    closedCollarSimplePatchN6Slice50000_100000Counts.normalFormPrefixPassingProfileCaseCount +
      closedCollarSimplePatchN6Slice100000_150000Counts.normalFormPrefixPassingProfileCaseCount

def closedCollarSimplePatchN6First150000PlanarFirstBlockerCount : Nat :=
  closedCollarSimplePatchN6Slice0_50000Counts.planarFirstBlockerCount +
    closedCollarSimplePatchN6Slice50000_100000Counts.planarFirstBlockerCount +
      closedCollarSimplePatchN6Slice100000_150000Counts.planarFirstBlockerCount

/--
Resumable-slice evidence for the six-internal simple-patch search.  In the
first 150000 exact-size topologies, 7924 radial-order cases preserve the full
winding profile.  None passes the tested normal-form prefix, and every
profile-preserving case in these slices fails first at planarity.
-/
def ClosedCollarWindingFreedomSimplePatchN6First150000BlockedByPlanarityEvidence :
    Prop :=
  ClosedCollarWindingFreedomWitnessRealizationData ∧
    closedCollarSimplePatchN6First150000ProcessedCount = 150000 ∧
    closedCollarSimplePatchN6First150000RadialOrderCount = 300000 ∧
    closedCollarSimplePatchN6First150000ProfilePreservingCount = 7924 ∧
    closedCollarSimplePatchN6First150000NormalFormPrefixPassingCount = 0 ∧
    closedCollarSimplePatchN6First150000PlanarFirstBlockerCount = 7924 ∧
    closedCollarSimplePatchN6First150000PlanarFirstBlockerCount =
      closedCollarSimplePatchN6First150000ProfilePreservingCount

theorem closedCollarWindingFreedomSimplePatchN6First150000BlockedByPlanarityEvidence :
    ClosedCollarWindingFreedomSimplePatchN6First150000BlockedByPlanarityEvidence := by
  refine
    ⟨closedCollarWindingFreedomWitnessRealizationData,
      ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

def closedCollarSimplePatchN6Slice150000_200000Counts :
    ClosedCollarSimplePatchSliceCounts where
  internalVertexCount := 6
  patchStartIndex := 150000
  patchTopologyLimit := 50000
  nextPatchStartIndex := 200000
  processedPatchTopologyCount := 50000
  radialOrderCaseCount := 100000
  profilePreservingCaseCount := 3900
  normalFormPrefixPassingProfileCaseCount := 0
  planarFirstBlockerCount := 3900

def closedCollarSimplePatchN6Slice200000_250000Counts :
    ClosedCollarSimplePatchSliceCounts where
  internalVertexCount := 6
  patchStartIndex := 200000
  patchTopologyLimit := 50000
  nextPatchStartIndex := 250000
  processedPatchTopologyCount := 50000
  radialOrderCaseCount := 100000
  profilePreservingCaseCount := 3776
  normalFormPrefixPassingProfileCaseCount := 0
  planarFirstBlockerCount := 3776

def closedCollarSimplePatchN6Slice250000_300000Counts :
    ClosedCollarSimplePatchSliceCounts where
  internalVertexCount := 6
  patchStartIndex := 250000
  patchTopologyLimit := 50000
  nextPatchStartIndex := 300000
  processedPatchTopologyCount := 50000
  radialOrderCaseCount := 100000
  profilePreservingCaseCount := 3120
  normalFormPrefixPassingProfileCaseCount := 0
  planarFirstBlockerCount := 3120

def closedCollarSimplePatchN6First300000ProcessedCount : Nat :=
  closedCollarSimplePatchN6First150000ProcessedCount +
    closedCollarSimplePatchN6Slice150000_200000Counts.processedPatchTopologyCount +
      closedCollarSimplePatchN6Slice200000_250000Counts.processedPatchTopologyCount +
        closedCollarSimplePatchN6Slice250000_300000Counts.processedPatchTopologyCount

def closedCollarSimplePatchN6First300000RadialOrderCount : Nat :=
  closedCollarSimplePatchN6First150000RadialOrderCount +
    closedCollarSimplePatchN6Slice150000_200000Counts.radialOrderCaseCount +
      closedCollarSimplePatchN6Slice200000_250000Counts.radialOrderCaseCount +
        closedCollarSimplePatchN6Slice250000_300000Counts.radialOrderCaseCount

def closedCollarSimplePatchN6First300000ProfilePreservingCount : Nat :=
  closedCollarSimplePatchN6First150000ProfilePreservingCount +
    closedCollarSimplePatchN6Slice150000_200000Counts.profilePreservingCaseCount +
      closedCollarSimplePatchN6Slice200000_250000Counts.profilePreservingCaseCount +
        closedCollarSimplePatchN6Slice250000_300000Counts.profilePreservingCaseCount

def closedCollarSimplePatchN6First300000NormalFormPrefixPassingCount : Nat :=
  closedCollarSimplePatchN6First150000NormalFormPrefixPassingCount +
    closedCollarSimplePatchN6Slice150000_200000Counts.normalFormPrefixPassingProfileCaseCount +
      closedCollarSimplePatchN6Slice200000_250000Counts.normalFormPrefixPassingProfileCaseCount +
        closedCollarSimplePatchN6Slice250000_300000Counts.normalFormPrefixPassingProfileCaseCount

def closedCollarSimplePatchN6First300000PlanarFirstBlockerCount : Nat :=
  closedCollarSimplePatchN6First150000PlanarFirstBlockerCount +
    closedCollarSimplePatchN6Slice150000_200000Counts.planarFirstBlockerCount +
      closedCollarSimplePatchN6Slice200000_250000Counts.planarFirstBlockerCount +
        closedCollarSimplePatchN6Slice250000_300000Counts.planarFirstBlockerCount

/--
Expanded resumable-slice evidence for the six-internal simple-patch search.
In the first 300000 exact-size topologies, 18720 radial-order cases preserve
the full winding profile.  None passes the tested normal-form prefix, and
every profile-preserving case in these slices fails first at planarity.
-/
def ClosedCollarWindingFreedomSimplePatchN6First300000BlockedByPlanarityEvidence :
    Prop :=
  ClosedCollarWindingFreedomWitnessRealizationData ∧
    closedCollarSimplePatchN6First300000ProcessedCount = 300000 ∧
    closedCollarSimplePatchN6First300000RadialOrderCount = 600000 ∧
    closedCollarSimplePatchN6First300000ProfilePreservingCount = 18720 ∧
    closedCollarSimplePatchN6First300000NormalFormPrefixPassingCount = 0 ∧
    closedCollarSimplePatchN6First300000PlanarFirstBlockerCount = 18720 ∧
    closedCollarSimplePatchN6First300000PlanarFirstBlockerCount =
      closedCollarSimplePatchN6First300000ProfilePreservingCount

theorem closedCollarWindingFreedomSimplePatchN6First300000BlockedByPlanarityEvidence :
    ClosedCollarWindingFreedomSimplePatchN6First300000BlockedByPlanarityEvidence := by
  refine
    ⟨closedCollarWindingFreedomWitnessRealizationData,
      ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/--
Expanded cumulative counts for the six-internal simple-patch search.  This
record is used once the search reaches planar profile-preserving cases, so the
first blocker is no longer only planarity.
-/
structure ClosedCollarSimplePatchPrefixBlockerCounts where
  internalVertexCount : Nat
  processedPatchTopologyCount : Nat
  radialOrderCaseCount : Nat
  profilePreservingCaseCount : Nat
  normalFormPrefixPassingProfileCaseCount : Nat
  planarFirstBlockerCount : Nat
  cyclicCutFirstBlockerCount : Nat
  minimumCyclicCutSizeTwoCount : Nat
  minimumCyclicCutSizeThreeCount : Nat

def closedCollarSimplePatchN6First900000Counts :
    ClosedCollarSimplePatchPrefixBlockerCounts where
  internalVertexCount := 6
  processedPatchTopologyCount := 900000
  radialOrderCaseCount := 1800000
  profilePreservingCaseCount := 19810
  normalFormPrefixPassingProfileCaseCount := 0
  planarFirstBlockerCount := 19576
  cyclicCutFirstBlockerCount := 234
  minimumCyclicCutSizeTwoCount := 222
  minimumCyclicCutSizeThreeCount := 12

/--
Resumable-slice evidence for the first 900000 six-internal simple-patch
topologies.  Profile-preserving patches do include planar cases in this range,
but no profile-preserving case passes the tested normal-form prefix: 19576 fail
first at planarity, and 234 planar cases fail first at cyclic edge cuts of size
at most four.
-/
def ClosedCollarWindingFreedomSimplePatchN6First900000BlockedByPlanarityOrCyclicCutsEvidence :
    Prop :=
  ClosedCollarWindingFreedomWitnessRealizationData ∧
    closedCollarSimplePatchN6First900000Counts.internalVertexCount = 6 ∧
    closedCollarSimplePatchN6First900000Counts.processedPatchTopologyCount = 900000 ∧
    closedCollarSimplePatchN6First900000Counts.radialOrderCaseCount = 1800000 ∧
    closedCollarSimplePatchN6First900000Counts.profilePreservingCaseCount = 19810 ∧
    closedCollarSimplePatchN6First900000Counts.normalFormPrefixPassingProfileCaseCount = 0 ∧
    closedCollarSimplePatchN6First900000Counts.planarFirstBlockerCount = 19576 ∧
    closedCollarSimplePatchN6First900000Counts.cyclicCutFirstBlockerCount = 234 ∧
    closedCollarSimplePatchN6First900000Counts.minimumCyclicCutSizeTwoCount = 222 ∧
    closedCollarSimplePatchN6First900000Counts.minimumCyclicCutSizeThreeCount = 12 ∧
    closedCollarSimplePatchN6First900000Counts.planarFirstBlockerCount +
        closedCollarSimplePatchN6First900000Counts.cyclicCutFirstBlockerCount =
      closedCollarSimplePatchN6First900000Counts.profilePreservingCaseCount ∧
    closedCollarSimplePatchN6First900000Counts.minimumCyclicCutSizeTwoCount +
        closedCollarSimplePatchN6First900000Counts.minimumCyclicCutSizeThreeCount =
      closedCollarSimplePatchN6First900000Counts.cyclicCutFirstBlockerCount

theorem closedCollarWindingFreedomSimplePatchN6First900000BlockedByPlanarityOrCyclicCutsEvidence :
    ClosedCollarWindingFreedomSimplePatchN6First900000BlockedByPlanarityOrCyclicCutsEvidence := by
  refine
    ⟨closedCollarWindingFreedomWitnessRealizationData,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

def closedCollarSimplePatchN6First950000Counts :
    ClosedCollarSimplePatchPrefixBlockerCounts where
  internalVertexCount := 6
  processedPatchTopologyCount := 950000
  radialOrderCaseCount := 1900000
  profilePreservingCaseCount := 20208
  normalFormPrefixPassingProfileCaseCount := 0
  planarFirstBlockerCount := 19920
  cyclicCutFirstBlockerCount := 288
  minimumCyclicCutSizeTwoCount := 264
  minimumCyclicCutSizeThreeCount := 24

/--
Resumable-slice evidence through the first 950000 six-internal simple-patch
topologies.  The additional 900000-950000 slice again finds planar
profile-preserving cases, but every profile-preserving case still fails the
tested normal-form prefix by planarity or by a cyclic edge cut of size at most
four.
-/
def ClosedCollarWindingFreedomSimplePatchN6First950000BlockedByPlanarityOrCyclicCutsEvidence :
    Prop :=
  ClosedCollarWindingFreedomWitnessRealizationData ∧
    closedCollarSimplePatchN6First950000Counts.internalVertexCount = 6 ∧
    closedCollarSimplePatchN6First950000Counts.processedPatchTopologyCount = 950000 ∧
    closedCollarSimplePatchN6First950000Counts.radialOrderCaseCount = 1900000 ∧
    closedCollarSimplePatchN6First950000Counts.profilePreservingCaseCount = 20208 ∧
    closedCollarSimplePatchN6First950000Counts.normalFormPrefixPassingProfileCaseCount = 0 ∧
    closedCollarSimplePatchN6First950000Counts.planarFirstBlockerCount = 19920 ∧
    closedCollarSimplePatchN6First950000Counts.cyclicCutFirstBlockerCount = 288 ∧
    closedCollarSimplePatchN6First950000Counts.minimumCyclicCutSizeTwoCount = 264 ∧
    closedCollarSimplePatchN6First950000Counts.minimumCyclicCutSizeThreeCount = 24 ∧
    closedCollarSimplePatchN6First950000Counts.planarFirstBlockerCount +
        closedCollarSimplePatchN6First950000Counts.cyclicCutFirstBlockerCount =
      closedCollarSimplePatchN6First950000Counts.profilePreservingCaseCount ∧
    closedCollarSimplePatchN6First950000Counts.minimumCyclicCutSizeTwoCount +
        closedCollarSimplePatchN6First950000Counts.minimumCyclicCutSizeThreeCount =
      closedCollarSimplePatchN6First950000Counts.cyclicCutFirstBlockerCount

theorem closedCollarWindingFreedomSimplePatchN6First950000BlockedByPlanarityOrCyclicCutsEvidence :
    ClosedCollarWindingFreedomSimplePatchN6First950000BlockedByPlanarityOrCyclicCutsEvidence := by
  refine
    ⟨closedCollarWindingFreedomWitnessRealizationData,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

def closedCollarSimplePatchN6First1000000Counts :
    ClosedCollarSimplePatchPrefixBlockerCounts where
  internalVertexCount := 6
  processedPatchTopologyCount := 1000000
  radialOrderCaseCount := 2000000
  profilePreservingCaseCount := 20870
  normalFormPrefixPassingProfileCaseCount := 0
  planarFirstBlockerCount := 20454
  cyclicCutFirstBlockerCount := 416
  minimumCyclicCutSizeTwoCount := 380
  minimumCyclicCutSizeThreeCount := 36

/--
Resumable-slice evidence through the first 1000000 six-internal simple-patch
topologies.  No profile-preserving case passes the tested normal-form prefix;
the profile-preserving cases fail first at planarity or at a cyclic edge cut of
size at most four.
-/
def ClosedCollarWindingFreedomSimplePatchN6First1000000BlockedByPlanarityOrCyclicCutsEvidence :
    Prop :=
  ClosedCollarWindingFreedomWitnessRealizationData ∧
    closedCollarSimplePatchN6First1000000Counts.internalVertexCount = 6 ∧
    closedCollarSimplePatchN6First1000000Counts.processedPatchTopologyCount = 1000000 ∧
    closedCollarSimplePatchN6First1000000Counts.radialOrderCaseCount = 2000000 ∧
    closedCollarSimplePatchN6First1000000Counts.profilePreservingCaseCount = 20870 ∧
    closedCollarSimplePatchN6First1000000Counts.normalFormPrefixPassingProfileCaseCount = 0 ∧
    closedCollarSimplePatchN6First1000000Counts.planarFirstBlockerCount = 20454 ∧
    closedCollarSimplePatchN6First1000000Counts.cyclicCutFirstBlockerCount = 416 ∧
    closedCollarSimplePatchN6First1000000Counts.minimumCyclicCutSizeTwoCount = 380 ∧
    closedCollarSimplePatchN6First1000000Counts.minimumCyclicCutSizeThreeCount = 36 ∧
    closedCollarSimplePatchN6First1000000Counts.planarFirstBlockerCount +
        closedCollarSimplePatchN6First1000000Counts.cyclicCutFirstBlockerCount =
      closedCollarSimplePatchN6First1000000Counts.profilePreservingCaseCount ∧
    closedCollarSimplePatchN6First1000000Counts.minimumCyclicCutSizeTwoCount +
        closedCollarSimplePatchN6First1000000Counts.minimumCyclicCutSizeThreeCount =
      closedCollarSimplePatchN6First1000000Counts.cyclicCutFirstBlockerCount

theorem closedCollarWindingFreedomSimplePatchN6First1000000BlockedByPlanarityOrCyclicCutsEvidence :
    ClosedCollarWindingFreedomSimplePatchN6First1000000BlockedByPlanarityOrCyclicCutsEvidence := by
  refine
    ⟨closedCollarWindingFreedomWitnessRealizationData,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/--
Shape-classification counts for a single resumable simple-patch slice.  This
records a second-pass classifier over the cyclic-cut blockers; it is separate
from the main prefix verdict because it inspects the shape of the first sampled
small cyclic cut.
-/
structure ClosedCollarSimplePatchCyclicCutShapeSliceCounts where
  internalVertexCount : Nat
  patchStartIndex : Nat
  patchTopologyLimit : Nat
  sampledCyclicCutLimit : Nat
  processedPatchTopologyCount : Nat
  radialOrderCaseCount : Nat
  profilePreservingCaseCount : Nat
  planarFirstBlockerCount : Nat
  cyclicCutFirstBlockerCount : Nat
  firstCutSizeTwoCount : Nat
  firstCutUsesTwoCollarEdgesCount : Nat
  firstCutSideHasFourVerticesCount : Nat
  firstCutSideHasTwoCollarAndTwoPatchInternalVerticesCount : Nat

def closedCollarSimplePatchN6Slice900000_950000CyclicCutShapeCounts :
    ClosedCollarSimplePatchCyclicCutShapeSliceCounts where
  internalVertexCount := 6
  patchStartIndex := 900000
  patchTopologyLimit := 50000
  sampledCyclicCutLimit := 24
  processedPatchTopologyCount := 50000
  radialOrderCaseCount := 100000
  profilePreservingCaseCount := 398
  planarFirstBlockerCount := 344
  cyclicCutFirstBlockerCount := 54
  firstCutSizeTwoCount := 54
  firstCutUsesTwoCollarEdgesCount := 54
  firstCutSideHasFourVerticesCount := 54
  firstCutSideHasTwoCollarAndTwoPatchInternalVerticesCount := 54

def closedCollarSimplePatchN6Slice800000_850000CyclicCutShapeCounts :
    ClosedCollarSimplePatchCyclicCutShapeSliceCounts where
  internalVertexCount := 6
  patchStartIndex := 800000
  patchTopologyLimit := 50000
  sampledCyclicCutLimit := 24
  processedPatchTopologyCount := 50000
  radialOrderCaseCount := 100000
  profilePreservingCaseCount := 664
  planarFirstBlockerCount := 536
  cyclicCutFirstBlockerCount := 128
  firstCutSizeTwoCount := 128
  firstCutUsesTwoCollarEdgesCount := 128
  firstCutSideHasFourVerticesCount := 128
  firstCutSideHasTwoCollarAndTwoPatchInternalVerticesCount := 128

def closedCollarSimplePatchN6Slice850000_900000CyclicCutShapeCounts :
    ClosedCollarSimplePatchCyclicCutShapeSliceCounts where
  internalVertexCount := 6
  patchStartIndex := 850000
  patchTopologyLimit := 50000
  sampledCyclicCutLimit := 24
  processedPatchTopologyCount := 50000
  radialOrderCaseCount := 100000
  profilePreservingCaseCount := 426
  planarFirstBlockerCount := 320
  cyclicCutFirstBlockerCount := 106
  firstCutSizeTwoCount := 106
  firstCutUsesTwoCollarEdgesCount := 106
  firstCutSideHasFourVerticesCount := 106
  firstCutSideHasTwoCollarAndTwoPatchInternalVerticesCount := 106

def closedCollarSimplePatchN6Slices800000_950000CyclicCutShapeCounts :
    ClosedCollarSimplePatchCyclicCutShapeSliceCounts where
  internalVertexCount := 6
  patchStartIndex := 800000
  patchTopologyLimit := 150000
  sampledCyclicCutLimit := 24
  processedPatchTopologyCount := 150000
  radialOrderCaseCount := 300000
  profilePreservingCaseCount := 1488
  planarFirstBlockerCount := 1200
  cyclicCutFirstBlockerCount := 288
  firstCutSizeTwoCount := 288
  firstCutUsesTwoCollarEdgesCount := 288
  firstCutSideHasFourVerticesCount := 288
  firstCutSideHasTwoCollarAndTwoPatchInternalVerticesCount := 288

def closedCollarSimplePatchN6Slice950000_1000000CyclicCutShapeCounts :
    ClosedCollarSimplePatchCyclicCutShapeSliceCounts where
  internalVertexCount := 6
  patchStartIndex := 950000
  patchTopologyLimit := 50000
  sampledCyclicCutLimit := 24
  processedPatchTopologyCount := 50000
  radialOrderCaseCount := 100000
  profilePreservingCaseCount := 662
  planarFirstBlockerCount := 534
  cyclicCutFirstBlockerCount := 128
  firstCutSizeTwoCount := 128
  firstCutUsesTwoCollarEdgesCount := 128
  firstCutSideHasFourVerticesCount := 128
  firstCutSideHasTwoCollarAndTwoPatchInternalVerticesCount := 128

def closedCollarSimplePatchN6Slices800000_1000000CyclicCutShapeCounts :
    ClosedCollarSimplePatchCyclicCutShapeSliceCounts where
  internalVertexCount := 6
  patchStartIndex := 800000
  patchTopologyLimit := 200000
  sampledCyclicCutLimit := 24
  processedPatchTopologyCount := 200000
  radialOrderCaseCount := 400000
  profilePreservingCaseCount := 2150
  planarFirstBlockerCount := 1734
  cyclicCutFirstBlockerCount := 416
  firstCutSizeTwoCount := 416
  firstCutUsesTwoCollarEdgesCount := 416
  firstCutSideHasFourVerticesCount := 416
  firstCutSideHasTwoCollarAndTwoPatchInternalVerticesCount := 416

/--
Second-pass cyclic-cut shape evidence for the 900000-950000 six-internal
simple-patch slice.  Every cyclic-cut blocker in this slice has a first sampled
cut of size two, the two cut edges are both collar edges, and the small side has
exactly two collar vertices and two patch-internal vertices.
-/
def ClosedCollarWindingFreedomSimplePatchN6Slice900000_950000UniformCollarTwoCutShapeEvidence :
    Prop :=
  ClosedCollarWindingFreedomWitnessRealizationData ∧
    closedCollarSimplePatchN6Slice900000_950000CyclicCutShapeCounts.internalVertexCount = 6 ∧
    closedCollarSimplePatchN6Slice900000_950000CyclicCutShapeCounts.patchStartIndex = 900000 ∧
    closedCollarSimplePatchN6Slice900000_950000CyclicCutShapeCounts.patchTopologyLimit = 50000 ∧
    closedCollarSimplePatchN6Slice900000_950000CyclicCutShapeCounts.sampledCyclicCutLimit = 24 ∧
    closedCollarSimplePatchN6Slice900000_950000CyclicCutShapeCounts.processedPatchTopologyCount =
      50000 ∧
    closedCollarSimplePatchN6Slice900000_950000CyclicCutShapeCounts.radialOrderCaseCount =
      100000 ∧
    closedCollarSimplePatchN6Slice900000_950000CyclicCutShapeCounts.profilePreservingCaseCount =
      398 ∧
    closedCollarSimplePatchN6Slice900000_950000CyclicCutShapeCounts.planarFirstBlockerCount =
      344 ∧
    closedCollarSimplePatchN6Slice900000_950000CyclicCutShapeCounts.cyclicCutFirstBlockerCount =
      54 ∧
    closedCollarSimplePatchN6Slice900000_950000CyclicCutShapeCounts.firstCutSizeTwoCount =
      closedCollarSimplePatchN6Slice900000_950000CyclicCutShapeCounts.cyclicCutFirstBlockerCount ∧
    closedCollarSimplePatchN6Slice900000_950000CyclicCutShapeCounts.firstCutUsesTwoCollarEdgesCount =
      closedCollarSimplePatchN6Slice900000_950000CyclicCutShapeCounts.cyclicCutFirstBlockerCount ∧
    closedCollarSimplePatchN6Slice900000_950000CyclicCutShapeCounts.firstCutSideHasFourVerticesCount =
      closedCollarSimplePatchN6Slice900000_950000CyclicCutShapeCounts.cyclicCutFirstBlockerCount ∧
    closedCollarSimplePatchN6Slice900000_950000CyclicCutShapeCounts.firstCutSideHasTwoCollarAndTwoPatchInternalVerticesCount =
      closedCollarSimplePatchN6Slice900000_950000CyclicCutShapeCounts.cyclicCutFirstBlockerCount ∧
    closedCollarSimplePatchN6Slice900000_950000CyclicCutShapeCounts.planarFirstBlockerCount +
        closedCollarSimplePatchN6Slice900000_950000CyclicCutShapeCounts.cyclicCutFirstBlockerCount =
      closedCollarSimplePatchN6Slice900000_950000CyclicCutShapeCounts.profilePreservingCaseCount

theorem closedCollarWindingFreedomSimplePatchN6Slice900000_950000UniformCollarTwoCutShapeEvidence :
    ClosedCollarWindingFreedomSimplePatchN6Slice900000_950000UniformCollarTwoCutShapeEvidence := by
  refine
    ⟨closedCollarWindingFreedomWitnessRealizationData,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/--
Cumulative second-pass cyclic-cut shape evidence for the 800000-950000
six-internal simple-patch slices.  Across the three slices where planar
profile-preserving cyclic-cut blockers first appear, every cyclic-cut blocker
has a first sampled cut of size two, with two collar cut edges and a four-vertex
small side made of two collar vertices and two patch-internal vertices.
-/
def ClosedCollarWindingFreedomSimplePatchN6Slices800000_950000UniformCollarTwoCutShapeEvidence :
    Prop :=
  ClosedCollarWindingFreedomWitnessRealizationData ∧
    closedCollarSimplePatchN6Slice800000_850000CyclicCutShapeCounts.cyclicCutFirstBlockerCount =
      128 ∧
    closedCollarSimplePatchN6Slice850000_900000CyclicCutShapeCounts.cyclicCutFirstBlockerCount =
      106 ∧
    closedCollarSimplePatchN6Slice900000_950000CyclicCutShapeCounts.cyclicCutFirstBlockerCount =
      54 ∧
    closedCollarSimplePatchN6Slices800000_950000CyclicCutShapeCounts.internalVertexCount =
      6 ∧
    closedCollarSimplePatchN6Slices800000_950000CyclicCutShapeCounts.patchStartIndex =
      800000 ∧
    closedCollarSimplePatchN6Slices800000_950000CyclicCutShapeCounts.patchTopologyLimit =
      150000 ∧
    closedCollarSimplePatchN6Slices800000_950000CyclicCutShapeCounts.sampledCyclicCutLimit =
      24 ∧
    closedCollarSimplePatchN6Slices800000_950000CyclicCutShapeCounts.processedPatchTopologyCount =
      150000 ∧
    closedCollarSimplePatchN6Slices800000_950000CyclicCutShapeCounts.radialOrderCaseCount =
      300000 ∧
    closedCollarSimplePatchN6Slices800000_950000CyclicCutShapeCounts.profilePreservingCaseCount =
      1488 ∧
    closedCollarSimplePatchN6Slices800000_950000CyclicCutShapeCounts.planarFirstBlockerCount =
      1200 ∧
    closedCollarSimplePatchN6Slices800000_950000CyclicCutShapeCounts.cyclicCutFirstBlockerCount =
      288 ∧
    closedCollarSimplePatchN6Slices800000_950000CyclicCutShapeCounts.firstCutSizeTwoCount =
      closedCollarSimplePatchN6Slices800000_950000CyclicCutShapeCounts.cyclicCutFirstBlockerCount ∧
    closedCollarSimplePatchN6Slices800000_950000CyclicCutShapeCounts.firstCutUsesTwoCollarEdgesCount =
      closedCollarSimplePatchN6Slices800000_950000CyclicCutShapeCounts.cyclicCutFirstBlockerCount ∧
    closedCollarSimplePatchN6Slices800000_950000CyclicCutShapeCounts.firstCutSideHasFourVerticesCount =
      closedCollarSimplePatchN6Slices800000_950000CyclicCutShapeCounts.cyclicCutFirstBlockerCount ∧
    closedCollarSimplePatchN6Slices800000_950000CyclicCutShapeCounts.firstCutSideHasTwoCollarAndTwoPatchInternalVerticesCount =
      closedCollarSimplePatchN6Slices800000_950000CyclicCutShapeCounts.cyclicCutFirstBlockerCount ∧
    closedCollarSimplePatchN6Slices800000_950000CyclicCutShapeCounts.planarFirstBlockerCount +
        closedCollarSimplePatchN6Slices800000_950000CyclicCutShapeCounts.cyclicCutFirstBlockerCount =
      closedCollarSimplePatchN6Slices800000_950000CyclicCutShapeCounts.profilePreservingCaseCount ∧
    closedCollarSimplePatchN6Slice800000_850000CyclicCutShapeCounts.cyclicCutFirstBlockerCount +
        closedCollarSimplePatchN6Slice850000_900000CyclicCutShapeCounts.cyclicCutFirstBlockerCount +
          closedCollarSimplePatchN6Slice900000_950000CyclicCutShapeCounts.cyclicCutFirstBlockerCount =
      closedCollarSimplePatchN6Slices800000_950000CyclicCutShapeCounts.cyclicCutFirstBlockerCount

theorem closedCollarWindingFreedomSimplePatchN6Slices800000_950000UniformCollarTwoCutShapeEvidence :
    ClosedCollarWindingFreedomSimplePatchN6Slices800000_950000UniformCollarTwoCutShapeEvidence := by
  refine
    ⟨closedCollarWindingFreedomWitnessRealizationData,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    decide

/--
Cumulative second-pass cyclic-cut shape evidence for the 800000-1000000
six-internal simple-patch slices.  Across these four slices, every cyclic-cut
blocker has a first sampled cut of size two, with two collar cut edges and a
four-vertex small side made of two collar vertices and two patch-internal
vertices.
-/
def ClosedCollarWindingFreedomSimplePatchN6Slices800000_1000000UniformCollarTwoCutShapeEvidence :
    Prop :=
  ClosedCollarWindingFreedomWitnessRealizationData ∧
    closedCollarSimplePatchN6Slice800000_850000CyclicCutShapeCounts.cyclicCutFirstBlockerCount =
      128 ∧
    closedCollarSimplePatchN6Slice850000_900000CyclicCutShapeCounts.cyclicCutFirstBlockerCount =
      106 ∧
    closedCollarSimplePatchN6Slice900000_950000CyclicCutShapeCounts.cyclicCutFirstBlockerCount =
      54 ∧
    closedCollarSimplePatchN6Slice950000_1000000CyclicCutShapeCounts.cyclicCutFirstBlockerCount =
      128 ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutShapeCounts.internalVertexCount =
      6 ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutShapeCounts.patchStartIndex =
      800000 ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutShapeCounts.patchTopologyLimit =
      200000 ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutShapeCounts.sampledCyclicCutLimit =
      24 ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutShapeCounts.processedPatchTopologyCount =
      200000 ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutShapeCounts.radialOrderCaseCount =
      400000 ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutShapeCounts.profilePreservingCaseCount =
      2150 ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutShapeCounts.planarFirstBlockerCount =
      1734 ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutShapeCounts.cyclicCutFirstBlockerCount =
      416 ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutShapeCounts.firstCutSizeTwoCount =
      closedCollarSimplePatchN6Slices800000_1000000CyclicCutShapeCounts.cyclicCutFirstBlockerCount ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutShapeCounts.firstCutUsesTwoCollarEdgesCount =
      closedCollarSimplePatchN6Slices800000_1000000CyclicCutShapeCounts.cyclicCutFirstBlockerCount ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutShapeCounts.firstCutSideHasFourVerticesCount =
      closedCollarSimplePatchN6Slices800000_1000000CyclicCutShapeCounts.cyclicCutFirstBlockerCount ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutShapeCounts.firstCutSideHasTwoCollarAndTwoPatchInternalVerticesCount =
      closedCollarSimplePatchN6Slices800000_1000000CyclicCutShapeCounts.cyclicCutFirstBlockerCount ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutShapeCounts.planarFirstBlockerCount +
        closedCollarSimplePatchN6Slices800000_1000000CyclicCutShapeCounts.cyclicCutFirstBlockerCount =
      closedCollarSimplePatchN6Slices800000_1000000CyclicCutShapeCounts.profilePreservingCaseCount ∧
    closedCollarSimplePatchN6Slice800000_850000CyclicCutShapeCounts.cyclicCutFirstBlockerCount +
        closedCollarSimplePatchN6Slice850000_900000CyclicCutShapeCounts.cyclicCutFirstBlockerCount +
          closedCollarSimplePatchN6Slice900000_950000CyclicCutShapeCounts.cyclicCutFirstBlockerCount +
            closedCollarSimplePatchN6Slice950000_1000000CyclicCutShapeCounts.cyclicCutFirstBlockerCount =
      closedCollarSimplePatchN6Slices800000_1000000CyclicCutShapeCounts.cyclicCutFirstBlockerCount

theorem closedCollarWindingFreedomSimplePatchN6Slices800000_1000000UniformCollarTwoCutShapeEvidence :
    ClosedCollarWindingFreedomSimplePatchN6Slices800000_1000000UniformCollarTwoCutShapeEvidence := by
  refine
    ⟨closedCollarWindingFreedomWitnessRealizationData,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    decide

/--
Exact-template classifier for the first sampled cyclic-cut blockers in a
resumable simple-patch slice.  The two named templates are the two diagonal
collar two-poles seen by the lab; they refine the coarser "two collar edges
and a four-vertex side" shape.
-/
structure ClosedCollarSimplePatchCyclicCutExactTemplateCounts where
  internalVertexCount : Nat
  patchStartIndex : Nat
  patchTopologyLimit : Nat
  sampledCyclicCutLimit : Nat
  processedPatchTopologyCount : Nat
  radialOrderCaseCount : Nat
  profilePreservingCaseCount : Nat
  planarFirstBlockerCount : Nat
  cyclicCutFirstBlockerCount : Nat
  firstCutSizeTwoCount : Nat
  firstCutUsesTwoCollarEdgesCount : Nat
  firstCutSideHasFourVerticesCount : Nat
  firstCutSideHasTwoCollarAndTwoPatchInternalVerticesCount : Nat
  diagonalForwardCutEdges : List String
  diagonalForwardSideCollarVertices : List String
  diagonalForwardTemplateCount : Nat
  diagonalReverseCutEdges : List String
  diagonalReverseSideCollarVertices : List String
  diagonalReverseTemplateCount : Nat

def closedCollarSimplePatchN6Slices800000_1000000CyclicCutExactTemplateCounts :
    ClosedCollarSimplePatchCyclicCutExactTemplateCounts where
  internalVertexCount := 6
  patchStartIndex := 800000
  patchTopologyLimit := 200000
  sampledCyclicCutLimit := 24
  processedPatchTopologyCount := 200000
  radialOrderCaseCount := 400000
  profilePreservingCaseCount := 2150
  planarFirstBlockerCount := 1734
  cyclicCutFirstBlockerCount := 416
  firstCutSizeTwoCount := 416
  firstCutUsesTwoCollarEdgesCount := 416
  firstCutSideHasFourVerticesCount := 416
  firstCutSideHasTwoCollarAndTwoPatchInternalVerticesCount := 416
  diagonalForwardCutEdges := ["g0:F1F0", "g1:F4F5"]
  diagonalForwardSideCollarVertices := ["g0:F1", "g1:F5"]
  diagonalForwardTemplateCount := 216
  diagonalReverseCutEdges := ["g0:F4F5", "g1:F1F0"]
  diagonalReverseSideCollarVertices := ["g0:F5", "g1:F1"]
  diagonalReverseTemplateCount := 200

/--
Exact-template evidence for the 800000-1000000 six-internal simple-patch
window.  Every cyclic-cut blocker in the window has a first sampled cut of
size two and belongs to one of the two diagonal collar two-pole templates.
-/
def ClosedCollarWindingFreedomSimplePatchN6Slices800000_1000000ExactCollarTwoPoleTemplateEvidence :
    Prop :=
  ClosedCollarWindingFreedomWitnessRealizationData ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutExactTemplateCounts.internalVertexCount =
      6 ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutExactTemplateCounts.patchStartIndex =
      800000 ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutExactTemplateCounts.patchTopologyLimit =
      200000 ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutExactTemplateCounts.sampledCyclicCutLimit =
      24 ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutExactTemplateCounts.processedPatchTopologyCount =
      200000 ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutExactTemplateCounts.radialOrderCaseCount =
      400000 ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutExactTemplateCounts.profilePreservingCaseCount =
      2150 ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutExactTemplateCounts.planarFirstBlockerCount =
      1734 ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutExactTemplateCounts.cyclicCutFirstBlockerCount =
      416 ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutExactTemplateCounts.cyclicCutFirstBlockerCount =
      closedCollarSimplePatchN6Slices800000_1000000CyclicCutShapeCounts.cyclicCutFirstBlockerCount ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutExactTemplateCounts.firstCutSizeTwoCount =
      closedCollarSimplePatchN6Slices800000_1000000CyclicCutExactTemplateCounts.cyclicCutFirstBlockerCount ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutExactTemplateCounts.firstCutUsesTwoCollarEdgesCount =
      closedCollarSimplePatchN6Slices800000_1000000CyclicCutExactTemplateCounts.cyclicCutFirstBlockerCount ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutExactTemplateCounts.firstCutSideHasFourVerticesCount =
      closedCollarSimplePatchN6Slices800000_1000000CyclicCutExactTemplateCounts.cyclicCutFirstBlockerCount ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutExactTemplateCounts.firstCutSideHasTwoCollarAndTwoPatchInternalVerticesCount =
      closedCollarSimplePatchN6Slices800000_1000000CyclicCutExactTemplateCounts.cyclicCutFirstBlockerCount ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutExactTemplateCounts.diagonalForwardCutEdges =
      ["g0:F1F0", "g1:F4F5"] ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutExactTemplateCounts.diagonalForwardSideCollarVertices =
      ["g0:F1", "g1:F5"] ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutExactTemplateCounts.diagonalForwardTemplateCount =
      216 ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutExactTemplateCounts.diagonalReverseCutEdges =
      ["g0:F4F5", "g1:F1F0"] ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutExactTemplateCounts.diagonalReverseSideCollarVertices =
      ["g0:F5", "g1:F1"] ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutExactTemplateCounts.diagonalReverseTemplateCount =
      200 ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutExactTemplateCounts.diagonalForwardTemplateCount +
        closedCollarSimplePatchN6Slices800000_1000000CyclicCutExactTemplateCounts.diagonalReverseTemplateCount =
      closedCollarSimplePatchN6Slices800000_1000000CyclicCutExactTemplateCounts.cyclicCutFirstBlockerCount ∧
    closedCollarSimplePatchN6Slices800000_1000000CyclicCutExactTemplateCounts.planarFirstBlockerCount +
        closedCollarSimplePatchN6Slices800000_1000000CyclicCutExactTemplateCounts.cyclicCutFirstBlockerCount =
      closedCollarSimplePatchN6Slices800000_1000000CyclicCutExactTemplateCounts.profilePreservingCaseCount

theorem closedCollarWindingFreedomSimplePatchN6Slices800000_1000000ExactCollarTwoPoleTemplateEvidence :
    ClosedCollarWindingFreedomSimplePatchN6Slices800000_1000000ExactCollarTwoPoleTemplateEvidence := by
  refine
    ⟨closedCollarWindingFreedomWitnessRealizationData,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩ <;>
    decide

/-- The two exact diagonal collar two-pole templates isolated by the simple-patch lab. -/
inductive ClosedCollarDiagonalTwoPoleTemplateId where
  | forward
  | reverse
  deriving DecidableEq, Repr

def ClosedCollarDiagonalTwoPoleTemplateId.cutEdges :
    ClosedCollarDiagonalTwoPoleTemplateId → List String
  | forward => ["g0:F1F0", "g1:F4F5"]
  | reverse => ["g0:F4F5", "g1:F1F0"]

def ClosedCollarDiagonalTwoPoleTemplateId.sideCollarVertices :
    ClosedCollarDiagonalTwoPoleTemplateId → List String
  | forward => ["g0:F1", "g1:F5"]
  | reverse => ["g0:F5", "g1:F1"]

def ClosedCollarDiagonalTwoPoleTemplateId.countInN6Slices800000_1000000 :
    ClosedCollarDiagonalTwoPoleTemplateId → Nat
  | forward => 216
  | reverse => 200

def ClosedCollarDiagonalTwoPoleTemplateId.countInN6Slices800000_1200000 :
    ClosedCollarDiagonalTwoPoleTemplateId → Nat
  | forward => 432
  | reverse => 400

def ClosedCollarDiagonalTwoPoleTemplateId.countInN6Slices800000_1858980 :
    ClosedCollarDiagonalTwoPoleTemplateId → Nat
  | forward => 1080
  | reverse => 1080

/--
Graph-facing carrier for one of the exact diagonal collar two-pole templates.
The string labels pin the lab template, while `separator` is the reusable
normal-form interface: an exact realization would be a small cyclic separator
candidate in the ambient graph.
-/
structure ClosedCollarDiagonalTwoPoleTemplateCandidate
    (G : SimpleGraph V) where
  template : ClosedCollarDiagonalTwoPoleTemplateId
  separator : CyclicSeparatorCandidate G

def ClosedCollarDiagonalTwoPoleTemplateCandidate.cutEdges
    {G : SimpleGraph V} (candidate : ClosedCollarDiagonalTwoPoleTemplateCandidate G) :
    List String :=
  candidate.template.cutEdges

def ClosedCollarDiagonalTwoPoleTemplateCandidate.sideCollarVertices
    {G : SimpleGraph V} (candidate : ClosedCollarDiagonalTwoPoleTemplateCandidate G) :
    List String :=
  candidate.template.sideCollarVertices

def ClosedCollarDiagonalTwoPoleTemplateCandidate.Realizes
    {G : SimpleGraph V} (candidate : ClosedCollarDiagonalTwoPoleTemplateCandidate G) :
    Prop :=
  candidate.separator.Realizes

theorem ClosedCollarDiagonalTwoPoleTemplateCandidate.not_realizes_of_cyclicallyFiveEdgeConnected
    {G : SimpleGraph V} (candidate : ClosedCollarDiagonalTwoPoleTemplateCandidate G)
    (hcyclic : CyclicallyFiveEdgeConnected G) :
    ¬ candidate.Realizes :=
  candidate.separator.not_realizes_of_cyclicallyFiveEdgeConnected hcyclic

/--
Normal-form exclusion target for the exact diagonal collar two-pole templates:
in a cyclically five-edge-connected ambient graph, neither exact template can
be realized as the complete side-crossing support of its two-pole separator.
-/
def Section92WindingExactTemplateNormalFormExclusion : Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    ∀ candidate : ClosedCollarDiagonalTwoPoleTemplateCandidate G,
      CyclicallyFiveEdgeConnected G → ¬ candidate.Realizes

theorem section92WindingExactTemplateNormalFormExclusion :
    Section92WindingExactTemplateNormalFormExclusion := by
  intro V G candidate hcyclic
  exact candidate.not_realizes_of_cyclicallyFiveEdgeConnected hcyclic

/--
The missing geometric reduction needed to turn the finite simple-patch evidence
into a full normal-form nonrealizability theorem: every honest normal-form
annular realization of the winding-freedom witness must expose one of the exact
diagonal collar two-pole templates as a realized cyclic separator.
-/
def ClosedCollarWindingFreedomNormalFormRealizationForcesExactTemplate : Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    ClosedCollarWindingFreedomNormalFormRealization G →
      ∃ candidate : ClosedCollarDiagonalTwoPoleTemplateCandidate G,
        candidate.Realizes

/-- Full repair-side statement: the winding-freedom witness has no honest
normal-form annular realization. -/
def ClosedCollarWindingFreedomNonrealizableInNormalForm : Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    ClosedCollarWindingFreedomNormalFormRealization G → False

theorem closedCollarWindingFreedomNormalFormRealization_false_of_forcedTemplate
    {G : SimpleGraph V} (data : ClosedCollarWindingFreedomNormalFormRealization G)
    (candidate : ClosedCollarDiagonalTwoPoleTemplateCandidate G)
    (hrealizes : candidate.Realizes) :
    False :=
  (candidate.not_realizes_of_cyclicallyFiveEdgeConnected
    data.cyclicallyFiveEdgeConnected) hrealizes

theorem closedCollarWindingFreedomNonrealizableInNormalForm_of_forcesExactTemplate
    (hforces : ClosedCollarWindingFreedomNormalFormRealizationForcesExactTemplate) :
    ClosedCollarWindingFreedomNonrealizableInNormalForm := by
  intro V G data
  rcases hforces data with ⟨candidate, hrealizes⟩
  exact
    closedCollarWindingFreedomNormalFormRealization_false_of_forcedTemplate
      data candidate hrealizes

/--
Repaired Section 9.2 Step 4 target exposed by the winding work: residual
per-component winding freedom is killed by the minimal-counterexample
normal-form regime once the forced-template reduction is proved, not by
abstract boundary parity alone.
-/
def Section92Step4RepairedByNormalFormWindingTarget : Prop :=
  ClosedCollarWindingFreedomNormalFormRealizationForcesExactTemplate →
    ClosedCollarWindingFreedomNonrealizableInNormalForm

theorem section92Step4RepairedByNormalFormWindingTarget :
    Section92Step4RepairedByNormalFormWindingTarget :=
  closedCollarWindingFreedomNonrealizableInNormalForm_of_forcesExactTemplate

/--
The current formally supported S4 repair fork.  The lab has narrowed the
surviving six-internal simple-patch blockers to the two exact diagonal collar
two-pole templates, and the graph normal-form API excludes any exact realization
of those templates under cyclic five-edge-connectivity.
-/
def ClosedCollarWindingFreedomExactTemplatesBlockedByCyclicallyFiveNormalForm :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6Slices800000_1000000ExactCollarTwoPoleTemplateEvidence ∧
    Section92WindingExactTemplateNormalFormExclusion

theorem closedCollarWindingFreedomExactTemplatesBlockedByCyclicallyFiveNormalForm :
    ClosedCollarWindingFreedomExactTemplatesBlockedByCyclicallyFiveNormalForm := by
  exact
    ⟨closedCollarWindingFreedomSimplePatchN6Slices800000_1000000ExactCollarTwoPoleTemplateEvidence,
      section92WindingExactTemplateNormalFormExclusion⟩

/--
Template-blocker counts for a resumable simple-patch slice after applying the
normal-form exclusion of the two exact diagonal collar two-poles.  Structural
first blockers are the ordinary connected/cubic/bridgeless/planar/simple
prefix tests; exact-template blockers are cyclic-cut blockers whose explicit
two-pole template is excluded by cyclic five-edge-connectivity.
-/
structure ClosedCollarSimplePatchTemplateBlockerSliceCounts where
  internalVertexCount : Nat
  patchStartIndex : Nat
  patchTopologyLimit : Nat
  processedPatchTopologyCount : Nat
  radialOrderCaseCount : Nat
  profilePreservingCaseCount : Nat
  structuralFirstBlockerCount : Nat
  exactTemplateBlockerCount : Nat
  diagonalForwardTemplateCount : Nat
  diagonalReverseTemplateCount : Nat
  nonTemplateCyclicCutBlockerCount : Nat
  cap5LikeBlockerCount : Nat
  normalFormAfterTemplateExclusionPassingCount : Nat

def closedCollarSimplePatchN6ExactPatchTopologyCount : Nat :=
  1858980

def closedCollarSimplePatchN6First800000StructuralCounts :
    ClosedCollarSimplePatchTemplateBlockerSliceCounts where
  internalVertexCount := 6
  patchStartIndex := 0
  patchTopologyLimit := 800000
  processedPatchTopologyCount := 800000
  radialOrderCaseCount := 1600000
  profilePreservingCaseCount := 18720
  structuralFirstBlockerCount := 18720
  exactTemplateBlockerCount := 0
  diagonalForwardTemplateCount := 0
  diagonalReverseTemplateCount := 0
  nonTemplateCyclicCutBlockerCount := 0
  cap5LikeBlockerCount := 0
  normalFormAfterTemplateExclusionPassingCount := 0

def closedCollarSimplePatchN6Slices800000_1000000TemplateBlockerCounts :
    ClosedCollarSimplePatchTemplateBlockerSliceCounts where
  internalVertexCount := 6
  patchStartIndex := 800000
  patchTopologyLimit := 200000
  processedPatchTopologyCount := 200000
  radialOrderCaseCount := 400000
  profilePreservingCaseCount := 2150
  structuralFirstBlockerCount := 1734
  exactTemplateBlockerCount := 416
  diagonalForwardTemplateCount := 216
  diagonalReverseTemplateCount := 200
  nonTemplateCyclicCutBlockerCount := 0
  cap5LikeBlockerCount := 0
  normalFormAfterTemplateExclusionPassingCount := 0

def closedCollarSimplePatchN6Slices1000000_1200000TemplateBlockerCounts :
    ClosedCollarSimplePatchTemplateBlockerSliceCounts where
  internalVertexCount := 6
  patchStartIndex := 1000000
  patchTopologyLimit := 200000
  processedPatchTopologyCount := 200000
  radialOrderCaseCount := 400000
  profilePreservingCaseCount := 2084
  structuralFirstBlockerCount := 1668
  exactTemplateBlockerCount := 416
  diagonalForwardTemplateCount := 216
  diagonalReverseTemplateCount := 200
  nonTemplateCyclicCutBlockerCount := 0
  cap5LikeBlockerCount := 0
  normalFormAfterTemplateExclusionPassingCount := 0

def closedCollarSimplePatchN6Slices800000_1200000TemplateBlockerCounts :
    ClosedCollarSimplePatchTemplateBlockerSliceCounts where
  internalVertexCount := 6
  patchStartIndex := 800000
  patchTopologyLimit := 400000
  processedPatchTopologyCount := 400000
  radialOrderCaseCount := 800000
  profilePreservingCaseCount := 4234
  structuralFirstBlockerCount := 3402
  exactTemplateBlockerCount := 832
  diagonalForwardTemplateCount := 432
  diagonalReverseTemplateCount := 400
  nonTemplateCyclicCutBlockerCount := 0
  cap5LikeBlockerCount := 0
  normalFormAfterTemplateExclusionPassingCount := 0

def closedCollarSimplePatchN6Slices1200000_1400000TemplateBlockerCounts :
    ClosedCollarSimplePatchTemplateBlockerSliceCounts where
  internalVertexCount := 6
  patchStartIndex := 1200000
  patchTopologyLimit := 200000
  processedPatchTopologyCount := 200000
  radialOrderCaseCount := 400000
  profilePreservingCaseCount := 1832
  structuralFirstBlockerCount := 1498
  exactTemplateBlockerCount := 334
  diagonalForwardTemplateCount := 144
  diagonalReverseTemplateCount := 190
  nonTemplateCyclicCutBlockerCount := 0
  cap5LikeBlockerCount := 0
  normalFormAfterTemplateExclusionPassingCount := 0

def closedCollarSimplePatchN6Slices1400000_1600000TemplateBlockerCounts :
    ClosedCollarSimplePatchTemplateBlockerSliceCounts where
  internalVertexCount := 6
  patchStartIndex := 1400000
  patchTopologyLimit := 200000
  processedPatchTopologyCount := 200000
  radialOrderCaseCount := 400000
  profilePreservingCaseCount := 2118
  structuralFirstBlockerCount := 1700
  exactTemplateBlockerCount := 418
  diagonalForwardTemplateCount := 216
  diagonalReverseTemplateCount := 202
  nonTemplateCyclicCutBlockerCount := 0
  cap5LikeBlockerCount := 0
  normalFormAfterTemplateExclusionPassingCount := 0

def closedCollarSimplePatchN6Slices1600000_1858980TemplateBlockerCounts :
    ClosedCollarSimplePatchTemplateBlockerSliceCounts where
  internalVertexCount := 6
  patchStartIndex := 1600000
  patchTopologyLimit := 400000
  processedPatchTopologyCount := 258980
  radialOrderCaseCount := 517960
  profilePreservingCaseCount := 2976
  structuralFirstBlockerCount := 2400
  exactTemplateBlockerCount := 576
  diagonalForwardTemplateCount := 288
  diagonalReverseTemplateCount := 288
  nonTemplateCyclicCutBlockerCount := 0
  cap5LikeBlockerCount := 0
  normalFormAfterTemplateExclusionPassingCount := 0

def closedCollarSimplePatchN6Slices800000_1858980TemplateBlockerCounts :
    ClosedCollarSimplePatchTemplateBlockerSliceCounts where
  internalVertexCount := 6
  patchStartIndex := 800000
  patchTopologyLimit := 1058980
  processedPatchTopologyCount := 1058980
  radialOrderCaseCount := 2117960
  profilePreservingCaseCount := 11160
  structuralFirstBlockerCount := 9000
  exactTemplateBlockerCount := 2160
  diagonalForwardTemplateCount := 1080
  diagonalReverseTemplateCount := 1080
  nonTemplateCyclicCutBlockerCount := 0
  cap5LikeBlockerCount := 0
  normalFormAfterTemplateExclusionPassingCount := 0

def closedCollarSimplePatchN6AllTemplateBlockerCounts :
    ClosedCollarSimplePatchTemplateBlockerSliceCounts where
  internalVertexCount := 6
  patchStartIndex := 0
  patchTopologyLimit := 1858980
  processedPatchTopologyCount := 1858980
  radialOrderCaseCount := 3717960
  profilePreservingCaseCount := 29880
  structuralFirstBlockerCount := 27720
  exactTemplateBlockerCount := 2160
  diagonalForwardTemplateCount := 1080
  diagonalReverseTemplateCount := 1080
  nonTemplateCyclicCutBlockerCount := 0
  cap5LikeBlockerCount := 0
  normalFormAfterTemplateExclusionPassingCount := 0

/--
Template-exclusion evidence through the 800000-1200000 six-internal
simple-patch window.  After direct search for the two exact diagonal templates,
every profile-preserving case is blocked either structurally or by one of the
two templates already excluded by cyclic five-edge-connectivity; no residual
non-template small cyclic cut, CAP5-like blocker, or template-exclusion pass is
seen in these slices.
-/
def ClosedCollarWindingFreedomSimplePatchN6Slices800000_1200000BlockedByStructuralOrExcludedTemplateEvidence :
    Prop :=
  ClosedCollarWindingFreedomWitnessRealizationData ∧
    closedCollarSimplePatchN6Slices800000_1200000TemplateBlockerCounts.internalVertexCount =
      6 ∧
    closedCollarSimplePatchN6Slices800000_1200000TemplateBlockerCounts.patchStartIndex =
      800000 ∧
    closedCollarSimplePatchN6Slices800000_1200000TemplateBlockerCounts.patchTopologyLimit =
      400000 ∧
    closedCollarSimplePatchN6Slices800000_1200000TemplateBlockerCounts.processedPatchTopologyCount =
      400000 ∧
    closedCollarSimplePatchN6Slices800000_1200000TemplateBlockerCounts.radialOrderCaseCount =
      800000 ∧
    closedCollarSimplePatchN6Slices800000_1200000TemplateBlockerCounts.profilePreservingCaseCount =
      4234 ∧
    closedCollarSimplePatchN6Slices800000_1200000TemplateBlockerCounts.structuralFirstBlockerCount =
      3402 ∧
    closedCollarSimplePatchN6Slices800000_1200000TemplateBlockerCounts.exactTemplateBlockerCount =
      832 ∧
    closedCollarSimplePatchN6Slices800000_1200000TemplateBlockerCounts.diagonalForwardTemplateCount =
      432 ∧
    closedCollarSimplePatchN6Slices800000_1200000TemplateBlockerCounts.diagonalReverseTemplateCount =
      400 ∧
    closedCollarSimplePatchN6Slices800000_1200000TemplateBlockerCounts.nonTemplateCyclicCutBlockerCount =
      0 ∧
    closedCollarSimplePatchN6Slices800000_1200000TemplateBlockerCounts.cap5LikeBlockerCount =
      0 ∧
    closedCollarSimplePatchN6Slices800000_1200000TemplateBlockerCounts.normalFormAfterTemplateExclusionPassingCount =
      0 ∧
    closedCollarSimplePatchN6Slices800000_1200000TemplateBlockerCounts.diagonalForwardTemplateCount =
      ClosedCollarDiagonalTwoPoleTemplateId.countInN6Slices800000_1200000
        ClosedCollarDiagonalTwoPoleTemplateId.forward ∧
    closedCollarSimplePatchN6Slices800000_1200000TemplateBlockerCounts.diagonalReverseTemplateCount =
      ClosedCollarDiagonalTwoPoleTemplateId.countInN6Slices800000_1200000
        ClosedCollarDiagonalTwoPoleTemplateId.reverse ∧
    closedCollarSimplePatchN6Slices800000_1200000TemplateBlockerCounts.diagonalForwardTemplateCount +
        closedCollarSimplePatchN6Slices800000_1200000TemplateBlockerCounts.diagonalReverseTemplateCount =
      closedCollarSimplePatchN6Slices800000_1200000TemplateBlockerCounts.exactTemplateBlockerCount ∧
    closedCollarSimplePatchN6Slices800000_1200000TemplateBlockerCounts.structuralFirstBlockerCount +
        closedCollarSimplePatchN6Slices800000_1200000TemplateBlockerCounts.exactTemplateBlockerCount =
      closedCollarSimplePatchN6Slices800000_1200000TemplateBlockerCounts.profilePreservingCaseCount

theorem closedCollarWindingFreedomSimplePatchN6Slices800000_1200000BlockedByStructuralOrExcludedTemplateEvidence :
    ClosedCollarWindingFreedomSimplePatchN6Slices800000_1200000BlockedByStructuralOrExcludedTemplateEvidence := by
  refine
    ⟨closedCollarWindingFreedomWitnessRealizationData,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    decide

/--
Combined current fork statement for the six-internal realization lab: in the
400000-case 800000-1200000 window, all profile-preserving candidates are
blocked structurally or by exact diagonal templates, and the exact templates
are excluded by cyclic five-edge-connectivity.
-/
def ClosedCollarWindingFreedomSimplePatchN6Slices800000_1200000BlockedAfterCyclicallyFiveTemplateExclusion :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6Slices800000_1200000BlockedByStructuralOrExcludedTemplateEvidence ∧
    Section92WindingExactTemplateNormalFormExclusion

theorem closedCollarWindingFreedomSimplePatchN6Slices800000_1200000BlockedAfterCyclicallyFiveTemplateExclusion :
    ClosedCollarWindingFreedomSimplePatchN6Slices800000_1200000BlockedAfterCyclicallyFiveTemplateExclusion := by
  exact
    ⟨closedCollarWindingFreedomSimplePatchN6Slices800000_1200000BlockedByStructuralOrExcludedTemplateEvidence,
      section92WindingExactTemplateNormalFormExclusion⟩

/--
Exhaustive six-internal simple-patch evidence.  The lab enumerated all
1858980 simple cubic four-terminal patch topologies, tested both radial
orders, required preservation of the full closed-collar winding profile, and
then classified every profile-preserving candidate.  All such candidates are
accounted for by structural normal-form blockers or by one of the two exact
diagonal collar two-pole templates; no residual non-template small cyclic cut,
literal CAP5 blocker, or post-template-exclusion pass remains.
-/
def ClosedCollarWindingFreedomSimplePatchN6ExhaustiveBlockedByStructuralOrExcludedTemplateEvidence :
    Prop :=
  ClosedCollarWindingFreedomWitnessRealizationData ∧
    closedCollarSimplePatchN6ExactPatchTopologyCount = 1858980 ∧
    closedCollarSimplePatchN6AllTemplateBlockerCounts.internalVertexCount = 6 ∧
    closedCollarSimplePatchN6AllTemplateBlockerCounts.patchStartIndex = 0 ∧
    closedCollarSimplePatchN6AllTemplateBlockerCounts.patchTopologyLimit =
      closedCollarSimplePatchN6ExactPatchTopologyCount ∧
    closedCollarSimplePatchN6AllTemplateBlockerCounts.processedPatchTopologyCount =
      closedCollarSimplePatchN6ExactPatchTopologyCount ∧
    closedCollarSimplePatchN6AllTemplateBlockerCounts.radialOrderCaseCount =
      2 * closedCollarSimplePatchN6ExactPatchTopologyCount ∧
    closedCollarSimplePatchN6AllTemplateBlockerCounts.profilePreservingCaseCount =
      29880 ∧
    closedCollarSimplePatchN6AllTemplateBlockerCounts.structuralFirstBlockerCount =
      27720 ∧
    closedCollarSimplePatchN6AllTemplateBlockerCounts.exactTemplateBlockerCount =
      2160 ∧
    closedCollarSimplePatchN6AllTemplateBlockerCounts.diagonalForwardTemplateCount =
      1080 ∧
    closedCollarSimplePatchN6AllTemplateBlockerCounts.diagonalReverseTemplateCount =
      1080 ∧
    closedCollarSimplePatchN6AllTemplateBlockerCounts.nonTemplateCyclicCutBlockerCount =
      0 ∧
    closedCollarSimplePatchN6AllTemplateBlockerCounts.cap5LikeBlockerCount =
      0 ∧
    closedCollarSimplePatchN6AllTemplateBlockerCounts.normalFormAfterTemplateExclusionPassingCount =
      0 ∧
    closedCollarSimplePatchN6AllTemplateBlockerCounts.diagonalForwardTemplateCount =
      ClosedCollarDiagonalTwoPoleTemplateId.countInN6Slices800000_1858980
        ClosedCollarDiagonalTwoPoleTemplateId.forward ∧
    closedCollarSimplePatchN6AllTemplateBlockerCounts.diagonalReverseTemplateCount =
      ClosedCollarDiagonalTwoPoleTemplateId.countInN6Slices800000_1858980
        ClosedCollarDiagonalTwoPoleTemplateId.reverse ∧
    closedCollarSimplePatchN6AllTemplateBlockerCounts.diagonalForwardTemplateCount +
        closedCollarSimplePatchN6AllTemplateBlockerCounts.diagonalReverseTemplateCount =
      closedCollarSimplePatchN6AllTemplateBlockerCounts.exactTemplateBlockerCount ∧
    closedCollarSimplePatchN6AllTemplateBlockerCounts.structuralFirstBlockerCount +
        closedCollarSimplePatchN6AllTemplateBlockerCounts.exactTemplateBlockerCount +
          closedCollarSimplePatchN6AllTemplateBlockerCounts.nonTemplateCyclicCutBlockerCount +
            closedCollarSimplePatchN6AllTemplateBlockerCounts.cap5LikeBlockerCount +
              closedCollarSimplePatchN6AllTemplateBlockerCounts.normalFormAfterTemplateExclusionPassingCount =
      closedCollarSimplePatchN6AllTemplateBlockerCounts.profilePreservingCaseCount ∧
    closedCollarSimplePatchN6First800000StructuralCounts.processedPatchTopologyCount +
        closedCollarSimplePatchN6Slices800000_1858980TemplateBlockerCounts.processedPatchTopologyCount =
      closedCollarSimplePatchN6AllTemplateBlockerCounts.processedPatchTopologyCount ∧
    closedCollarSimplePatchN6First800000StructuralCounts.profilePreservingCaseCount +
        closedCollarSimplePatchN6Slices800000_1858980TemplateBlockerCounts.profilePreservingCaseCount =
      closedCollarSimplePatchN6AllTemplateBlockerCounts.profilePreservingCaseCount ∧
    closedCollarSimplePatchN6Slices800000_1200000TemplateBlockerCounts.processedPatchTopologyCount +
        closedCollarSimplePatchN6Slices1200000_1400000TemplateBlockerCounts.processedPatchTopologyCount +
          closedCollarSimplePatchN6Slices1400000_1600000TemplateBlockerCounts.processedPatchTopologyCount +
            closedCollarSimplePatchN6Slices1600000_1858980TemplateBlockerCounts.processedPatchTopologyCount =
      closedCollarSimplePatchN6Slices800000_1858980TemplateBlockerCounts.processedPatchTopologyCount ∧
    closedCollarSimplePatchN6Slices800000_1200000TemplateBlockerCounts.exactTemplateBlockerCount +
        closedCollarSimplePatchN6Slices1200000_1400000TemplateBlockerCounts.exactTemplateBlockerCount +
          closedCollarSimplePatchN6Slices1400000_1600000TemplateBlockerCounts.exactTemplateBlockerCount +
            closedCollarSimplePatchN6Slices1600000_1858980TemplateBlockerCounts.exactTemplateBlockerCount =
      closedCollarSimplePatchN6Slices800000_1858980TemplateBlockerCounts.exactTemplateBlockerCount

theorem closedCollarWindingFreedomSimplePatchN6ExhaustiveBlockedByStructuralOrExcludedTemplateEvidence :
    ClosedCollarWindingFreedomSimplePatchN6ExhaustiveBlockedByStructuralOrExcludedTemplateEvidence := by
  refine ⟨closedCollarWindingFreedomWitnessRealizationData, ?_⟩
  decide

/--
Exhaustive current fork statement for the six-internal realization lab.  Every
profile-preserving simple-patch candidate is structurally blocked or realizes
one of the exact diagonal templates, and cyclic five-edge-connectivity excludes
those templates from the intended normal-form regime.
-/
def ClosedCollarWindingFreedomSimplePatchN6ExhaustiveBlockedAfterCyclicallyFiveTemplateExclusion :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6ExhaustiveBlockedByStructuralOrExcludedTemplateEvidence ∧
    Section92WindingExactTemplateNormalFormExclusion

theorem closedCollarWindingFreedomSimplePatchN6ExhaustiveBlockedAfterCyclicallyFiveTemplateExclusion :
    ClosedCollarWindingFreedomSimplePatchN6ExhaustiveBlockedAfterCyclicallyFiveTemplateExclusion := by
  exact
    ⟨closedCollarWindingFreedomSimplePatchN6ExhaustiveBlockedByStructuralOrExcludedTemplateEvidence,
      section92WindingExactTemplateNormalFormExclusion⟩

/--
Graph-facing hook for the finite six-internal simple-patch subclass tested by
the realization lab.  The index fields identify the enumerated patch topology
and one of the two radial orders; the annular realization supplies the actual
geometric data being represented.
-/
structure ClosedCollarWindingFreedomSimplePatchN6Representation
    (G : SimpleGraph V) where
  annular : ClosedCollarWindingFreedomAnnularRealization G
  patchTopologyIndex : Nat
  hpatchTopologyIndex_lt :
    patchTopologyIndex < closedCollarSimplePatchN6ExactPatchTopologyCount
  radialOrderIndex : Fin 2

/--
A normal-form realization that survives the exhausted six-internal
simple-patch lab as a post-template-exclusion pass.  The final field is the
finite lab certificate that such a pass was counted.
-/
structure ClosedCollarWindingFreedomSimplePatchN6LabNormalFormPass
    (G : SimpleGraph V) where
  normalForm : ClosedCollarWindingFreedomNormalFormRealization G
  representation : ClosedCollarWindingFreedomSimplePatchN6Representation G
  hpassCountPositive :
    0 <
      closedCollarSimplePatchN6AllTemplateBlockerCounts.normalFormAfterTemplateExclusionPassingCount

/--
Coverage obligation for the finite n6 subclass: if an honest normal-form
annular realization is represented by one of the enumerated six-internal
simple patches, then the lab's profile-preservation and normal-form-prefix
checks count it as a surviving pass.
-/
def ClosedCollarWindingFreedomSimplePatchN6CoveredByLab : Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    ClosedCollarWindingFreedomNormalFormRealization G →
      ClosedCollarWindingFreedomSimplePatchN6Representation G →
        Nonempty (ClosedCollarWindingFreedomSimplePatchN6LabNormalFormPass G)

theorem closedCollarWindingFreedomSimplePatchN6_noLabNormalFormPass
    {G : SimpleGraph V}
    (data : ClosedCollarWindingFreedomSimplePatchN6LabNormalFormPass G) :
    False := by
  have hzero :
      closedCollarSimplePatchN6AllTemplateBlockerCounts.normalFormAfterTemplateExclusionPassingCount =
        0 := rfl
  have hpos := data.hpassCountPositive
  omega

/--
Finite subclass nonrealizability: once the lab-coverage obligation is supplied,
no honest normal-form realization represented by an enumerated six-internal
simple patch can exist.
-/
def ClosedCollarWindingFreedomSimplePatchN6NonrealizableInNormalForm : Prop :=
  ClosedCollarWindingFreedomSimplePatchN6CoveredByLab →
    ∀ {V : Type} {G : SimpleGraph V},
      ClosedCollarWindingFreedomNormalFormRealization G →
        ClosedCollarWindingFreedomSimplePatchN6Representation G → False

theorem closedCollarWindingFreedomSimplePatchN6NonrealizableInNormalForm :
    ClosedCollarWindingFreedomSimplePatchN6NonrealizableInNormalForm := by
  intro hcovered V G normalForm representation
  rcases hcovered normalForm representation with ⟨labPass⟩
  exact
    closedCollarWindingFreedomSimplePatchN6_noLabNormalFormPass
      labPass

/--
Representative planar profile-preserving samples from the six-internal
simple-patch search.  These are not exhaustive certificates; they pin the first
normal-form blocker after planarity has been passed.
-/
structure ClosedCollarSimplePatchPlanarCyclicCutSample where
  patchIndex : Nat
  radialOrderAFirst : Bool
  profilePreservingStateCount : Nat
  vertexCount : Nat
  edgeCount : Nat
  passedConnectedMultigraph : Bool
  passedCubicMultigraph : Bool
  passedBridgelessMultigraph : Bool
  passedPlanarMultigraph : Bool
  passedSimpleEndpointRealization : Bool
  firstFailedByCyclicEdgeCutLe4 : Bool
  minimumSmallCyclicCutSize : Nat
  sampledSmallCyclicCutCount : Nat
  firstCutSize : Nat
  firstCutEdges : List String
  firstCutSideVertices : List String

def closedCollarSimplePatchN6PlanarSizeTwoCyclicCutSample :
    ClosedCollarSimplePatchPlanarCyclicCutSample where
  patchIndex := 821205
  radialOrderAFirst := true
  profilePreservingStateCount := 6
  vertexCount := 18
  edgeCount := 27
  passedConnectedMultigraph := true
  passedCubicMultigraph := true
  passedBridgelessMultigraph := true
  passedPlanarMultigraph := true
  passedSimpleEndpointRealization := true
  firstFailedByCyclicEdgeCutLe4 := true
  minimumSmallCyclicCutSize := 2
  sampledSmallCyclicCutCount := 12
  firstCutSize := 2
  firstCutEdges := ["g0:F1F0", "g1:F4F5"]
  firstCutSideVertices := ["N0", "N1", "g0:F1", "g1:F5"]

def closedCollarSimplePatchN6PlanarSizeThreeCyclicCutSample :
    ClosedCollarSimplePatchPlanarCyclicCutSample where
  patchIndex := 852969
  radialOrderAFirst := true
  profilePreservingStateCount := 6
  vertexCount := 18
  edgeCount := 27
  passedConnectedMultigraph := true
  passedCubicMultigraph := true
  passedBridgelessMultigraph := true
  passedPlanarMultigraph := true
  passedSimpleEndpointRealization := true
  firstFailedByCyclicEdgeCutLe4 := true
  minimumSmallCyclicCutSize := 3
  sampledSmallCyclicCutCount := 12
  firstCutSize := 3
  firstCutEdges := ["g1:F4F5", "P9:N0-N2", "P10:N1-N5"]
  firstCutSideVertices := ["N0", "N1", "g1:F5"]

/--
Named evidence that the first six-internal planar profile-preserving samples
seen by the lab are not planarity failures.  They pass the tested connected,
cubic, bridgeless, planar, and simple-endpoint checks, then fail at the
no-small-cyclic-cut normal-form condition.
-/
def ClosedCollarWindingFreedomSimplePatchN6PlanarCyclicCutSamplesEvidence :
    Prop :=
  ClosedCollarWindingFreedomWitnessRealizationData ∧
    closedCollarSimplePatchN6PlanarSizeTwoCyclicCutSample.patchIndex = 821205 ∧
    closedCollarSimplePatchN6PlanarSizeTwoCyclicCutSample.profilePreservingStateCount = 6 ∧
    closedCollarSimplePatchN6PlanarSizeTwoCyclicCutSample.passedConnectedMultigraph = true ∧
    closedCollarSimplePatchN6PlanarSizeTwoCyclicCutSample.passedCubicMultigraph = true ∧
    closedCollarSimplePatchN6PlanarSizeTwoCyclicCutSample.passedBridgelessMultigraph = true ∧
    closedCollarSimplePatchN6PlanarSizeTwoCyclicCutSample.passedPlanarMultigraph = true ∧
    closedCollarSimplePatchN6PlanarSizeTwoCyclicCutSample.passedSimpleEndpointRealization = true ∧
    closedCollarSimplePatchN6PlanarSizeTwoCyclicCutSample.firstFailedByCyclicEdgeCutLe4 = true ∧
    closedCollarSimplePatchN6PlanarSizeTwoCyclicCutSample.minimumSmallCyclicCutSize = 2 ∧
    closedCollarSimplePatchN6PlanarSizeTwoCyclicCutSample.firstCutSize = 2 ∧
    closedCollarSimplePatchN6PlanarSizeTwoCyclicCutSample.firstCutEdges =
      ["g0:F1F0", "g1:F4F5"] ∧
    closedCollarSimplePatchN6PlanarSizeTwoCyclicCutSample.firstCutSideVertices =
      ["N0", "N1", "g0:F1", "g1:F5"] ∧
    closedCollarSimplePatchN6PlanarSizeThreeCyclicCutSample.patchIndex = 852969 ∧
    closedCollarSimplePatchN6PlanarSizeThreeCyclicCutSample.profilePreservingStateCount = 6 ∧
    closedCollarSimplePatchN6PlanarSizeThreeCyclicCutSample.passedConnectedMultigraph = true ∧
    closedCollarSimplePatchN6PlanarSizeThreeCyclicCutSample.passedCubicMultigraph = true ∧
    closedCollarSimplePatchN6PlanarSizeThreeCyclicCutSample.passedBridgelessMultigraph = true ∧
    closedCollarSimplePatchN6PlanarSizeThreeCyclicCutSample.passedPlanarMultigraph = true ∧
    closedCollarSimplePatchN6PlanarSizeThreeCyclicCutSample.passedSimpleEndpointRealization = true ∧
    closedCollarSimplePatchN6PlanarSizeThreeCyclicCutSample.firstFailedByCyclicEdgeCutLe4 = true ∧
    closedCollarSimplePatchN6PlanarSizeThreeCyclicCutSample.minimumSmallCyclicCutSize = 3 ∧
    closedCollarSimplePatchN6PlanarSizeThreeCyclicCutSample.firstCutSize = 3 ∧
    closedCollarSimplePatchN6PlanarSizeThreeCyclicCutSample.firstCutEdges =
      ["g1:F4F5", "P9:N0-N2", "P10:N1-N5"] ∧
    closedCollarSimplePatchN6PlanarSizeThreeCyclicCutSample.firstCutSideVertices =
      ["N0", "N1", "g1:F5"]

theorem closedCollarWindingFreedomSimplePatchN6PlanarCyclicCutSamplesEvidence :
    ClosedCollarWindingFreedomSimplePatchN6PlanarCyclicCutSamplesEvidence := by
  refine
    ⟨closedCollarWindingFreedomWitnessRealizationData,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end GoertzelLemma818ClosedCollarWindingRealization

end Mettapedia.GraphTheory.FourColor
