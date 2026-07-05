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
Interface for the face created by cutting an annular collar open along a radial
arc.  A genuine embedded realization must supply an actual cut-open collar
face; this record keeps that geometric obligation explicit instead of folding
it into a numerical lab verdict.
-/
structure ClosedCollarCutOpenRadialFace
    {G : SimpleGraph V}
    (annular : ClosedCollarWindingFreedomAnnularRealization G) where
  faceEdges : Finset G.edgeSet
  isCutOpenCollarFace : Prop
  hface : isCutOpenCollarFace
  radialCut_subset_faceEdges : annular.radialCut ⊆ faceEdges

/--
Radial-face coherence for a cut-open annular realization: all radial-cut edges
are incident with one cut-open collar face.
-/
def ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
    {G : SimpleGraph V}
    (annular : ClosedCollarWindingFreedomAnnularRealization G) : Prop :=
  Nonempty (ClosedCollarCutOpenRadialFace annular)

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
Normal-form realization together with the specific radial-face coherence datum
needed to compare the embedded annulus with the cut-open rotation-system lab.
-/
structure ClosedCollarWindingFreedomNormalFormRadialFaceRealization
    (G : SimpleGraph V) where
  normalForm : ClosedCollarWindingFreedomNormalFormRealization G
  radialFace : ClosedCollarCutOpenRadialFace normalForm.annular

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

structure ClosedCollarSimplePatchTemplateBlockerIndexSampleCounts where
  internalVertexCount : Nat
  exactPatchTopologyCount : Nat
  sampledPatchTopologyCount : Nat
  radialOrderCaseCount : Nat
  profilePreservingCaseCount : Nat
  structuralFirstBlockerCount : Nat
  exactTemplateBlockerCount : Nat
  nonTemplateCyclicCutBlockerCount : Nat
  cap5LikeBlockerCount : Nat
  normalFormAfterTemplateExclusionPassingCount : Nat

structure ClosedCollarSimplePatchTemplateBlockerArchiveCounts where
  internalVertexCount : Nat
  archivedSliceFileCount : Nat
  archivedPatchStartIndex : Nat
  archivedPatchEndIndex : Nat
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

def closedCollarSimplePatchN8ExactPatchTopologyCount : Nat :=
  1189087725

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

def closedCollarSimplePatchN8First1000000TemplateBlockerCounts :
    ClosedCollarSimplePatchTemplateBlockerSliceCounts where
  internalVertexCount := 8
  patchStartIndex := 0
  patchTopologyLimit := 1000000
  processedPatchTopologyCount := 1000000
  radialOrderCaseCount := 2000000
  profilePreservingCaseCount := 0
  structuralFirstBlockerCount := 0
  exactTemplateBlockerCount := 0
  diagonalForwardTemplateCount := 0
  diagonalReverseTemplateCount := 0
  nonTemplateCyclicCutBlockerCount := 0
  cap5LikeBlockerCount := 0
  normalFormAfterTemplateExclusionPassingCount := 0

def closedCollarSimplePatchN8Slices1000000_1500000TemplateBlockerCounts :
    ClosedCollarSimplePatchTemplateBlockerSliceCounts where
  internalVertexCount := 8
  patchStartIndex := 1000000
  patchTopologyLimit := 500000
  processedPatchTopologyCount := 500000
  radialOrderCaseCount := 1000000
  profilePreservingCaseCount := 0
  structuralFirstBlockerCount := 0
  exactTemplateBlockerCount := 0
  diagonalForwardTemplateCount := 0
  diagonalReverseTemplateCount := 0
  nonTemplateCyclicCutBlockerCount := 0
  cap5LikeBlockerCount := 0
  normalFormAfterTemplateExclusionPassingCount := 0

def closedCollarSimplePatchN8Slices1500000_2000000TemplateBlockerCounts :
    ClosedCollarSimplePatchTemplateBlockerSliceCounts where
  internalVertexCount := 8
  patchStartIndex := 1500000
  patchTopologyLimit := 500000
  processedPatchTopologyCount := 500000
  radialOrderCaseCount := 1000000
  profilePreservingCaseCount := 0
  structuralFirstBlockerCount := 0
  exactTemplateBlockerCount := 0
  diagonalForwardTemplateCount := 0
  diagonalReverseTemplateCount := 0
  nonTemplateCyclicCutBlockerCount := 0
  cap5LikeBlockerCount := 0
  normalFormAfterTemplateExclusionPassingCount := 0

def closedCollarSimplePatchN8First2000000TemplateBlockerCounts :
    ClosedCollarSimplePatchTemplateBlockerSliceCounts where
  internalVertexCount := 8
  patchStartIndex := 0
  patchTopologyLimit := 2000000
  processedPatchTopologyCount := 2000000
  radialOrderCaseCount := 4000000
  profilePreservingCaseCount := 0
  structuralFirstBlockerCount := 0
  exactTemplateBlockerCount := 0
  diagonalForwardTemplateCount := 0
  diagonalReverseTemplateCount := 0
  nonTemplateCyclicCutBlockerCount := 0
  cap5LikeBlockerCount := 0
  normalFormAfterTemplateExclusionPassingCount := 0

def closedCollarSimplePatchN8Stratified33TemplateBlockerIndexSampleCounts :
    ClosedCollarSimplePatchTemplateBlockerIndexSampleCounts where
  internalVertexCount := 8
  exactPatchTopologyCount := 1189087725
  sampledPatchTopologyCount := 33
  radialOrderCaseCount := 66
  profilePreservingCaseCount := 0
  structuralFirstBlockerCount := 0
  exactTemplateBlockerCount := 0
  nonTemplateCyclicCutBlockerCount := 0
  cap5LikeBlockerCount := 0
  normalFormAfterTemplateExclusionPassingCount := 0

def closedCollarSimplePatchN8Stratified33FirstIndex : Nat :=
  0

def closedCollarSimplePatchN8Stratified33LastIndex : Nat :=
  1189087724

def closedCollarSimplePatchN6TemplateBlockerArchiveCounts :
    ClosedCollarSimplePatchTemplateBlockerArchiveCounts where
  internalVertexCount := 6
  archivedSliceFileCount := 5
  archivedPatchStartIndex := 800000
  archivedPatchEndIndex := 1858980
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

def closedCollarSimplePatchN8First2000000TemplateBlockerArchiveCounts :
    ClosedCollarSimplePatchTemplateBlockerArchiveCounts where
  internalVertexCount := 8
  archivedSliceFileCount := 5
  archivedPatchStartIndex := 0
  archivedPatchEndIndex := 2000000
  processedPatchTopologyCount := 2000000
  radialOrderCaseCount := 4000000
  profilePreservingCaseCount := 0
  structuralFirstBlockerCount := 0
  exactTemplateBlockerCount := 0
  diagonalForwardTemplateCount := 0
  diagonalReverseTemplateCount := 0
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
Tracked archive manifest for the template-blocker verdict JSONs.  The n6
archive covers the five template-blocker slices from index 800000 through the
end of the exact six-internal space; the first 800000 cases are represented by
the earlier structural slice aggregate.  The n8 archive covers the five
template-blocker slices making up the first 2000000 prefix.
-/
def ClosedCollarWindingFreedomSimplePatchTemplateBlockerArchiveEvidence :
    Prop :=
  ClosedCollarWindingFreedomWitnessRealizationData ∧
    closedCollarSimplePatchN6TemplateBlockerArchiveCounts.archivedSliceFileCount =
      5 ∧
    closedCollarSimplePatchN6TemplateBlockerArchiveCounts.archivedPatchStartIndex =
      800000 ∧
    closedCollarSimplePatchN6TemplateBlockerArchiveCounts.archivedPatchEndIndex =
      closedCollarSimplePatchN6ExactPatchTopologyCount ∧
    closedCollarSimplePatchN6TemplateBlockerArchiveCounts.processedPatchTopologyCount =
      closedCollarSimplePatchN6Slices800000_1858980TemplateBlockerCounts.processedPatchTopologyCount ∧
    closedCollarSimplePatchN6TemplateBlockerArchiveCounts.radialOrderCaseCount =
      closedCollarSimplePatchN6Slices800000_1858980TemplateBlockerCounts.radialOrderCaseCount ∧
    closedCollarSimplePatchN6TemplateBlockerArchiveCounts.profilePreservingCaseCount =
      closedCollarSimplePatchN6Slices800000_1858980TemplateBlockerCounts.profilePreservingCaseCount ∧
    closedCollarSimplePatchN6TemplateBlockerArchiveCounts.structuralFirstBlockerCount =
      closedCollarSimplePatchN6Slices800000_1858980TemplateBlockerCounts.structuralFirstBlockerCount ∧
    closedCollarSimplePatchN6TemplateBlockerArchiveCounts.exactTemplateBlockerCount =
      closedCollarSimplePatchN6Slices800000_1858980TemplateBlockerCounts.exactTemplateBlockerCount ∧
    closedCollarSimplePatchN6TemplateBlockerArchiveCounts.diagonalForwardTemplateCount =
      closedCollarSimplePatchN6Slices800000_1858980TemplateBlockerCounts.diagonalForwardTemplateCount ∧
    closedCollarSimplePatchN6TemplateBlockerArchiveCounts.diagonalReverseTemplateCount =
      closedCollarSimplePatchN6Slices800000_1858980TemplateBlockerCounts.diagonalReverseTemplateCount ∧
    closedCollarSimplePatchN6TemplateBlockerArchiveCounts.nonTemplateCyclicCutBlockerCount =
      0 ∧
    closedCollarSimplePatchN6TemplateBlockerArchiveCounts.cap5LikeBlockerCount =
      0 ∧
    closedCollarSimplePatchN6TemplateBlockerArchiveCounts.normalFormAfterTemplateExclusionPassingCount =
      0 ∧
    closedCollarSimplePatchN6First800000StructuralCounts.processedPatchTopologyCount +
        closedCollarSimplePatchN6TemplateBlockerArchiveCounts.processedPatchTopologyCount =
      closedCollarSimplePatchN6AllTemplateBlockerCounts.processedPatchTopologyCount ∧
    closedCollarSimplePatchN6First800000StructuralCounts.profilePreservingCaseCount +
        closedCollarSimplePatchN6TemplateBlockerArchiveCounts.profilePreservingCaseCount =
      closedCollarSimplePatchN6AllTemplateBlockerCounts.profilePreservingCaseCount ∧
    closedCollarSimplePatchN8First2000000TemplateBlockerArchiveCounts.archivedSliceFileCount =
      5 ∧
    closedCollarSimplePatchN8First2000000TemplateBlockerArchiveCounts.archivedPatchStartIndex =
      0 ∧
    closedCollarSimplePatchN8First2000000TemplateBlockerArchiveCounts.archivedPatchEndIndex =
      2000000 ∧
    closedCollarSimplePatchN8First2000000TemplateBlockerArchiveCounts.processedPatchTopologyCount =
      closedCollarSimplePatchN8First2000000TemplateBlockerCounts.processedPatchTopologyCount ∧
    closedCollarSimplePatchN8First2000000TemplateBlockerArchiveCounts.radialOrderCaseCount =
      closedCollarSimplePatchN8First2000000TemplateBlockerCounts.radialOrderCaseCount ∧
    closedCollarSimplePatchN8First2000000TemplateBlockerArchiveCounts.profilePreservingCaseCount =
      closedCollarSimplePatchN8First2000000TemplateBlockerCounts.profilePreservingCaseCount ∧
    closedCollarSimplePatchN8First2000000TemplateBlockerArchiveCounts.normalFormAfterTemplateExclusionPassingCount =
      closedCollarSimplePatchN8First2000000TemplateBlockerCounts.normalFormAfterTemplateExclusionPassingCount

theorem closedCollarWindingFreedomSimplePatchTemplateBlockerArchiveEvidence :
    ClosedCollarWindingFreedomSimplePatchTemplateBlockerArchiveEvidence := by
  refine ⟨closedCollarWindingFreedomWitnessRealizationData, ?_⟩
  decide

/--
First-million eight-internal simple-patch evidence.  The lab processed the
first 1000000 simple cubic four-terminal patch topologies at eight internal
vertices, tested both radial orders, and found no profile-preserving
candidate for the closed-collar winding-freedom witness.
-/
def ClosedCollarWindingFreedomSimplePatchN8First1000000NoProfilePreservingEvidence :
    Prop :=
  ClosedCollarWindingFreedomWitnessRealizationData ∧
    closedCollarSimplePatchN8First1000000TemplateBlockerCounts.internalVertexCount =
      8 ∧
    closedCollarSimplePatchN8First1000000TemplateBlockerCounts.patchStartIndex =
      0 ∧
    closedCollarSimplePatchN8First1000000TemplateBlockerCounts.patchTopologyLimit =
      1000000 ∧
    closedCollarSimplePatchN8First1000000TemplateBlockerCounts.processedPatchTopologyCount =
      1000000 ∧
    closedCollarSimplePatchN8First1000000TemplateBlockerCounts.radialOrderCaseCount =
      2000000 ∧
    closedCollarSimplePatchN8First1000000TemplateBlockerCounts.profilePreservingCaseCount =
      0 ∧
    closedCollarSimplePatchN8First1000000TemplateBlockerCounts.structuralFirstBlockerCount =
      0 ∧
    closedCollarSimplePatchN8First1000000TemplateBlockerCounts.exactTemplateBlockerCount =
      0 ∧
    closedCollarSimplePatchN8First1000000TemplateBlockerCounts.nonTemplateCyclicCutBlockerCount =
      0 ∧
    closedCollarSimplePatchN8First1000000TemplateBlockerCounts.cap5LikeBlockerCount =
      0 ∧
    closedCollarSimplePatchN8First1000000TemplateBlockerCounts.normalFormAfterTemplateExclusionPassingCount =
      0

theorem closedCollarWindingFreedomSimplePatchN8First1000000NoProfilePreservingEvidence :
    ClosedCollarWindingFreedomSimplePatchN8First1000000NoProfilePreservingEvidence := by
  refine
    ⟨closedCollarWindingFreedomWitnessRealizationData,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    decide

/-- Lab-side impossibility of a profile-preserving candidate in the first
million eight-internal simple-patch prefix. -/
structure ClosedCollarWindingFreedomSimplePatchN8First1000000ProfilePreservingCandidate where
  hprofileCountPositive :
    0 <
      closedCollarSimplePatchN8First1000000TemplateBlockerCounts.profilePreservingCaseCount

theorem closedCollarWindingFreedomSimplePatchN8First1000000_noProfilePreservingCandidate
    (candidate : ClosedCollarWindingFreedomSimplePatchN8First1000000ProfilePreservingCandidate) :
    False := by
  have hzero :
      closedCollarSimplePatchN8First1000000TemplateBlockerCounts.profilePreservingCaseCount =
        0 := rfl
  have hpos := candidate.hprofileCountPositive
  omega

/--
Two-million-prefix eight-internal simple-patch evidence.  The lab processed
the first 2000000 simple cubic four-terminal patch topologies at eight internal
vertices, tested both radial orders, and found no profile-preserving candidate
for the closed-collar winding-freedom witness.  This is a continuous prefix
certificate, not an exhaustion certificate.
-/
def ClosedCollarWindingFreedomSimplePatchN8First2000000NoProfilePreservingEvidence :
    Prop :=
  ClosedCollarWindingFreedomWitnessRealizationData ∧
    closedCollarSimplePatchN8First1000000TemplateBlockerCounts.internalVertexCount =
      8 ∧
    closedCollarSimplePatchN8First1000000TemplateBlockerCounts.patchStartIndex =
      0 ∧
    closedCollarSimplePatchN8First1000000TemplateBlockerCounts.patchTopologyLimit =
      1000000 ∧
    closedCollarSimplePatchN8Slices1000000_1500000TemplateBlockerCounts.internalVertexCount =
      8 ∧
    closedCollarSimplePatchN8Slices1000000_1500000TemplateBlockerCounts.patchStartIndex =
      1000000 ∧
    closedCollarSimplePatchN8Slices1000000_1500000TemplateBlockerCounts.patchTopologyLimit =
      500000 ∧
    closedCollarSimplePatchN8Slices1500000_2000000TemplateBlockerCounts.internalVertexCount =
      8 ∧
    closedCollarSimplePatchN8Slices1500000_2000000TemplateBlockerCounts.patchStartIndex =
      1500000 ∧
    closedCollarSimplePatchN8Slices1500000_2000000TemplateBlockerCounts.patchTopologyLimit =
      500000 ∧
    closedCollarSimplePatchN8First2000000TemplateBlockerCounts.internalVertexCount =
      8 ∧
    closedCollarSimplePatchN8First2000000TemplateBlockerCounts.patchStartIndex =
      0 ∧
    closedCollarSimplePatchN8First2000000TemplateBlockerCounts.patchTopologyLimit =
      2000000 ∧
    closedCollarSimplePatchN8First2000000TemplateBlockerCounts.processedPatchTopologyCount =
      2000000 ∧
    closedCollarSimplePatchN8First2000000TemplateBlockerCounts.radialOrderCaseCount =
      4000000 ∧
    closedCollarSimplePatchN8First2000000TemplateBlockerCounts.profilePreservingCaseCount =
      0 ∧
    closedCollarSimplePatchN8First2000000TemplateBlockerCounts.structuralFirstBlockerCount =
      0 ∧
    closedCollarSimplePatchN8First2000000TemplateBlockerCounts.exactTemplateBlockerCount =
      0 ∧
    closedCollarSimplePatchN8First2000000TemplateBlockerCounts.nonTemplateCyclicCutBlockerCount =
      0 ∧
    closedCollarSimplePatchN8First2000000TemplateBlockerCounts.cap5LikeBlockerCount =
      0 ∧
    closedCollarSimplePatchN8First2000000TemplateBlockerCounts.normalFormAfterTemplateExclusionPassingCount =
      0 ∧
    closedCollarSimplePatchN8First1000000TemplateBlockerCounts.processedPatchTopologyCount +
        closedCollarSimplePatchN8Slices1000000_1500000TemplateBlockerCounts.processedPatchTopologyCount +
          closedCollarSimplePatchN8Slices1500000_2000000TemplateBlockerCounts.processedPatchTopologyCount =
      closedCollarSimplePatchN8First2000000TemplateBlockerCounts.processedPatchTopologyCount ∧
    closedCollarSimplePatchN8First1000000TemplateBlockerCounts.radialOrderCaseCount +
        closedCollarSimplePatchN8Slices1000000_1500000TemplateBlockerCounts.radialOrderCaseCount +
          closedCollarSimplePatchN8Slices1500000_2000000TemplateBlockerCounts.radialOrderCaseCount =
      closedCollarSimplePatchN8First2000000TemplateBlockerCounts.radialOrderCaseCount ∧
    closedCollarSimplePatchN8First1000000TemplateBlockerCounts.profilePreservingCaseCount +
        closedCollarSimplePatchN8Slices1000000_1500000TemplateBlockerCounts.profilePreservingCaseCount +
          closedCollarSimplePatchN8Slices1500000_2000000TemplateBlockerCounts.profilePreservingCaseCount =
      closedCollarSimplePatchN8First2000000TemplateBlockerCounts.profilePreservingCaseCount

theorem closedCollarWindingFreedomSimplePatchN8First2000000NoProfilePreservingEvidence :
    ClosedCollarWindingFreedomSimplePatchN8First2000000NoProfilePreservingEvidence := by
  refine ⟨closedCollarWindingFreedomWitnessRealizationData, ?_⟩
  decide

/-- Lab-side impossibility of a profile-preserving candidate in the first
two million eight-internal simple-patch prefix. -/
structure ClosedCollarWindingFreedomSimplePatchN8First2000000ProfilePreservingCandidate where
  hprofileCountPositive :
    0 <
      closedCollarSimplePatchN8First2000000TemplateBlockerCounts.profilePreservingCaseCount

theorem closedCollarWindingFreedomSimplePatchN8First2000000_noProfilePreservingCandidate
    (candidate : ClosedCollarWindingFreedomSimplePatchN8First2000000ProfilePreservingCandidate) :
    False := by
  have hzero :
      closedCollarSimplePatchN8First2000000TemplateBlockerCounts.profilePreservingCaseCount =
        0 := rfl
  have hpos := candidate.hprofileCountPositive
  omega

/--
Scope certificate for the current eight-internal simple-patch lab: the checked
first-2000000 prefix is strict, leaves 1187087725 generated topologies outside
the prefix, and covers less than one five-hundredth of the exact n8 labelled
simple-patch topology space.
-/
def ClosedCollarWindingFreedomSimplePatchN8First2000000CoverageEvidence : Prop :=
  ClosedCollarWindingFreedomSimplePatchN8First2000000NoProfilePreservingEvidence ∧
    closedCollarSimplePatchN8ExactPatchTopologyCount = 1189087725 ∧
    closedCollarSimplePatchN8First2000000TemplateBlockerCounts.processedPatchTopologyCount =
      2000000 ∧
    closedCollarSimplePatchN8First2000000TemplateBlockerCounts.processedPatchTopologyCount <
      closedCollarSimplePatchN8ExactPatchTopologyCount ∧
    closedCollarSimplePatchN8ExactPatchTopologyCount -
        closedCollarSimplePatchN8First2000000TemplateBlockerCounts.processedPatchTopologyCount =
      1187087725 ∧
    500 *
        closedCollarSimplePatchN8First2000000TemplateBlockerCounts.processedPatchTopologyCount <
      closedCollarSimplePatchN8ExactPatchTopologyCount

theorem closedCollarWindingFreedomSimplePatchN8First2000000CoverageEvidence :
    ClosedCollarWindingFreedomSimplePatchN8First2000000CoverageEvidence := by
  refine
    ⟨closedCollarWindingFreedomSimplePatchN8First2000000NoProfilePreservingEvidence,
      ?_, ?_, ?_, ?_, ?_⟩ <;>
    decide

/--
Stratified-sample evidence for the eight-internal simple-patch space.  The lab
unranked 33 evenly spaced exact topology indices, including the first and last
generated topology, tested both radial orders, and found no profile-preserving
candidate for the closed-collar winding-freedom witness.  This is distribution
coverage evidence, not an exhaustion certificate.
-/
def ClosedCollarWindingFreedomSimplePatchN8Stratified33NoProfilePreservingEvidence :
    Prop :=
  ClosedCollarWindingFreedomWitnessRealizationData ∧
    closedCollarSimplePatchN8Stratified33TemplateBlockerIndexSampleCounts.internalVertexCount =
      8 ∧
    closedCollarSimplePatchN8Stratified33TemplateBlockerIndexSampleCounts.exactPatchTopologyCount =
      closedCollarSimplePatchN8ExactPatchTopologyCount ∧
    closedCollarSimplePatchN8Stratified33TemplateBlockerIndexSampleCounts.exactPatchTopologyCount =
      1189087725 ∧
    closedCollarSimplePatchN8Stratified33TemplateBlockerIndexSampleCounts.sampledPatchTopologyCount =
      33 ∧
    closedCollarSimplePatchN8Stratified33TemplateBlockerIndexSampleCounts.radialOrderCaseCount =
      66 ∧
    closedCollarSimplePatchN8Stratified33TemplateBlockerIndexSampleCounts.profilePreservingCaseCount =
      0 ∧
    closedCollarSimplePatchN8Stratified33TemplateBlockerIndexSampleCounts.structuralFirstBlockerCount =
      0 ∧
    closedCollarSimplePatchN8Stratified33TemplateBlockerIndexSampleCounts.exactTemplateBlockerCount =
      0 ∧
    closedCollarSimplePatchN8Stratified33TemplateBlockerIndexSampleCounts.nonTemplateCyclicCutBlockerCount =
      0 ∧
    closedCollarSimplePatchN8Stratified33TemplateBlockerIndexSampleCounts.cap5LikeBlockerCount =
      0 ∧
    closedCollarSimplePatchN8Stratified33TemplateBlockerIndexSampleCounts.normalFormAfterTemplateExclusionPassingCount =
      0 ∧
    closedCollarSimplePatchN8Stratified33TemplateBlockerIndexSampleCounts.radialOrderCaseCount =
      2 *
        closedCollarSimplePatchN8Stratified33TemplateBlockerIndexSampleCounts.sampledPatchTopologyCount ∧
    closedCollarSimplePatchN8Stratified33FirstIndex = 0 ∧
    closedCollarSimplePatchN8Stratified33LastIndex + 1 =
      closedCollarSimplePatchN8ExactPatchTopologyCount

theorem closedCollarWindingFreedomSimplePatchN8Stratified33NoProfilePreservingEvidence :
    ClosedCollarWindingFreedomSimplePatchN8Stratified33NoProfilePreservingEvidence := by
  refine ⟨closedCollarWindingFreedomWitnessRealizationData, ?_⟩
  decide

/-- Lab-side impossibility of a profile-preserving candidate in the 33-point
stratified eight-internal simple-patch sample. -/
structure ClosedCollarWindingFreedomSimplePatchN8Stratified33ProfilePreservingCandidate where
  hprofileCountPositive :
    0 <
      closedCollarSimplePatchN8Stratified33TemplateBlockerIndexSampleCounts.profilePreservingCaseCount

theorem closedCollarWindingFreedomSimplePatchN8Stratified33_noProfilePreservingCandidate
    (candidate :
      ClosedCollarWindingFreedomSimplePatchN8Stratified33ProfilePreservingCandidate) :
    False := by
  have hzero :
      closedCollarSimplePatchN8Stratified33TemplateBlockerIndexSampleCounts.profilePreservingCaseCount =
        0 := rfl
  have hpos := candidate.hprofileCountPositive
  omega

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
A normal-form realization represented by one enumerated six-internal simple
patch.  The equality field records that the normal-form annulus and the
finite patch representation are the same annular realization.
-/
structure ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation
    (G : SimpleGraph V) where
  normalForm : ClosedCollarWindingFreedomNormalFormRealization G
  representation : ClosedCollarWindingFreedomSimplePatchN6Representation G
  annular_eq : representation.annular = normalForm.annular

/--
A six-internal simple-patch representation whose normal-form annulus already
comes with the cut-open radial-face datum needed by the embedding lab.
-/
structure ClosedCollarWindingFreedomSimplePatchN6NormalFormRadialFaceRepresentation
    (G : SimpleGraph V) where
  normalFormRadialFace : ClosedCollarWindingFreedomNormalFormRadialFaceRealization G
  representation : ClosedCollarWindingFreedomSimplePatchN6Representation G
  annular_eq : normalFormRadialFace.normalForm.annular = representation.annular

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

/--
Counts for the radial-face annular embedding audit on selected six-internal
simple-patch realizations.  The audit enumerates all cubic rotation systems
for the sampled planar profile-preserving cases and asks whether the four
radial-cut edges can lie on a single face of the cut-open collar graph.
-/
structure ClosedCollarSimplePatchAnnularEmbeddingSampleCounts where
  internalVertexCount : Nat
  sampledPatchTopologyCount : Nat
  radialOrderCaseCount : Nat
  profilePreservingCaseCount : Nat
  planarProfilePreservingCaseCount : Nat
  radialFaceCoherentCaseCount : Nat
  radialFaceIncoherentCaseCount : Nat
  totalRotationSystemCount : Nat
  enumeratedRotationSystemCount : Nat
  planarRotationSystemCount : Nat
  radialFaceCoherentRotationCount : Nat
  exactDiagonalTwoPoleTemplateBlockerCount : Nat
  maxRadialCutEdgesOnSingleFaceTwoCount : Nat

def closedCollarSimplePatchN6AnnularEmbeddingSamplePatchIndices : List Nat :=
  [821205, 852969, 1000301]

def closedCollarSimplePatchN6AnnularEmbeddingSampleCases : List (Nat × Nat) :=
  [(821205, 0), (821205, 1), (852969, 0), (852969, 1),
    (1000301, 0), (1000301, 1)]

def closedCollarSimplePatchN6AnnularEmbeddingSampleCounts :
    ClosedCollarSimplePatchAnnularEmbeddingSampleCounts where
  internalVertexCount := 6
  sampledPatchTopologyCount := 3
  radialOrderCaseCount := 6
  profilePreservingCaseCount := 6
  planarProfilePreservingCaseCount := 6
  radialFaceCoherentCaseCount := 0
  radialFaceIncoherentCaseCount := 6
  totalRotationSystemCount := 1572864
  enumeratedRotationSystemCount := 1572864
  planarRotationSystemCount := 48
  radialFaceCoherentRotationCount := 0
  exactDiagonalTwoPoleTemplateBlockerCount := 6
  maxRadialCutEdgesOnSingleFaceTwoCount := 48

/--
Archived radial-face evidence for selected planar profile-preserving
six-internal cases.  These cases preserve the winding-freedom witness and pass
planarity, but no planar rotation system among the 48 found places all four
radial-cut edges on one face.  This is a concrete annular embedding constraint,
not an exhaustive nonrealizability theorem for all fillers.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceEvidence :
    Prop :=
  ClosedCollarWindingFreedomWitnessRealizationData ∧
    closedCollarSimplePatchN6AnnularEmbeddingSamplePatchIndices =
      [821205, 852969, 1000301] ∧
    closedCollarSimplePatchN6AnnularEmbeddingSampleCases =
      [(821205, 0), (821205, 1), (852969, 0), (852969, 1),
        (1000301, 0), (1000301, 1)] ∧
    closedCollarSimplePatchN6AnnularEmbeddingSampleCounts.internalVertexCount =
      6 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSampleCounts.sampledPatchTopologyCount =
      3 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSampleCounts.radialOrderCaseCount =
      6 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSampleCounts.profilePreservingCaseCount =
      6 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSampleCounts.planarProfilePreservingCaseCount =
      6 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSampleCounts.radialFaceCoherentCaseCount =
      0 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSampleCounts.radialFaceIncoherentCaseCount =
      6 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSampleCounts.totalRotationSystemCount =
      1572864 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSampleCounts.enumeratedRotationSystemCount =
      closedCollarSimplePatchN6AnnularEmbeddingSampleCounts.totalRotationSystemCount ∧
    closedCollarSimplePatchN6AnnularEmbeddingSampleCounts.planarRotationSystemCount =
      48 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSampleCounts.radialFaceCoherentRotationCount =
      0 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSampleCounts.exactDiagonalTwoPoleTemplateBlockerCount =
      6 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSampleCounts.maxRadialCutEdgesOnSingleFaceTwoCount =
      closedCollarSimplePatchN6AnnularEmbeddingSampleCounts.planarRotationSystemCount

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceEvidence :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceEvidence := by
  refine ⟨closedCollarWindingFreedomWitnessRealizationData, ?_⟩
  decide

/-- Lab-side candidate for a radial-face coherent case in this n6 sample. -/
structure ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCaseCandidate where
  hcaseCountPositive :
    0 <
      closedCollarSimplePatchN6AnnularEmbeddingSampleCounts.radialFaceCoherentCaseCount

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSample_noRadialFaceCaseCandidate
    (candidate :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCaseCandidate) :
    False := by
  have hzero :
      closedCollarSimplePatchN6AnnularEmbeddingSampleCounts.radialFaceCoherentCaseCount =
        0 := rfl
  have hpos := candidate.hcaseCountPositive
  omega

/--
Lab-side candidate for a radial-face coherent planar rotation system in this
n6 sample.
-/
structure ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRotationCandidate where
  hrotationCountPositive :
    0 <
      closedCollarSimplePatchN6AnnularEmbeddingSampleCounts.radialFaceCoherentRotationCount

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSample_noRadialFaceRotationCandidate
    (candidate :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRotationCandidate) :
    False := by
  have hzero :
      closedCollarSimplePatchN6AnnularEmbeddingSampleCounts.radialFaceCoherentRotationCount =
        0 := rfl
  have hpos := candidate.hrotationCountPositive
  omega

/--
Coverage obligation for the radial-face sample: if a sampled six-internal
simple-patch representation carries a genuine cut-open radial face, then the
rotation-system lab counts at least one radial-face coherent planar rotation.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCoveredByLab :
    Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    (representation : ClosedCollarWindingFreedomSimplePatchN6Representation G) →
      (representation.patchTopologyIndex, representation.radialOrderIndex.1) ∈
          closedCollarSimplePatchN6AnnularEmbeddingSampleCases →
        ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
          representation.annular →
          Nonempty
            ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRotationCandidate

/--
Sample-level obstruction for radial-face coherent annular realizations.  It
does not assert the coverage obligation; it states the exact implication the
geometry proof must feed from honest collar embeddings into the finite lab.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleNoRadialFaceCoherentRepresentation :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCoveredByLab →
    ∀ {V : Type} {G : SimpleGraph V},
      (representation : ClosedCollarWindingFreedomSimplePatchN6Representation G) →
        (representation.patchTopologyIndex, representation.radialOrderIndex.1) ∈
            closedCollarSimplePatchN6AnnularEmbeddingSampleCases →
          ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
            representation.annular →
            False

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleNoRadialFaceCoherentRepresentation :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleNoRadialFaceCoherentRepresentation := by
  intro hcovered V G representation hsample hradial
  rcases hcovered representation hsample hradial with ⟨candidate⟩
  exact
    closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSample_noRadialFaceRotationCandidate
      candidate

/--
Direct sampled obstruction once the normal-form realization already supplies
the cut-open radial face.  This is the immediate bridge from actual embedded
collar data to the archived rotation-system verdict; it still requires the
finite lab coverage map for the representation class.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleNoNormalFormRadialFaceRepresentation :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCoveredByLab →
    ∀ {V : Type} {G : SimpleGraph V},
      (data :
        ClosedCollarWindingFreedomSimplePatchN6NormalFormRadialFaceRepresentation G) →
        (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
            closedCollarSimplePatchN6AnnularEmbeddingSampleCases →
          False

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleNoNormalFormRadialFaceRepresentation :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleNoNormalFormRadialFaceRepresentation := by
  intro hcovered V G data hsample
  have hradial :
      ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
        data.representation.annular := by
    have hbase :
        ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
          data.normalFormRadialFace.normalForm.annular :=
      ⟨data.normalFormRadialFace.radialFace⟩
    simpa [data.annular_eq] using hbase
  exact
    closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleNoRadialFaceCoherentRepresentation
      hcovered data.representation hsample hradial

/--
Missing geometric reduction for using the radial-face sample against the
normal-form regime: every sampled six-internal normal-form representation must
provide a radial-face coherent cut-open annulus.
-/
def ClosedCollarWindingFreedomSimplePatchN6NormalFormSampleForcesRadialFace :
    Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
      (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
          closedCollarSimplePatchN6AnnularEmbeddingSampleCases →
        ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
          data.representation.annular

/--
Radial-face version of the serious S4 repair target for the sampled
six-internal subclass.  Once the embedding geometry proves radial-face
coherence for honest normal-form collars and the lab coverage map is supplied,
the sampled normal-form representations are excluded by the archived
rotation-system verdict.
-/
def Section92Step4RadialFaceSampleNormalFormObstructionTarget : Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCoveredByLab →
    ClosedCollarWindingFreedomSimplePatchN6NormalFormSampleForcesRadialFace →
      ∀ {V : Type} {G : SimpleGraph V},
        (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
          (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
              closedCollarSimplePatchN6AnnularEmbeddingSampleCases →
            False

theorem section92Step4RadialFaceSampleNormalFormObstructionTarget :
    Section92Step4RadialFaceSampleNormalFormObstructionTarget := by
  intro hcovered hforces V G data hsample
  exact
    closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleNoRadialFaceCoherentRepresentation
      hcovered data.representation hsample (hforces data hsample)

/--
Counts for a resumable radial-face slice search beginning at topology index
`1000000`.  Unlike the earlier indexed sample, this mode scans a bounded
range, discovers profile-preserving non-structural cases, and only then runs
the rotation-system radial-face audit.
-/
structure ClosedCollarSimplePatchAnnularEmbeddingSliceCounts where
  internalVertexCount : Nat
  exactPatchTopologyCount : Nat
  patchStartIndex : Nat
  patchTopologyLimit : Nat
  nextPatchStartIndex : Nat
  stoppedByEmbeddingCaseLimit : Bool
  embeddingCaseLimit : Nat
  processedPatchTopologyCount : Nat
  radialOrderCaseCount : Nat
  profilePreservingCaseCount : Nat
  structuralSkippedCaseCount : Nat
  embeddingAuditedCaseCount : Nat
  radialFaceCoherentCaseCount : Nat
  radialFaceIncoherentCaseCount : Nat
  totalRotationSystemCount : Nat
  enumeratedRotationSystemCount : Nat
  planarRotationSystemCount : Nat
  radialFaceCoherentRotationCount : Nat
  exactDiagonalTwoPoleTemplateBlockerCount : Nat
  maxRadialCutEdgesOnSingleFaceTwoCount : Nat

def closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Cases :
    List (Nat × Nat) :=
  [(1000301, 0), (1000301, 1)]

def closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts :
    ClosedCollarSimplePatchAnnularEmbeddingSliceCounts where
  internalVertexCount := 6
  exactPatchTopologyCount := 1858980
  patchStartIndex := 1000000
  patchTopologyLimit := 500
  nextPatchStartIndex := 1000302
  stoppedByEmbeddingCaseLimit := true
  embeddingCaseLimit := 2
  processedPatchTopologyCount := 302
  radialOrderCaseCount := 604
  profilePreservingCaseCount := 2
  structuralSkippedCaseCount := 0
  embeddingAuditedCaseCount := 2
  radialFaceCoherentCaseCount := 0
  radialFaceIncoherentCaseCount := 2
  totalRotationSystemCount := 524288
  enumeratedRotationSystemCount := 524288
  planarRotationSystemCount := 16
  radialFaceCoherentRotationCount := 0
  exactDiagonalTwoPoleTemplateBlockerCount := 2
  maxRadialCutEdgesOnSingleFaceTwoCount := 16

/--
Archived evidence from the bounded radial-face slice mode.  The scan
processed topology indices `1000000` through `1000301`, discovered two
profile-preserving non-structural cases at topology `1000301`, exhausted both
rotation-system searches, and found no radial-face coherent planar rotation.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000RadialFaceEvidence :
    Prop :=
  ClosedCollarWindingFreedomWitnessRealizationData ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Cases =
      [(1000301, 0), (1000301, 1)] ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.internalVertexCount =
      6 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.exactPatchTopologyCount =
      1858980 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.patchStartIndex =
      1000000 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.patchTopologyLimit =
      500 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.nextPatchStartIndex =
      1000302 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.stoppedByEmbeddingCaseLimit =
      true ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.embeddingCaseLimit =
      2 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.processedPatchTopologyCount =
      302 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.radialOrderCaseCount =
      604 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.profilePreservingCaseCount =
      2 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.structuralSkippedCaseCount =
      0 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.embeddingAuditedCaseCount =
      2 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.radialFaceCoherentCaseCount =
      0 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.radialFaceIncoherentCaseCount =
      2 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.totalRotationSystemCount =
      524288 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.enumeratedRotationSystemCount =
      closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.totalRotationSystemCount ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.planarRotationSystemCount =
      16 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.radialFaceCoherentRotationCount =
      0 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.exactDiagonalTwoPoleTemplateBlockerCount =
      2 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.maxRadialCutEdgesOnSingleFaceTwoCount =
      closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.planarRotationSystemCount

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000RadialFaceEvidence :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000RadialFaceEvidence := by
  refine ⟨closedCollarWindingFreedomWitnessRealizationData, ?_⟩
  decide

/--
First-blocker reading of the bounded radial-face slice.  The two discovered
profile-preserving non-structural cases are already exact diagonal two-pole
template blockers before the radial-face question is asked; the radial-face
audit then confirms that neither has a coherent cut-open face.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000ExactTemplateFirstBlockerEvidence :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000RadialFaceEvidence ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.profilePreservingCaseCount =
      2 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.exactDiagonalTwoPoleTemplateBlockerCount =
      2 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.profilePreservingCaseCount =
      closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.exactDiagonalTwoPoleTemplateBlockerCount ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.structuralSkippedCaseCount =
      0 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.embeddingAuditedCaseCount =
      closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.exactDiagonalTwoPoleTemplateBlockerCount ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.radialFaceCoherentRotationCount =
      0

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000ExactTemplateFirstBlockerEvidence :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000ExactTemplateFirstBlockerEvidence := by
  refine
    ⟨closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000RadialFaceEvidence,
      ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    decide

def ClosedCollarDiagonalTwoPoleTemplateId.labKey :
    ClosedCollarDiagonalTwoPoleTemplateId → String
  | .forward => "edges:g0:F1F0,g1:F4F5|sideCollar:g0:F1,g1:F5"
  | .reverse => "edges:g0:F4F5,g1:F1F0|sideCollar:g0:F5,g1:F1"

/-- Per-case exact-template payload for the bounded radial-face slice. -/
structure ClosedCollarAnnularEmbeddingSliceExactTemplateCase where
  patchTopologyIndex : Nat
  radialOrderIndex : Nat
  template : ClosedCollarDiagonalTwoPoleTemplateId
  exactTemplateKey : String
  cutEdges : List String
  sideCollarVertices : List String
  sideVertices : List String
  cutSize : Nat
  sideVertexCount : Nat
  otherSideVertexCount : Nat

def closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Case0Template :
    ClosedCollarAnnularEmbeddingSliceExactTemplateCase where
  patchTopologyIndex := 1000301
  radialOrderIndex := 0
  template := ClosedCollarDiagonalTwoPoleTemplateId.reverse
  exactTemplateKey := ClosedCollarDiagonalTwoPoleTemplateId.reverse.labKey
  cutEdges := ["g0:F4F5", "g1:F1F0"]
  sideCollarVertices := ["g0:F5", "g1:F1"]
  sideVertices := ["N1", "N2", "g0:F5", "g1:F1"]
  cutSize := 2
  sideVertexCount := 4
  otherSideVertexCount := 14

def closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Case1Template :
    ClosedCollarAnnularEmbeddingSliceExactTemplateCase where
  patchTopologyIndex := 1000301
  radialOrderIndex := 1
  template := ClosedCollarDiagonalTwoPoleTemplateId.reverse
  exactTemplateKey := ClosedCollarDiagonalTwoPoleTemplateId.reverse.labKey
  cutEdges := ["g0:F4F5", "g1:F1F0"]
  sideCollarVertices := ["g0:F5", "g1:F1"]
  sideVertices := ["N1", "N2", "g0:F5", "g1:F1"]
  cutSize := 2
  sideVertexCount := 4
  otherSideVertexCount := 14

/--
Per-case template payload for the bounded radial-face slice.  Both discovered
cases are the reverse exact diagonal two-pole template, with the exact lab key
and separator side recorded.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000ReverseTemplatePayloadEvidence :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000ExactTemplateFirstBlockerEvidence ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Case0Template.patchTopologyIndex =
      1000301 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Case0Template.radialOrderIndex =
      0 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Case1Template.patchTopologyIndex =
      1000301 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Case1Template.radialOrderIndex =
      1 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Case0Template.template =
      ClosedCollarDiagonalTwoPoleTemplateId.reverse ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Case1Template.template =
      ClosedCollarDiagonalTwoPoleTemplateId.reverse ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Case0Template.exactTemplateKey =
      ClosedCollarDiagonalTwoPoleTemplateId.reverse.labKey ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Case1Template.exactTemplateKey =
      ClosedCollarDiagonalTwoPoleTemplateId.reverse.labKey ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Case0Template.cutEdges =
      ClosedCollarDiagonalTwoPoleTemplateId.reverse.cutEdges ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Case1Template.cutEdges =
      ClosedCollarDiagonalTwoPoleTemplateId.reverse.cutEdges ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Case0Template.sideCollarVertices =
      ClosedCollarDiagonalTwoPoleTemplateId.reverse.sideCollarVertices ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Case1Template.sideCollarVertices =
      ClosedCollarDiagonalTwoPoleTemplateId.reverse.sideCollarVertices ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Case0Template.sideVertices =
      ["N1", "N2", "g0:F5", "g1:F1"] ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Case1Template.sideVertices =
      ["N1", "N2", "g0:F5", "g1:F1"] ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Case0Template.cutSize =
      2 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Case1Template.cutSize =
      2 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Case0Template.sideVertexCount =
      4 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Case1Template.sideVertexCount =
      4 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Case0Template.otherSideVertexCount =
      14 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Case1Template.otherSideVertexCount =
      14

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000ReverseTemplatePayloadEvidence :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000ReverseTemplatePayloadEvidence := by
  refine
    ⟨closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000ExactTemplateFirstBlockerEvidence,
      ?_⟩
  decide

/--
Coverage obligation for using the slice's exact-template first blocker against
normal-form realizations: a normal-form representation in one of the slice
cases must realize one of the exact diagonal collar two-pole separators.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000NormalFormForcesExactTemplate :
    Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
      (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
          closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Cases →
        ∃ candidate : ClosedCollarDiagonalTwoPoleTemplateCandidate G,
          candidate.Realizes

/--
Exact-template normal-form obstruction target for the bounded slice.  Once the
geometry proof supplies the slice-specific exact-template coverage map, cyclic
five-edge-connectivity excludes every normal-form representation in the two
discovered cases.
-/
def Section92Step4ExactTemplateSlice1000000NormalFormObstructionTarget : Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000ExactTemplateFirstBlockerEvidence →
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000NormalFormForcesExactTemplate →
      ∀ {V : Type} {G : SimpleGraph V},
        (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
          (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
              closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Cases →
            False

theorem section92Step4ExactTemplateSlice1000000NormalFormObstructionTarget :
    Section92Step4ExactTemplateSlice1000000NormalFormObstructionTarget := by
  intro _hevidence hforces V G data hcase
  rcases hforces data hcase with ⟨candidate, hrealizes⟩
  exact
    closedCollarWindingFreedomNormalFormRealization_false_of_forcedTemplate
      data.normalForm candidate hrealizes

/--
Sharper coverage obligation supplied by the refreshed slice archive: a
normal-form representation in either discovered case must realize the reverse
exact diagonal two-pole template.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000NormalFormForcesReverseTemplate :
    Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
      (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
          closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Cases →
        ∃ candidate : ClosedCollarDiagonalTwoPoleTemplateCandidate G,
          candidate.template = ClosedCollarDiagonalTwoPoleTemplateId.reverse ∧
            candidate.Realizes

/--
Reverse-template normal-form obstruction target for the bounded slice.  This
is the current sharpest named blocker for the discovered cases.
-/
def Section92Step4ReverseTemplateSlice1000000NormalFormObstructionTarget : Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000ReverseTemplatePayloadEvidence →
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000NormalFormForcesReverseTemplate →
      ∀ {V : Type} {G : SimpleGraph V},
        (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
          (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
              closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Cases →
            False

theorem section92Step4ReverseTemplateSlice1000000NormalFormObstructionTarget :
    Section92Step4ReverseTemplateSlice1000000NormalFormObstructionTarget := by
  intro _hevidence hforces V G data hcase
  rcases hforces data hcase with ⟨candidate, _htemplate, hrealizes⟩
  exact
    closedCollarWindingFreedomNormalFormRealization_false_of_forcedTemplate
      data.normalForm candidate hrealizes

/--
Current combined slice verdict: the discovered cases are exact-template first
blockers, and exact diagonal templates are incompatible with cyclically
five-edge-connected normal form.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000BlockedAfterCyclicallyFiveTemplateExclusion :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000ExactTemplateFirstBlockerEvidence ∧
    Section92WindingExactTemplateNormalFormExclusion

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000BlockedAfterCyclicallyFiveTemplateExclusion :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000BlockedAfterCyclicallyFiveTemplateExclusion := by
  exact
    ⟨closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000ExactTemplateFirstBlockerEvidence,
      section92WindingExactTemplateNormalFormExclusion⟩

def closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Cases :
    List (Nat × Nat) :=
  [(1000788, 0), (1000788, 1)]

def closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts :
    ClosedCollarSimplePatchAnnularEmbeddingSliceCounts where
  internalVertexCount := 6
  exactPatchTopologyCount := 1858980
  patchStartIndex := 1000302
  patchTopologyLimit := 500
  nextPatchStartIndex := 1000789
  stoppedByEmbeddingCaseLimit := true
  embeddingCaseLimit := 2
  processedPatchTopologyCount := 487
  radialOrderCaseCount := 974
  profilePreservingCaseCount := 2
  structuralSkippedCaseCount := 0
  embeddingAuditedCaseCount := 2
  radialFaceCoherentCaseCount := 0
  radialFaceIncoherentCaseCount := 2
  totalRotationSystemCount := 524288
  enumeratedRotationSystemCount := 524288
  planarRotationSystemCount := 16
  radialFaceCoherentRotationCount := 0
  exactDiagonalTwoPoleTemplateBlockerCount := 2
  maxRadialCutEdgesOnSingleFaceTwoCount := 16

/--
Archived evidence from the next bounded radial-face slice mode.  The scan
processed topology indices `1000302` through `1000788`, discovered two
profile-preserving non-structural cases at topology `1000788`, exhausted both
rotation-system searches, and found no radial-face coherent planar rotation.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceEvidence :
    Prop :=
  ClosedCollarWindingFreedomWitnessRealizationData ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Cases =
      [(1000788, 0), (1000788, 1)] ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.internalVertexCount =
      6 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.exactPatchTopologyCount =
      1858980 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.patchStartIndex =
      1000302 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.patchTopologyLimit =
      500 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.nextPatchStartIndex =
      1000789 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.stoppedByEmbeddingCaseLimit =
      true ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.embeddingCaseLimit =
      2 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.processedPatchTopologyCount =
      487 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.radialOrderCaseCount =
      974 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.profilePreservingCaseCount =
      2 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.structuralSkippedCaseCount =
      0 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.embeddingAuditedCaseCount =
      2 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.radialFaceCoherentCaseCount =
      0 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.radialFaceIncoherentCaseCount =
      2 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.totalRotationSystemCount =
      524288 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.enumeratedRotationSystemCount =
      closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.totalRotationSystemCount ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.planarRotationSystemCount =
      16 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.radialFaceCoherentRotationCount =
      0 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.exactDiagonalTwoPoleTemplateBlockerCount =
      2 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.maxRadialCutEdgesOnSingleFaceTwoCount =
      closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.planarRotationSystemCount

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceEvidence :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceEvidence := by
  refine ⟨closedCollarWindingFreedomWitnessRealizationData, ?_⟩
  decide

/--
First-blocker reading of the second bounded radial-face slice.  The two
discovered profile-preserving non-structural cases are already exact diagonal
two-pole template blockers, and the radial-face audit finds no coherent
cut-open face.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302ExactTemplateFirstBlockerEvidence :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceEvidence ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.profilePreservingCaseCount =
      2 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.exactDiagonalTwoPoleTemplateBlockerCount =
      2 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.profilePreservingCaseCount =
      closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.exactDiagonalTwoPoleTemplateBlockerCount ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.structuralSkippedCaseCount =
      0 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.embeddingAuditedCaseCount =
      closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.exactDiagonalTwoPoleTemplateBlockerCount ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.radialFaceCoherentRotationCount =
      0

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302ExactTemplateFirstBlockerEvidence :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302ExactTemplateFirstBlockerEvidence := by
  refine
    ⟨closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceEvidence,
      ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    decide

def closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Case0Template :
    ClosedCollarAnnularEmbeddingSliceExactTemplateCase where
  patchTopologyIndex := 1000788
  radialOrderIndex := 0
  template := ClosedCollarDiagonalTwoPoleTemplateId.reverse
  exactTemplateKey := ClosedCollarDiagonalTwoPoleTemplateId.reverse.labKey
  cutEdges := ["g0:F4F5", "g1:F1F0"]
  sideCollarVertices := ["g0:F5", "g1:F1"]
  sideVertices := ["N1", "N5", "g0:F5", "g1:F1"]
  cutSize := 2
  sideVertexCount := 4
  otherSideVertexCount := 14

def closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Case1Template :
    ClosedCollarAnnularEmbeddingSliceExactTemplateCase where
  patchTopologyIndex := 1000788
  radialOrderIndex := 1
  template := ClosedCollarDiagonalTwoPoleTemplateId.reverse
  exactTemplateKey := ClosedCollarDiagonalTwoPoleTemplateId.reverse.labKey
  cutEdges := ["g0:F4F5", "g1:F1F0"]
  sideCollarVertices := ["g0:F5", "g1:F1"]
  sideVertices := ["N1", "N5", "g0:F5", "g1:F1"]
  cutSize := 2
  sideVertexCount := 4
  otherSideVertexCount := 14

/--
Per-case template payload for the second bounded radial-face slice.  Both
discovered cases are again the reverse exact diagonal two-pole template.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302ReverseTemplatePayloadEvidence :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302ExactTemplateFirstBlockerEvidence ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Case0Template.patchTopologyIndex =
      1000788 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Case0Template.radialOrderIndex =
      0 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Case1Template.patchTopologyIndex =
      1000788 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Case1Template.radialOrderIndex =
      1 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Case0Template.template =
      ClosedCollarDiagonalTwoPoleTemplateId.reverse ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Case1Template.template =
      ClosedCollarDiagonalTwoPoleTemplateId.reverse ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Case0Template.exactTemplateKey =
      ClosedCollarDiagonalTwoPoleTemplateId.reverse.labKey ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Case1Template.exactTemplateKey =
      ClosedCollarDiagonalTwoPoleTemplateId.reverse.labKey ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Case0Template.cutEdges =
      ClosedCollarDiagonalTwoPoleTemplateId.reverse.cutEdges ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Case1Template.cutEdges =
      ClosedCollarDiagonalTwoPoleTemplateId.reverse.cutEdges ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Case0Template.sideCollarVertices =
      ClosedCollarDiagonalTwoPoleTemplateId.reverse.sideCollarVertices ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Case1Template.sideCollarVertices =
      ClosedCollarDiagonalTwoPoleTemplateId.reverse.sideCollarVertices ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Case0Template.sideVertices =
      ["N1", "N5", "g0:F5", "g1:F1"] ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Case1Template.sideVertices =
      ["N1", "N5", "g0:F5", "g1:F1"] ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Case0Template.cutSize =
      2 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Case1Template.cutSize =
      2 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Case0Template.sideVertexCount =
      4 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Case1Template.sideVertexCount =
      4 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Case0Template.otherSideVertexCount =
      14 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Case1Template.otherSideVertexCount =
      14

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302ReverseTemplatePayloadEvidence :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302ReverseTemplatePayloadEvidence := by
  refine
    ⟨closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302ExactTemplateFirstBlockerEvidence,
      ?_⟩
  decide

/--
Sharper coverage obligation for the second bounded slice: a normal-form
representation in either discovered case must realize the reverse exact
diagonal two-pole template.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302NormalFormForcesReverseTemplate :
    Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
      (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
          closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Cases →
        ∃ candidate : ClosedCollarDiagonalTwoPoleTemplateCandidate G,
          candidate.template = ClosedCollarDiagonalTwoPoleTemplateId.reverse ∧
            candidate.Realizes

/--
Reverse-template normal-form obstruction target for the second bounded slice.
-/
def Section92Step4ReverseTemplateSlice1000302NormalFormObstructionTarget : Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302ReverseTemplatePayloadEvidence →
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302NormalFormForcesReverseTemplate →
      ∀ {V : Type} {G : SimpleGraph V},
        (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
          (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
              closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Cases →
            False

theorem section92Step4ReverseTemplateSlice1000302NormalFormObstructionTarget :
    Section92Step4ReverseTemplateSlice1000302NormalFormObstructionTarget := by
  intro _hevidence hforces V G data hcase
  rcases hforces data hcase with ⟨candidate, _htemplate, hrealizes⟩
  exact
    closedCollarWindingFreedomNormalFormRealization_false_of_forcedTemplate
      data.normalForm candidate hrealizes

/--
Cumulative discovery evidence for the two consecutive bounded radial-face
slices.  Four audited profile-preserving cases have been found, all four are
reverse exact diagonal two-pole template blockers, and none has a radial-face
coherent planar rotation.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlices1000000_1000789ReverseTemplateDiscoveryEvidence :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000ReverseTemplatePayloadEvidence ∧
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302ReverseTemplatePayloadEvidence ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.embeddingAuditedCaseCount +
        closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.embeddingAuditedCaseCount =
      4 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.planarRotationSystemCount +
        closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.planarRotationSystemCount =
      32 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.radialFaceCoherentRotationCount +
        closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.radialFaceCoherentRotationCount =
      0 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.exactDiagonalTwoPoleTemplateBlockerCount +
        closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.exactDiagonalTwoPoleTemplateBlockerCount =
      4

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlices1000000_1000789ReverseTemplateDiscoveryEvidence :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlices1000000_1000789ReverseTemplateDiscoveryEvidence := by
  refine
    ⟨closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000ReverseTemplatePayloadEvidence,
      closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302ReverseTemplatePayloadEvidence,
      ?_, ?_, ?_, ?_⟩ <;>
    decide

/-- Lab-side candidate for a radial-face coherent rotation in the slice. -/
structure ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000RadialFaceRotationCandidate where
  hrotationCountPositive :
    0 <
      closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.radialFaceCoherentRotationCount

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000_noRadialFaceRotationCandidate
    (candidate :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000RadialFaceRotationCandidate) :
    False := by
  have hzero :
      closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.radialFaceCoherentRotationCount =
        0 := rfl
  have hpos := candidate.hrotationCountPositive
  omega

/--
Coverage obligation for the bounded radial-face slice: if a representation
lies in one of the discovered audited cases and carries a genuine cut-open
radial face, then the slice lab would count a coherent planar rotation.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000RadialFaceCoveredByLab :
    Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    (representation : ClosedCollarWindingFreedomSimplePatchN6Representation G) →
      (representation.patchTopologyIndex, representation.radialOrderIndex.1) ∈
          closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Cases →
        ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
          representation.annular →
          Nonempty
            ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000RadialFaceRotationCandidate

/--
Slice-level obstruction for radial-face coherent annular realizations in the
new resumable search mode.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000NoRadialFaceCoherentRepresentation :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000RadialFaceCoveredByLab →
    ∀ {V : Type} {G : SimpleGraph V},
      (representation : ClosedCollarWindingFreedomSimplePatchN6Representation G) →
        (representation.patchTopologyIndex, representation.radialOrderIndex.1) ∈
            closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Cases →
          ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
            representation.annular →
            False

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000NoRadialFaceCoherentRepresentation :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000NoRadialFaceCoherentRepresentation := by
  intro hcovered V G representation hcase hradial
  rcases hcovered representation hcase hradial with ⟨candidate⟩
  exact
    closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000_noRadialFaceRotationCandidate
      candidate

/--
Radial-face normal-form target for the bounded slice search.  This is the same
serious S4 bridge as the indexed sample, but now attached to a resumable
discovery run rather than hand-picked topology indices.
-/
def Section92Step4RadialFaceSlice1000000NormalFormObstructionTarget : Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000RadialFaceCoveredByLab →
    ClosedCollarWindingFreedomSimplePatchN6NormalFormSampleForcesRadialFace →
      ∀ {V : Type} {G : SimpleGraph V},
        (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
          (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
              closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Cases →
            False

theorem section92Step4RadialFaceSlice1000000NormalFormObstructionTarget :
    Section92Step4RadialFaceSlice1000000NormalFormObstructionTarget := by
  intro hcovered hforces V G data hcase
  have hsample :
      (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
          closedCollarSimplePatchN6AnnularEmbeddingSampleCases := by
    have hpairs :
        (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) =
            (1000301, 0) ∨
          (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) =
            (1000301, 1) := by
      simpa [closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Cases] using hcase
    rcases hpairs with h0 | h1
    · simp [closedCollarSimplePatchN6AnnularEmbeddingSampleCases, h0]
    · simp [closedCollarSimplePatchN6AnnularEmbeddingSampleCases, h1]
  exact
    closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000NoRadialFaceCoherentRepresentation
      hcovered data.representation hcase (hforces data hsample)

end GoertzelLemma818ClosedCollarWindingRealization

end Mettapedia.GraphTheory.FourColor
