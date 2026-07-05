import Mettapedia.GraphTheory.FourColor.CyclicEdgeCut
import Mettapedia.GraphTheory.FourColor.GoertzelDefinition48
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarWinding
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusGeometry

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
Lab classification surface for an honest n6 normal-form representation.  A
representation that preserves the closed-collar winding witness is classified
by the exhaustive simple-patch lab as either a structural prefix blocker, an
exact diagonal two-pole template, or a residual post-template-exclusion pass.
-/
structure ClosedCollarWindingFreedomSimplePatchN6ExhaustiveLabClassification
    {V : Type} {G : SimpleGraph V}
    (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) where
  structuralBlocker : Prop
  hclassified :
    structuralBlocker ∨
      (∃ candidate : ClosedCollarDiagonalTwoPoleTemplateCandidate G,
        candidate.Realizes) ∨
        Nonempty (ClosedCollarWindingFreedomSimplePatchN6LabNormalFormPass G)

/--
Coverage obligation from the finite exhaustive lab to graph-facing n6
representations: every honest normal-form representation in the n6 subclass
receives one of the lab classifications.
-/
def ClosedCollarWindingFreedomSimplePatchN6NormalFormClassifiedByExhaustiveLab :
    Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
      Nonempty
        (ClosedCollarWindingFreedomSimplePatchN6ExhaustiveLabClassification data)

/--
Geometric obligation that honest normal-form collars cannot be one of the
structural prefix blockers of the n6 lab.  This names the missing bridge from
the graph-facing normal-form fields to the lab's connected/cubic/bridgeless/
planar/simple-endpoint prefix checks.
-/
def ClosedCollarWindingFreedomSimplePatchN6NormalFormExcludesStructuralBlockers :
    Prop :=
  ∀ {V : Type} {G : SimpleGraph V}
    (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G)
    (classification :
      ClosedCollarWindingFreedomSimplePatchN6ExhaustiveLabClassification data),
      ¬ classification.structuralBlocker

/--
Finite-subclass Section 9.2 Step 4 repair target for six-internal simple
patches.  Once the exhaustive lab classifies every n6 normal-form
representation and the graph geometry rules out structural prefix blockers,
the remaining exact templates are excluded by cyclic five-edge-connectivity
and the residual post-template-exclusion pass count is zero.
-/
def Section92Step4N6ExhaustiveNormalFormObstructionTarget : Prop :=
  ClosedCollarWindingFreedomSimplePatchN6ExhaustiveBlockedAfterCyclicallyFiveTemplateExclusion →
    ClosedCollarWindingFreedomSimplePatchN6NormalFormClassifiedByExhaustiveLab →
      ClosedCollarWindingFreedomSimplePatchN6NormalFormExcludesStructuralBlockers →
        ∀ {V : Type} {G : SimpleGraph V},
          (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
            False

theorem section92Step4N6ExhaustiveNormalFormObstructionTarget :
    Section92Step4N6ExhaustiveNormalFormObstructionTarget := by
  intro _hexhaustive hclassified hnoStructural V G data
  rcases hclassified data with ⟨classification⟩
  rcases classification.hclassified with hstructural | hremaining
  · exact (hnoStructural data classification) hstructural
  · rcases hremaining with htemplate | hpass
    · rcases htemplate with ⟨candidate, hrealizes⟩
      exact
        closedCollarWindingFreedomNormalFormRealization_false_of_forcedTemplate
          data.normalForm candidate hrealizes
    · rcases hpass with ⟨labPass⟩
      exact closedCollarWindingFreedomSimplePatchN6_noLabNormalFormPass labPass

/--
Structural prefix blockers used by the n6 realization lab.  The names match
the lab's first-failed normal-form prefix checks.
-/
inductive ClosedCollarSimplePatchN6StructuralBlockerId where
  | connectedMultigraph
  | cubicMultigraph
  | bridgelessMultigraph
  | planarMultigraph
  | simpleEndpointRealization
  deriving DecidableEq, Repr

def ClosedCollarSimplePatchN6StructuralBlockerId.labName :
    ClosedCollarSimplePatchN6StructuralBlockerId → String
  | .connectedMultigraph => "connected_multigraph"
  | .cubicMultigraph => "cubic_multigraph"
  | .bridgelessMultigraph => "bridgeless_multigraph"
  | .planarMultigraph => "planar_multigraph"
  | .simpleEndpointRealization => "simple_endpoint_realization"

def closedCollarSimplePatchN6StructuralBlockerIds :
    List ClosedCollarSimplePatchN6StructuralBlockerId :=
  [.connectedMultigraph, .cubicMultigraph, .bridgelessMultigraph,
    .planarMultigraph, .simpleEndpointRealization]

/--
Detailed taxonomy counts from the exhaustive n6 artifact audit.  The first
800000 topologies are supplied by the structural-prefix slices; the remaining
1058980 topologies are supplied by the template-blocker slices.
-/
structure ClosedCollarSimplePatchN6DetailedTaxonomyCounts where
  internalVertexCount : Nat
  exactPatchTopologyCount : Nat
  structuralPrefixSliceFileCount : Nat
  templateBlockerSliceFileCount : Nat
  structuralPrefixEndIndex : Nat
  processedPatchTopologyCount : Nat
  radialOrderCaseCount : Nat
  profilePreservingCaseCount : Nat
  connectedStructuralBlockerCount : Nat
  cubicStructuralBlockerCount : Nat
  bridgelessStructuralBlockerCount : Nat
  planarStructuralBlockerCount : Nat
  simpleEndpointStructuralBlockerCount : Nat
  exactTemplateBlockerCount : Nat
  diagonalForwardTemplateCount : Nat
  diagonalReverseTemplateCount : Nat
  nonTemplateCyclicCutBlockerCount : Nat
  cap5LikeBlockerCount : Nat
  normalFormAfterTemplateExclusionPassingCount : Nat
  residualAfterStructuralAndExactTemplateCount : Nat

def closedCollarSimplePatchN6DetailedTaxonomyCounts :
    ClosedCollarSimplePatchN6DetailedTaxonomyCounts where
  internalVertexCount := 6
  exactPatchTopologyCount := closedCollarSimplePatchN6ExactPatchTopologyCount
  structuralPrefixSliceFileCount := 16
  templateBlockerSliceFileCount := 5
  structuralPrefixEndIndex := 800000
  processedPatchTopologyCount := 1858980
  radialOrderCaseCount := 3717960
  profilePreservingCaseCount := 29880
  connectedStructuralBlockerCount := 0
  cubicStructuralBlockerCount := 0
  bridgelessStructuralBlockerCount := 0
  planarStructuralBlockerCount := 27720
  simpleEndpointStructuralBlockerCount := 0
  exactTemplateBlockerCount := 2160
  diagonalForwardTemplateCount := 1080
  diagonalReverseTemplateCount := 1080
  nonTemplateCyclicCutBlockerCount := 0
  cap5LikeBlockerCount := 0
  normalFormAfterTemplateExclusionPassingCount := 0
  residualAfterStructuralAndExactTemplateCount := 0

def ClosedCollarSimplePatchN6StructuralBlockerId.countInDetailedTaxonomy :
    ClosedCollarSimplePatchN6StructuralBlockerId → Nat
  | .connectedMultigraph =>
      closedCollarSimplePatchN6DetailedTaxonomyCounts.connectedStructuralBlockerCount
  | .cubicMultigraph =>
      closedCollarSimplePatchN6DetailedTaxonomyCounts.cubicStructuralBlockerCount
  | .bridgelessMultigraph =>
      closedCollarSimplePatchN6DetailedTaxonomyCounts.bridgelessStructuralBlockerCount
  | .planarMultigraph =>
      closedCollarSimplePatchN6DetailedTaxonomyCounts.planarStructuralBlockerCount
  | .simpleEndpointRealization =>
      closedCollarSimplePatchN6DetailedTaxonomyCounts.simpleEndpointStructuralBlockerCount

/--
Artifact-backed detailed taxonomy for the exhaustive n6 simple-patch run:
every structural blocker counted by the archived verdicts is the
`planar_multigraph` prefix failure; all remaining profile-preserving cases are
the two exact diagonal templates, and no residual post-template-exclusion pass
remains.
-/
def ClosedCollarWindingFreedomSimplePatchN6DetailedTaxonomyArtifactEvidence :
    Prop :=
  ClosedCollarWindingFreedomWitnessRealizationData ∧
    closedCollarSimplePatchN6DetailedTaxonomyCounts.internalVertexCount = 6 ∧
    closedCollarSimplePatchN6DetailedTaxonomyCounts.exactPatchTopologyCount =
      closedCollarSimplePatchN6ExactPatchTopologyCount ∧
    closedCollarSimplePatchN6DetailedTaxonomyCounts.structuralPrefixSliceFileCount =
      16 ∧
    closedCollarSimplePatchN6DetailedTaxonomyCounts.templateBlockerSliceFileCount =
      closedCollarSimplePatchN6TemplateBlockerArchiveCounts.archivedSliceFileCount ∧
    closedCollarSimplePatchN6DetailedTaxonomyCounts.structuralPrefixEndIndex =
      closedCollarSimplePatchN6First800000StructuralCounts.processedPatchTopologyCount ∧
    closedCollarSimplePatchN6DetailedTaxonomyCounts.processedPatchTopologyCount =
      closedCollarSimplePatchN6AllTemplateBlockerCounts.processedPatchTopologyCount ∧
    closedCollarSimplePatchN6DetailedTaxonomyCounts.radialOrderCaseCount =
      closedCollarSimplePatchN6AllTemplateBlockerCounts.radialOrderCaseCount ∧
    closedCollarSimplePatchN6DetailedTaxonomyCounts.profilePreservingCaseCount =
      closedCollarSimplePatchN6AllTemplateBlockerCounts.profilePreservingCaseCount ∧
    closedCollarSimplePatchN6DetailedTaxonomyCounts.connectedStructuralBlockerCount =
      0 ∧
    closedCollarSimplePatchN6DetailedTaxonomyCounts.cubicStructuralBlockerCount =
      0 ∧
    closedCollarSimplePatchN6DetailedTaxonomyCounts.bridgelessStructuralBlockerCount =
      0 ∧
    closedCollarSimplePatchN6DetailedTaxonomyCounts.planarStructuralBlockerCount =
      closedCollarSimplePatchN6AllTemplateBlockerCounts.structuralFirstBlockerCount ∧
    closedCollarSimplePatchN6DetailedTaxonomyCounts.simpleEndpointStructuralBlockerCount =
      0 ∧
    closedCollarSimplePatchN6DetailedTaxonomyCounts.exactTemplateBlockerCount =
      closedCollarSimplePatchN6AllTemplateBlockerCounts.exactTemplateBlockerCount ∧
    closedCollarSimplePatchN6DetailedTaxonomyCounts.diagonalForwardTemplateCount =
      closedCollarSimplePatchN6AllTemplateBlockerCounts.diagonalForwardTemplateCount ∧
    closedCollarSimplePatchN6DetailedTaxonomyCounts.diagonalReverseTemplateCount =
      closedCollarSimplePatchN6AllTemplateBlockerCounts.diagonalReverseTemplateCount ∧
    closedCollarSimplePatchN6DetailedTaxonomyCounts.nonTemplateCyclicCutBlockerCount =
      0 ∧
    closedCollarSimplePatchN6DetailedTaxonomyCounts.cap5LikeBlockerCount =
      0 ∧
    closedCollarSimplePatchN6DetailedTaxonomyCounts.normalFormAfterTemplateExclusionPassingCount =
      0 ∧
    closedCollarSimplePatchN6DetailedTaxonomyCounts.residualAfterStructuralAndExactTemplateCount =
      0 ∧
    closedCollarSimplePatchN6DetailedTaxonomyCounts.connectedStructuralBlockerCount +
        closedCollarSimplePatchN6DetailedTaxonomyCounts.cubicStructuralBlockerCount +
          closedCollarSimplePatchN6DetailedTaxonomyCounts.bridgelessStructuralBlockerCount +
            closedCollarSimplePatchN6DetailedTaxonomyCounts.planarStructuralBlockerCount +
              closedCollarSimplePatchN6DetailedTaxonomyCounts.simpleEndpointStructuralBlockerCount =
      closedCollarSimplePatchN6AllTemplateBlockerCounts.structuralFirstBlockerCount ∧
    closedCollarSimplePatchN6DetailedTaxonomyCounts.diagonalForwardTemplateCount +
        closedCollarSimplePatchN6DetailedTaxonomyCounts.diagonalReverseTemplateCount =
      closedCollarSimplePatchN6DetailedTaxonomyCounts.exactTemplateBlockerCount ∧
    closedCollarSimplePatchN6DetailedTaxonomyCounts.planarStructuralBlockerCount +
        closedCollarSimplePatchN6DetailedTaxonomyCounts.exactTemplateBlockerCount +
          closedCollarSimplePatchN6DetailedTaxonomyCounts.residualAfterStructuralAndExactTemplateCount =
      closedCollarSimplePatchN6DetailedTaxonomyCounts.profilePreservingCaseCount ∧
    closedCollarSimplePatchN6First800000StructuralCounts.processedPatchTopologyCount +
        closedCollarSimplePatchN6TemplateBlockerArchiveCounts.processedPatchTopologyCount =
      closedCollarSimplePatchN6DetailedTaxonomyCounts.processedPatchTopologyCount

theorem closedCollarWindingFreedomSimplePatchN6DetailedTaxonomyArtifactEvidence :
    ClosedCollarWindingFreedomSimplePatchN6DetailedTaxonomyArtifactEvidence := by
  refine ⟨closedCollarWindingFreedomWitnessRealizationData, ?_⟩
  decide

/-- A positive structural-blocker case in the detailed n6 taxonomy. -/
structure ClosedCollarWindingFreedomSimplePatchN6DetailedStructuralBlockerCase where
  blocker : ClosedCollarSimplePatchN6StructuralBlockerId
  hpositive : 0 < blocker.countInDetailedTaxonomy

theorem closedCollarWindingFreedomSimplePatchN6DetailedStructuralBlockerCase_planar
    (candidate :
      ClosedCollarWindingFreedomSimplePatchN6DetailedStructuralBlockerCase) :
    candidate.blocker = ClosedCollarSimplePatchN6StructuralBlockerId.planarMultigraph := by
  rcases candidate with ⟨blocker, hpositive⟩
  cases blocker <;>
    simp [ClosedCollarSimplePatchN6StructuralBlockerId.countInDetailedTaxonomy,
      closedCollarSimplePatchN6DetailedTaxonomyCounts] at hpositive ⊢

/--
Normal-form field whose failure would explain a lab structural blocker.  This
is the explicit bridge obligation from graph-facing normal form to the lab's
prefix tests.
-/
def ClosedCollarSimplePatchN6StructuralBlockerId.excludedByNormalForm
    {G : SimpleGraph V}
    (blocker : ClosedCollarSimplePatchN6StructuralBlockerId)
    (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) :
    Prop :=
  match blocker with
  | .connectedMultigraph => data.normalForm.actualCollarEmbeddingConstraints
  | .cubicMultigraph => data.normalForm.cubicBridgelessTaitSetting
  | .bridgelessMultigraph => data.normalForm.cubicBridgelessTaitSetting
  | .planarMultigraph => data.normalForm.dualTriangulationNormalForm
  | .simpleEndpointRealization => data.normalForm.actualCollarEmbeddingConstraints

/--
A structural blocker is realized only if the corresponding normal-form field
fails.  Honest normal-form data carries proofs of those fields, so the
structural branch is impossible once the lab classification is aligned with
this predicate.
-/
def ClosedCollarSimplePatchN6StructuralBlockerId.RealizesAgainstNormalForm
    {G : SimpleGraph V}
    (blocker : ClosedCollarSimplePatchN6StructuralBlockerId)
    (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) :
    Prop :=
  ¬ blocker.excludedByNormalForm data

theorem closedCollarSimplePatchN6StructuralBlocker_not_realizesAgainstNormalForm
    {G : SimpleGraph V}
    (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G)
    (blocker : ClosedCollarSimplePatchN6StructuralBlockerId) :
    ¬ blocker.RealizesAgainstNormalForm data := by
  cases blocker <;> intro hblocker
  · exact hblocker data.normalForm.hactualCollarEmbeddingConstraints
  · exact hblocker data.normalForm.hcubicBridgelessTaitSetting
  · exact hblocker data.normalForm.hcubicBridgelessTaitSetting
  · exact hblocker data.normalForm.hdualTriangulationNormalForm
  · exact hblocker data.normalForm.hactualCollarEmbeddingConstraints

/--
The detailed n6 taxonomy sharpens the structural branch: any positive
structural blocker is the `planar_multigraph` prefix failure, so normal-form
data excludes it specifically through dual-triangulation normal form.
-/
theorem closedCollarWindingFreedomSimplePatchN6DetailedStructuralBlockerCase_not_realizesAgainstNormalForm
    {G : SimpleGraph V}
    (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G)
    (candidate :
      ClosedCollarWindingFreedomSimplePatchN6DetailedStructuralBlockerCase) :
    ¬ candidate.blocker.RealizesAgainstNormalForm data := by
  have hplanar :=
    closedCollarWindingFreedomSimplePatchN6DetailedStructuralBlockerCase_planar
      candidate
  rw [hplanar]
  intro hblocker
  exact hblocker data.normalForm.hdualTriangulationNormalForm

/--
Detailed exhaustive lab outcome for an honest n6 normal-form representation.
The structural branch records the exact lab prefix blocker and the normal-form
field whose failure would be required for that blocker to apply.
-/
inductive ClosedCollarWindingFreedomSimplePatchN6DetailedLabOutcome
    {V : Type} {G : SimpleGraph V}
    (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) where
  | structural
      (blocker : ClosedCollarSimplePatchN6StructuralBlockerId)
      (hrealizes : blocker.RealizesAgainstNormalForm data)
  | exactTemplate
      (candidate : ClosedCollarDiagonalTwoPoleTemplateCandidate G)
      (hrealizes : candidate.Realizes)
  | residualPass
      (pass : ClosedCollarWindingFreedomSimplePatchN6LabNormalFormPass G)

/--
Sharper coverage obligation from the exhaustive n6 lab: every graph-facing n6
normal-form representation receives a detailed lab outcome.
-/
def ClosedCollarWindingFreedomSimplePatchN6NormalFormDetailedClassifiedByExhaustiveLab :
    Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
      Nonempty
        (ClosedCollarWindingFreedomSimplePatchN6DetailedLabOutcome data)

/--
Sharper n6 finite-subclass obstruction target.  The detailed classification
already ties structural prefix blockers to violations of named normal-form
fields, so the only remaining coverage obligation is the exhaustive lab
classification itself.
-/
def Section92Step4N6DetailedNormalFormObstructionTarget : Prop :=
  ClosedCollarWindingFreedomSimplePatchN6ExhaustiveBlockedAfterCyclicallyFiveTemplateExclusion →
    ClosedCollarWindingFreedomSimplePatchN6NormalFormDetailedClassifiedByExhaustiveLab →
      ∀ {V : Type} {G : SimpleGraph V},
        (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
          False

theorem section92Step4N6DetailedNormalFormObstructionTarget :
    Section92Step4N6DetailedNormalFormObstructionTarget := by
  intro _hexhaustive hclassified V G data
  rcases hclassified data with ⟨outcome⟩
  cases outcome with
  | structural blocker hrealizes =>
      exact
        closedCollarSimplePatchN6StructuralBlocker_not_realizesAgainstNormalForm
          data blocker hrealizes
  | exactTemplate candidate hrealizes =>
      exact
        closedCollarWindingFreedomNormalFormRealization_false_of_forcedTemplate
          data.normalForm candidate hrealizes
  | residualPass pass =>
      exact closedCollarWindingFreedomSimplePatchN6_noLabNormalFormPass pass

/--
Artifact-taxonomy version of the exhaustive n6 lab outcome.  The structural
branch is not an arbitrary prefix failure; it must be a positive structural
blocker from the detailed taxonomy, which the audit proves is always the
planarity prefix failure.
-/
inductive ClosedCollarWindingFreedomSimplePatchN6TaxonomyLabOutcome
    {V : Type} {G : SimpleGraph V}
    (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) where
  | structural
      (candidate :
        ClosedCollarWindingFreedomSimplePatchN6DetailedStructuralBlockerCase)
      (hrealizes : candidate.blocker.RealizesAgainstNormalForm data)
  | exactTemplate
      (candidate : ClosedCollarDiagonalTwoPoleTemplateCandidate G)
      (hrealizes : candidate.Realizes)
  | residualPass
      (pass : ClosedCollarWindingFreedomSimplePatchN6LabNormalFormPass G)

/--
Sharper graph-facing coverage obligation for the exhaustive n6 artifact
taxonomy: every represented normal-form annulus is assigned either the unique
planarity-prefix structural branch, one of the two exact diagonal templates,
or a residual pass counted after template exclusion.
-/
def ClosedCollarWindingFreedomSimplePatchN6NormalFormClassifiedByDetailedTaxonomy :
    Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
      Nonempty
        (ClosedCollarWindingFreedomSimplePatchN6TaxonomyLabOutcome data)

/--
N6 finite-subclass obstruction target with the first exact blocker named:
the archived taxonomy reduces structural failures to the planarity prefix, so
normal form kills that branch through dual-triangulation normal form; cyclic
five-edge-connectivity kills exact templates; the residual pass count is zero.
-/
def Section92Step4N6PlanarityTemplateTaxonomyObstructionTarget : Prop :=
  ClosedCollarWindingFreedomSimplePatchN6DetailedTaxonomyArtifactEvidence →
    ClosedCollarWindingFreedomSimplePatchN6NormalFormClassifiedByDetailedTaxonomy →
      ∀ {V : Type} {G : SimpleGraph V},
        (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
          False

theorem section92Step4N6PlanarityTemplateTaxonomyObstructionTarget :
    Section92Step4N6PlanarityTemplateTaxonomyObstructionTarget := by
  intro _htaxonomy hclassified V G data
  rcases hclassified data with ⟨outcome⟩
  cases outcome with
  | structural blockerCase hrealizes =>
      exact
        closedCollarWindingFreedomSimplePatchN6DetailedStructuralBlockerCase_not_realizesAgainstNormalForm
          data blockerCase hrealizes
  | exactTemplate candidate hrealizes =>
      exact
        closedCollarWindingFreedomNormalFormRealization_false_of_forcedTemplate
          data.normalForm candidate hrealizes
  | residualPass pass =>
      exact closedCollarWindingFreedomSimplePatchN6_noLabNormalFormPass pass

/--
Coverage datum for the global normal-form repair path: an arbitrary honest
normal-form annular realization of the winding-freedom witness is represented
by one of the exhaustive n6 simple-patch cases and receives a detailed taxonomy
outcome from the archived lab.
-/
structure ClosedCollarWindingFreedomNormalFormN6DetailedTaxonomyCoverage
    {V : Type} {G : SimpleGraph V}
    (normalForm : ClosedCollarWindingFreedomNormalFormRealization G) where
  data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G
  normalForm_eq : data.normalForm = normalForm
  outcome : ClosedCollarWindingFreedomSimplePatchN6TaxonomyLabOutcome data

/--
First geometric sub-obligation for the n6 repair route: an honest normal-form
annular realization can be extracted as one of the enumerated six-internal
simple-patch representations.
-/
structure ClosedCollarWindingFreedomNormalFormN6RepresentationExtraction
    {V : Type} {G : SimpleGraph V}
    (normalForm : ClosedCollarWindingFreedomNormalFormRealization G) where
  data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G
  normalForm_eq : data.normalForm = normalForm

/--
First radial-face sub-obligation for n6 extraction: an honest normal-form
annulus has the cut-open radial-face datum needed by the finite embedding
lab.
-/
structure ClosedCollarWindingFreedomNormalFormRadialFaceExtraction
    {V : Type} {G : SimpleGraph V}
    (normalForm : ClosedCollarWindingFreedomNormalFormRealization G) where
  normalFormRadialFace : ClosedCollarWindingFreedomNormalFormRadialFaceRealization G
  normalForm_eq : normalFormRadialFace.normalForm = normalForm

/--
Second radial-face sub-obligation: a normal-form annulus with its cut-open
radial-face datum has one of the enumerated n6 simple-patch representations.
-/
structure ClosedCollarWindingFreedomRadialFaceN6RepresentationExtraction
    {V : Type} {G : SimpleGraph V}
    (normalFormRadialFace :
      ClosedCollarWindingFreedomNormalFormRadialFaceRealization G) where
  data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRadialFaceRepresentation G
  normalFormRadialFace_eq : data.normalFormRadialFace = normalFormRadialFace

/--
Global extraction theorem needed before the finite taxonomy can apply: every
honest normal-form annulus for the winding-freedom witness has an n6
simple-patch representation.
-/
def ClosedCollarWindingFreedomEveryNormalFormHasN6Representation :
    Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    (normalForm : ClosedCollarWindingFreedomNormalFormRealization G) →
      Nonempty
        (ClosedCollarWindingFreedomNormalFormN6RepresentationExtraction normalForm)

/-- Every honest normal-form annulus supplies a cut-open radial-face datum. -/
def ClosedCollarWindingFreedomEveryNormalFormHasRadialFace :
    Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    (normalForm : ClosedCollarWindingFreedomNormalFormRealization G) →
      Nonempty
        (ClosedCollarWindingFreedomNormalFormRadialFaceExtraction normalForm)

/--
Actual-collar source for radial-face existence: the normal-form field
`actualCollarEmbeddingConstraints` is the intended geometric datum from which
the cut-open collar face must be extracted.
-/
def ClosedCollarWindingFreedomActualCollarEmbeddingForcesRadialFace :
    Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    (normalForm : ClosedCollarWindingFreedomNormalFormRealization G) →
      normalForm.actualCollarEmbeddingConstraints →
        ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
          normalForm.annular

/--
Edge support of an existing planar annulus-collar geometry, restricted to the
faces in the collar layers.  This is the bridge from the project-wide
embedding API to the graph-edge support stored by the winding realization
interface.
-/
def closedCollarActualCollarGeometryEdgeSupport
    {V : Type} [DecidableEq V] {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (collarGeometry : PlanarBoundaryAnnulusCollarGeometry emb) :
    Finset G.edgeSet :=
  (Finset.univ.biUnion collarGeometry.collarFaces).biUnion
    (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)

/--
Embedded collar geometry extracted from an honest normal-form realization,
before choosing the cut-open radial face.  This separates the planar
annulus-collar support equalities from the later face-selection obligation.
-/
structure ClosedCollarWindingFreedomActualCollarEmbeddingGeometryData
    {V : Type} [DecidableEq V] {G : SimpleGraph V}
    (normalForm : ClosedCollarWindingFreedomNormalFormRealization G) where
  emb : PlaneEmbeddingWithBoundary G
  collarGeometry : PlanarBoundaryAnnulusCollarGeometry emb
  collarEdges_eq :
    normalForm.annular.collarEdges =
      closedCollarActualCollarGeometryEdgeSupport collarGeometry
  outerBoundaryEdges_eq :
    normalForm.annular.outerBoundaryEdges = collarGeometry.outerAmbientBoundary

/--
Stronger repaired annulus-geometry source for the winding realization bridge.
The project-wide previous-boundary witness geometry records the missing
placement condition for positive collar layers; this structure pins that
stronger surface to the winding witness support equalities.
-/
structure ClosedCollarWindingFreedomActualCollarEmbeddingPreviousBoundaryGeometryData
    {V : Type} [DecidableEq V] {G : SimpleGraph V}
    (normalForm : ClosedCollarWindingFreedomNormalFormRealization G) where
  emb : PlaneEmbeddingWithBoundary G
  previousGeometry : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb
  collarEdges_eq :
    normalForm.annular.collarEdges =
      closedCollarActualCollarGeometryEdgeSupport
        previousGeometry.toPlanarBoundaryAnnulusCollarGeometry
  outerBoundaryEdges_eq :
    normalForm.annular.outerBoundaryEdges =
      previousGeometry.toPlanarBoundaryAnnulusCollarGeometry.outerAmbientBoundary

def ClosedCollarWindingFreedomActualCollarEmbeddingPreviousBoundaryGeometryData.toGeometryData
    {V : Type} [DecidableEq V] {G : SimpleGraph V}
    {normalForm : ClosedCollarWindingFreedomNormalFormRealization G}
    (data :
      ClosedCollarWindingFreedomActualCollarEmbeddingPreviousBoundaryGeometryData
        normalForm) :
    ClosedCollarWindingFreedomActualCollarEmbeddingGeometryData normalForm where
  emb := data.emb
  collarGeometry :=
    data.previousGeometry.toPlanarBoundaryAnnulusCollarGeometry
  collarEdges_eq := data.collarEdges_eq
  outerBoundaryEdges_eq := data.outerBoundaryEdges_eq

/--
Cut-open radial face extracted from already identified embedded collar
geometry.  This is the second geometric obligation needed by the finite n6
taxonomy route.
-/
structure ClosedCollarWindingFreedomActualCollarGeometryRadialFaceExtraction
    {V : Type} [DecidableEq V] {G : SimpleGraph V}
    {normalForm : ClosedCollarWindingFreedomNormalFormRealization G}
    (geometry :
      ClosedCollarWindingFreedomActualCollarEmbeddingGeometryData normalForm) where
  cutOpenFace : AmbientFace geometry.emb.faces
  cutOpenFace_mem_collar :
    ∃ i : Fin geometry.collarGeometry.numCollars,
      cutOpenFace ∈ geometry.collarGeometry.collarFaces i
  radialCut_subset_cutOpenFaceBoundary :
    normalForm.annular.radialCut ⊆ geometry.emb.faceBoundary cutOpenFace.1
  cutOpenFaceIsCutOpenCollarFace : Prop
  hcutOpenFace : cutOpenFaceIsCutOpenCollarFace

/--
Concrete embedded-collar certificate for the radial-face bridge.  It ties an
abstract winding normal-form realization to the existing planar annulus-collar
geometry layer, identifies the same collar edge support, and supplies the
specific cut-open collar face whose boundary contains the radial cut.
-/
structure ClosedCollarWindingFreedomActualCollarEmbeddingRadialFaceData
    {V : Type} [DecidableEq V] {G : SimpleGraph V}
    (normalForm : ClosedCollarWindingFreedomNormalFormRealization G) where
  emb : PlaneEmbeddingWithBoundary G
  collarGeometry : PlanarBoundaryAnnulusCollarGeometry emb
  collarEdges_eq :
    normalForm.annular.collarEdges =
      closedCollarActualCollarGeometryEdgeSupport collarGeometry
  outerBoundaryEdges_eq :
    normalForm.annular.outerBoundaryEdges = collarGeometry.outerAmbientBoundary
  cutOpenFace : AmbientFace emb.faces
  cutOpenFace_mem_collar :
    ∃ i : Fin collarGeometry.numCollars,
      cutOpenFace ∈ collarGeometry.collarFaces i
  radialCut_subset_cutOpenFaceBoundary :
    normalForm.annular.radialCut ⊆ emb.faceBoundary cutOpenFace.1
  cutOpenFaceIsCutOpenCollarFace : Prop
  hcutOpenFace : cutOpenFaceIsCutOpenCollarFace

def ClosedCollarWindingFreedomActualCollarEmbeddingRadialFaceData.ofGeometryExtraction
    {V : Type} [DecidableEq V] {G : SimpleGraph V}
    {normalForm : ClosedCollarWindingFreedomNormalFormRealization G}
    (geometry :
      ClosedCollarWindingFreedomActualCollarEmbeddingGeometryData normalForm)
    (radialFace :
      ClosedCollarWindingFreedomActualCollarGeometryRadialFaceExtraction
        geometry) :
    ClosedCollarWindingFreedomActualCollarEmbeddingRadialFaceData
      normalForm where
  emb := geometry.emb
  collarGeometry := geometry.collarGeometry
  collarEdges_eq := geometry.collarEdges_eq
  outerBoundaryEdges_eq := geometry.outerBoundaryEdges_eq
  cutOpenFace := radialFace.cutOpenFace
  cutOpenFace_mem_collar := radialFace.cutOpenFace_mem_collar
  radialCut_subset_cutOpenFaceBoundary :=
    radialFace.radialCut_subset_cutOpenFaceBoundary
  cutOpenFaceIsCutOpenCollarFace :=
    radialFace.cutOpenFaceIsCutOpenCollarFace
  hcutOpenFace := radialFace.hcutOpenFace

/--
Data-level version of the actual-collar bridge: the embedded collar
constraints must produce the concrete radial-face certificate above.
-/
def ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesRadialFaceData :
    Prop :=
  ∀ {V : Type} [DecidableEq V] {G : SimpleGraph V},
    (normalForm : ClosedCollarWindingFreedomNormalFormRealization G) →
      normalForm.actualCollarEmbeddingConstraints →
        Nonempty
          (ClosedCollarWindingFreedomActualCollarEmbeddingRadialFaceData
            normalForm)

/--
First factored data obligation: actual collar constraints produce embedded
annulus-collar geometry with the normal-form support equalities.
-/
def ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesGeometryData :
    Prop :=
  ∀ {V : Type} [DecidableEq V] {G : SimpleGraph V},
    (normalForm : ClosedCollarWindingFreedomNormalFormRealization G) →
      normalForm.actualCollarEmbeddingConstraints →
        Nonempty
          (ClosedCollarWindingFreedomActualCollarEmbeddingGeometryData
            normalForm)

/--
Stronger geometry-data obligation: actual collar constraints supply the
repaired previous-boundary witness annulus geometry, not merely the weaker
collar-geometry shell.
-/
def ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesPreviousBoundaryGeometryData :
    Prop :=
  ∀ {V : Type} [DecidableEq V] {G : SimpleGraph V},
    (normalForm : ClosedCollarWindingFreedomNormalFormRealization G) →
      normalForm.actualCollarEmbeddingConstraints →
        Nonempty
          (ClosedCollarWindingFreedomActualCollarEmbeddingPreviousBoundaryGeometryData
            normalForm)

theorem closedCollarWindingFreedomActualCollarEmbeddingSuppliesGeometryData_of_previousBoundaryGeometryData
    (hgeometry :
      ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesPreviousBoundaryGeometryData) :
    ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesGeometryData := by
  intro V _hV G normalForm hactual
  rcases hgeometry normalForm hactual with ⟨previousData⟩
  exact ⟨previousData.toGeometryData⟩

/--
Second factored data obligation: once the embedded collar geometry is known,
it supplies the cut-open radial face used by the normal-form n6 extraction.
-/
def ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction :
    Prop :=
  ∀ {V : Type} [DecidableEq V] {G : SimpleGraph V}
    {normalForm : ClosedCollarWindingFreedomNormalFormRealization G},
      (geometry :
        ClosedCollarWindingFreedomActualCollarEmbeddingGeometryData
          normalForm) →
        Nonempty
          (ClosedCollarWindingFreedomActualCollarGeometryRadialFaceExtraction
            geometry)

theorem closedCollarWindingFreedomActualCollarEmbeddingSuppliesRadialFaceData_of_geometry_of_radialFace
    (hgeometry :
      ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesGeometryData)
    (hradial :
      ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction) :
    ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesRadialFaceData := by
  intro V _hV G normalForm hactual
  rcases hgeometry normalForm hactual with ⟨geometry⟩
  rcases hradial geometry with ⟨radialFace⟩
  exact
    ⟨ClosedCollarWindingFreedomActualCollarEmbeddingRadialFaceData.ofGeometryExtraction
      geometry radialFace⟩

theorem closedCollarWindingFreedomActualCollarEmbeddingForcesRadialFace_of_suppliesRadialFaceData
    (hdata :
      ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesRadialFaceData) :
    ClosedCollarWindingFreedomActualCollarEmbeddingForcesRadialFace := by
  classical
  intro V G normalForm hactual
  rcases hdata normalForm hactual with ⟨data⟩
  exact
    ⟨{
      faceEdges := data.emb.faceBoundary data.cutOpenFace.1
      isCutOpenCollarFace := data.cutOpenFaceIsCutOpenCollarFace
      hface := data.hcutOpenFace
      radialCut_subset_faceEdges := data.radialCut_subset_cutOpenFaceBoundary
    }⟩

theorem closedCollarWindingFreedomEveryNormalFormHasRadialFace_of_actualCollarEmbeddingForcesRadialFace
    (hactual : ClosedCollarWindingFreedomActualCollarEmbeddingForcesRadialFace) :
    ClosedCollarWindingFreedomEveryNormalFormHasRadialFace := by
  intro V G normalForm
  rcases hactual normalForm normalForm.hactualCollarEmbeddingConstraints with
    ⟨radialFace⟩
  exact
    ⟨⟨
      { normalForm := normalForm
        radialFace := radialFace },
      rfl
    ⟩⟩

/--
Every cut-open radial-face normal-form annulus is represented by an n6
simple-patch case.
-/
def ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasN6Representation :
    Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    (normalFormRadialFace :
      ClosedCollarWindingFreedomNormalFormRadialFaceRealization G) →
      Nonempty
        (ClosedCollarWindingFreedomRadialFaceN6RepresentationExtraction
          normalFormRadialFace)

/--
The n6 extraction bridge factors through the cut-open radial-face geometry:
first get the radial face from normal form, then represent that radial-face
annulus by an enumerated n6 simple patch.
-/
theorem closedCollarWindingFreedomEveryNormalFormHasN6Representation_of_radialFace_of_radialFaceN6
    (hradial : ClosedCollarWindingFreedomEveryNormalFormHasRadialFace)
    (hn6 :
      ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasN6Representation) :
    ClosedCollarWindingFreedomEveryNormalFormHasN6Representation := by
  intro V G normalForm
  rcases hradial normalForm with ⟨radialExtraction⟩
  rcases hn6 radialExtraction.normalFormRadialFace with ⟨n6Extraction⟩
  let data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G :=
    { normalForm := n6Extraction.data.normalFormRadialFace.normalForm
      representation := n6Extraction.data.representation
      annular_eq := n6Extraction.data.annular_eq.symm }
  refine ⟨⟨data, ?_⟩⟩
  dsimp [data]
  rw [n6Extraction.normalFormRadialFace_eq, radialExtraction.normalForm_eq]

/--
The exact remaining geometric bridge for the n6 repair route: every honest
normal-form annular realization of the winding-freedom witness is covered by
the exhaustive n6 detailed taxonomy.
-/
def ClosedCollarWindingFreedomEveryNormalFormCoveredByN6DetailedTaxonomy :
    Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    (normalForm : ClosedCollarWindingFreedomNormalFormRealization G) →
      Nonempty
        (ClosedCollarWindingFreedomNormalFormN6DetailedTaxonomyCoverage normalForm)

/--
The monolithic n6 coverage bridge factors into two serious obligations:
extract an n6 representation from the honest normal-form annulus, and classify
that representation by the exhaustive detailed taxonomy.
-/
theorem closedCollarWindingFreedomEveryNormalFormCoveredByN6DetailedTaxonomy_of_extraction_of_classification
    (hextract : ClosedCollarWindingFreedomEveryNormalFormHasN6Representation)
    (hclassified :
      ClosedCollarWindingFreedomSimplePatchN6NormalFormClassifiedByDetailedTaxonomy) :
    ClosedCollarWindingFreedomEveryNormalFormCoveredByN6DetailedTaxonomy := by
  intro V G normalForm
  rcases hextract normalForm with ⟨extraction⟩
  rcases hclassified extraction.data with ⟨outcome⟩
  exact
    ⟨⟨extraction.data, extraction.normalForm_eq, outcome⟩⟩

/--
Global repair-side consequence of the n6 detailed taxonomy bridge.  Once every
honest normal-form realization is shown to fall into the exhaustive n6
taxonomy, the structural branch is a planarity-prefix failure, the exact
template branch is excluded by cyclic five-edge-connectivity, and the residual
post-template-exclusion branch is empty.
-/
def ClosedCollarWindingFreedomNonrealizableInNormalFormByN6DetailedTaxonomy :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6DetailedTaxonomyArtifactEvidence →
    ClosedCollarWindingFreedomEveryNormalFormCoveredByN6DetailedTaxonomy →
      ClosedCollarWindingFreedomNonrealizableInNormalForm

theorem closedCollarWindingFreedomNonrealizableInNormalFormByN6DetailedTaxonomy :
    ClosedCollarWindingFreedomNonrealizableInNormalFormByN6DetailedTaxonomy := by
  intro _htaxonomy hcovered V G normalForm
  rcases hcovered normalForm with ⟨coverage⟩
  cases coverage.outcome with
  | structural blockerCase hrealizes =>
      exact
        closedCollarWindingFreedomSimplePatchN6DetailedStructuralBlockerCase_not_realizesAgainstNormalForm
          coverage.data blockerCase hrealizes
  | exactTemplate candidate hrealizes =>
      exact
        closedCollarWindingFreedomNormalFormRealization_false_of_forcedTemplate
          coverage.data.normalForm candidate hrealizes
  | residualPass pass =>
      exact closedCollarWindingFreedomSimplePatchN6_noLabNormalFormPass pass

/--
Repaired Section 9.2 Step 4 target exposed by the n6 realization audit:
residual per-component winding freedom is killed by the normal-form regime if
the geometric coverage theorem reduces every honest normal-form annulus to the
exhaustive n6 detailed taxonomy.
-/
def Section92Step4RepairedByN6DetailedTaxonomyTarget : Prop :=
  ClosedCollarWindingFreedomEveryNormalFormCoveredByN6DetailedTaxonomy →
    ClosedCollarWindingFreedomNonrealizableInNormalForm

theorem section92Step4RepairedByN6DetailedTaxonomyTarget :
    Section92Step4RepairedByN6DetailedTaxonomyTarget := by
  intro hcovered
  exact
    closedCollarWindingFreedomNonrealizableInNormalFormByN6DetailedTaxonomy
      closedCollarWindingFreedomSimplePatchN6DetailedTaxonomyArtifactEvidence
      hcovered

/--
Factored repaired target for Section 9.2 Step 4: prove n6 extraction for every
honest normal-form annulus, then prove the extracted representations are
classified by the detailed taxonomy.
-/
def Section92Step4RepairedByN6ExtractionAndTaxonomyTarget : Prop :=
  ClosedCollarWindingFreedomEveryNormalFormHasN6Representation →
    ClosedCollarWindingFreedomSimplePatchN6NormalFormClassifiedByDetailedTaxonomy →
      ClosedCollarWindingFreedomNonrealizableInNormalForm

theorem section92Step4RepairedByN6ExtractionAndTaxonomyTarget :
    Section92Step4RepairedByN6ExtractionAndTaxonomyTarget := by
  intro hextract hclassified
  exact
    section92Step4RepairedByN6DetailedTaxonomyTarget
      (closedCollarWindingFreedomEveryNormalFormCoveredByN6DetailedTaxonomy_of_extraction_of_classification
        hextract hclassified)

/--
Radial-face factored repaired target: prove radial-face existence, prove n6
representation for radial-face normal-form annuli, then classify the extracted
n6 representations by the detailed taxonomy.
-/
def Section92Step4RepairedByRadialFaceN6ExtractionAndTaxonomyTarget : Prop :=
  ClosedCollarWindingFreedomEveryNormalFormHasRadialFace →
    ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasN6Representation →
      ClosedCollarWindingFreedomSimplePatchN6NormalFormClassifiedByDetailedTaxonomy →
        ClosedCollarWindingFreedomNonrealizableInNormalForm

theorem section92Step4RepairedByRadialFaceN6ExtractionAndTaxonomyTarget :
    Section92Step4RepairedByRadialFaceN6ExtractionAndTaxonomyTarget := by
  intro hradial hn6 hclassified
  exact
    section92Step4RepairedByN6ExtractionAndTaxonomyTarget
      (closedCollarWindingFreedomEveryNormalFormHasN6Representation_of_radialFace_of_radialFaceN6
        hradial hn6)
      hclassified

/--
Actual-collar factored repaired target: prove the embedded collar constraints
force the radial-face datum, prove n6 representation for radial-face
normal-form annuli, then classify the extracted n6 representations by the
detailed taxonomy.
-/
def Section92Step4RepairedByActualCollarEmbeddingN6TaxonomyTarget : Prop :=
  ClosedCollarWindingFreedomActualCollarEmbeddingForcesRadialFace →
    ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasN6Representation →
      ClosedCollarWindingFreedomSimplePatchN6NormalFormClassifiedByDetailedTaxonomy →
        ClosedCollarWindingFreedomNonrealizableInNormalForm

theorem section92Step4RepairedByActualCollarEmbeddingN6TaxonomyTarget :
    Section92Step4RepairedByActualCollarEmbeddingN6TaxonomyTarget := by
  intro hactual hn6 hclassified
  exact
    section92Step4RepairedByRadialFaceN6ExtractionAndTaxonomyTarget
      (closedCollarWindingFreedomEveryNormalFormHasRadialFace_of_actualCollarEmbeddingForcesRadialFace
        hactual)
      hn6 hclassified

/--
Embedded-collar factored repaired target: extract the concrete radial-face
certificate from actual planar annulus-collar geometry, then use the
radial-face n6 extraction and detailed taxonomy.
-/
def Section92Step4RepairedByEmbeddedCollarN6TaxonomyTarget : Prop :=
  ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesRadialFaceData →
    ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasN6Representation →
      ClosedCollarWindingFreedomSimplePatchN6NormalFormClassifiedByDetailedTaxonomy →
        ClosedCollarWindingFreedomNonrealizableInNormalForm

theorem section92Step4RepairedByEmbeddedCollarN6TaxonomyTarget :
    Section92Step4RepairedByEmbeddedCollarN6TaxonomyTarget := by
  intro hdata hn6 hclassified
  exact
    section92Step4RepairedByActualCollarEmbeddingN6TaxonomyTarget
      (closedCollarWindingFreedomActualCollarEmbeddingForcesRadialFace_of_suppliesRadialFaceData
        hdata)
      hn6 hclassified

/--
A concrete embedded geometry-only realization of the winding-freedom witness:
normal-form data together with the planar annulus-collar geometry and support
equalities, before selecting the cut-open radial face.
-/
structure ClosedCollarWindingFreedomEmbeddedGeometryNormalFormRealization
    {V : Type} [DecidableEq V] (G : SimpleGraph V) where
  normalForm : ClosedCollarWindingFreedomNormalFormRealization G
  geometryData :
    ClosedCollarWindingFreedomActualCollarEmbeddingGeometryData normalForm

/--
Extraction datum tying a concrete geometry-only embedded certificate back to
the specific normal-form annulus being refuted.
-/
structure ClosedCollarWindingFreedomEmbeddedGeometryNormalFormExtraction
    {V : Type} [DecidableEq V] {G : SimpleGraph V}
    (normalForm : ClosedCollarWindingFreedomNormalFormRealization G) where
  embedded : ClosedCollarWindingFreedomEmbeddedGeometryNormalFormRealization G
  normalForm_eq : embedded.normalForm = normalForm

/--
Global geometry extraction obligation from arbitrary normal-form annuli to the
concrete embedded collar geometry certificate for that same annulus.
-/
def ClosedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization :
    Prop :=
  ∀ {V : Type} [DecidableEq V] {G : SimpleGraph V},
    (normalForm : ClosedCollarWindingFreedomNormalFormRealization G) →
      Nonempty
        (ClosedCollarWindingFreedomEmbeddedGeometryNormalFormExtraction
          normalForm)

theorem closedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization_of_suppliesGeometryData
    (hgeometry :
      ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesGeometryData) :
    ClosedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization := by
  intro V _hV G normalForm
  rcases hgeometry normalForm normalForm.hactualCollarEmbeddingConstraints with
    ⟨geometryData⟩
  exact
    ⟨{
      embedded :=
        { normalForm := normalForm
          geometryData := geometryData }
      normalForm_eq := rfl
    }⟩

/--
A concrete embedded normal-form realization of the winding-freedom witness:
normal-form data together with the embedded collar radial-face certificate
extracted from actual planar annulus-collar geometry.
-/
structure ClosedCollarWindingFreedomEmbeddedCollarNormalFormRealization
    {V : Type} [DecidableEq V] (G : SimpleGraph V) where
  normalForm : ClosedCollarWindingFreedomNormalFormRealization G
  radialFaceData :
    ClosedCollarWindingFreedomActualCollarEmbeddingRadialFaceData normalForm

def ClosedCollarWindingFreedomEmbeddedCollarNormalFormRealization.toNormalFormRadialFaceRealization
    {V : Type} [DecidableEq V] {G : SimpleGraph V}
    (data : ClosedCollarWindingFreedomEmbeddedCollarNormalFormRealization G) :
    ClosedCollarWindingFreedomNormalFormRadialFaceRealization G where
  normalForm := data.normalForm
  radialFace :=
    { faceEdges := data.radialFaceData.emb.faceBoundary data.radialFaceData.cutOpenFace.1
      isCutOpenCollarFace := data.radialFaceData.cutOpenFaceIsCutOpenCollarFace
      hface := data.radialFaceData.hcutOpenFace
      radialCut_subset_faceEdges :=
        data.radialFaceData.radialCut_subset_cutOpenFaceBoundary }

def ClosedCollarWindingFreedomNoEmbeddedCollarNormalFormRealization : Prop :=
  ∀ {V : Type} [DecidableEq V] {G : SimpleGraph V},
    ClosedCollarWindingFreedomEmbeddedCollarNormalFormRealization G → False

/--
Extraction datum tying a concrete embedded-collar certificate back to the
specific normal-form annulus being refuted.
-/
structure ClosedCollarWindingFreedomEmbeddedCollarNormalFormExtraction
    {V : Type} [DecidableEq V] {G : SimpleGraph V}
    (normalForm : ClosedCollarWindingFreedomNormalFormRealization G) where
  embedded : ClosedCollarWindingFreedomEmbeddedCollarNormalFormRealization G
  normalForm_eq : embedded.normalForm = normalForm

/--
Global extraction obligation from arbitrary normal-form annuli to the concrete
embedded-collar certificate for that same annulus.  This is the serious
geometric theorem still needed to turn the certified embedded obstruction into
full normal-form nonrealizability.
-/
def ClosedCollarWindingFreedomEveryNormalFormHasEmbeddedCollarRealization :
    Prop :=
  ∀ {V : Type} [DecidableEq V] {G : SimpleGraph V},
    (normalForm : ClosedCollarWindingFreedomNormalFormRealization G) →
      Nonempty
        (ClosedCollarWindingFreedomEmbeddedCollarNormalFormExtraction
          normalForm)

theorem closedCollarWindingFreedomEveryNormalFormHasEmbeddedCollarRealization_of_suppliesRadialFaceData
    (hdata :
      ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesRadialFaceData) :
    ClosedCollarWindingFreedomEveryNormalFormHasEmbeddedCollarRealization := by
  intro V _hV G normalForm
  rcases hdata normalForm normalForm.hactualCollarEmbeddingConstraints with
    ⟨radialFaceData⟩
  exact
    ⟨{
      embedded :=
        { normalForm := normalForm
          radialFaceData := radialFaceData }
      normalForm_eq := rfl
    }⟩

theorem closedCollarWindingFreedomEveryNormalFormHasEmbeddedCollarRealization_of_geometryExtraction_of_radialFace
    (hextract :
      ClosedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization)
    (hradial :
      ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction) :
    ClosedCollarWindingFreedomEveryNormalFormHasEmbeddedCollarRealization := by
  intro V _hV G normalForm
  rcases hextract normalForm with ⟨geometryExtraction⟩
  rcases geometryExtraction with ⟨embeddedGeometry, hnormalForm⟩
  cases hnormalForm
  rcases hradial embeddedGeometry.geometryData with ⟨radialFace⟩
  exact
    ⟨{
      embedded :=
        { normalForm := embeddedGeometry.normalForm
          radialFaceData :=
            ClosedCollarWindingFreedomActualCollarEmbeddingRadialFaceData.ofGeometryExtraction
              embeddedGeometry.geometryData radialFace }
      normalForm_eq := rfl
    }⟩

theorem closedCollarWindingFreedomEveryNormalFormHasRadialFace_of_embeddedCollarExtraction
    (hextract :
      ClosedCollarWindingFreedomEveryNormalFormHasEmbeddedCollarRealization) :
    ClosedCollarWindingFreedomEveryNormalFormHasRadialFace := by
  classical
  intro V G normalForm
  rcases hextract normalForm with ⟨extraction⟩
  let normalFormRadialFace :=
    extraction.embedded.toNormalFormRadialFaceRealization
  exact
    ⟨{
      normalFormRadialFace := normalFormRadialFace
      normalForm_eq := extraction.normalForm_eq
    }⟩

theorem closedCollarWindingFreedomEveryNormalFormHasRadialFace_of_embeddedGeometryExtraction_of_radialFace
    (hextract :
      ClosedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization)
    (hradial :
      ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction) :
    ClosedCollarWindingFreedomEveryNormalFormHasRadialFace :=
  closedCollarWindingFreedomEveryNormalFormHasRadialFace_of_embeddedCollarExtraction
    (closedCollarWindingFreedomEveryNormalFormHasEmbeddedCollarRealization_of_geometryExtraction_of_radialFace
      hextract hradial)

theorem closedCollarWindingFreedomEveryNormalFormHasRadialFace_of_geometryData_of_radialFaceExtraction
    (hgeometry :
      ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesGeometryData)
    (hradial :
      ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction) :
    ClosedCollarWindingFreedomEveryNormalFormHasRadialFace :=
  closedCollarWindingFreedomEveryNormalFormHasRadialFace_of_embeddedGeometryExtraction_of_radialFace
    (closedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization_of_suppliesGeometryData
      hgeometry)
    hradial

theorem closedCollarWindingFreedomEmbeddedCollarNormalFormRealization_false_of_radialFaceN6_of_classification
    (hn6 :
      ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasN6Representation)
    (hclassified :
      ClosedCollarWindingFreedomSimplePatchN6NormalFormClassifiedByDetailedTaxonomy)
    {V : Type} [DecidableEq V] {G : SimpleGraph V}
    (embedded :
      ClosedCollarWindingFreedomEmbeddedCollarNormalFormRealization G) :
    False := by
  let radialFace :=
    embedded.toNormalFormRadialFaceRealization
  rcases hn6 radialFace with ⟨n6Extraction⟩
  let data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G :=
    { normalForm := n6Extraction.data.normalFormRadialFace.normalForm
      representation := n6Extraction.data.representation
      annular_eq := n6Extraction.data.annular_eq.symm }
  rcases hclassified data with ⟨outcome⟩
  cases outcome with
  | structural blockerCase hrealizes =>
      exact
        closedCollarWindingFreedomSimplePatchN6DetailedStructuralBlockerCase_not_realizesAgainstNormalForm
          data blockerCase hrealizes
  | exactTemplate candidate hrealizes =>
      exact
        closedCollarWindingFreedomNormalFormRealization_false_of_forcedTemplate
          data.normalForm candidate hrealizes
  | residualPass pass =>
      exact closedCollarWindingFreedomSimplePatchN6_noLabNormalFormPass pass

/--
Certified embedded-collar repaired target: once radial-face normal-form annuli
extract to n6 representations and those representations are classified by the
detailed taxonomy, no concrete embedded normal-form realization of the
winding-freedom witness remains.
-/
def Section92Step4RepairedByCertifiedEmbeddedCollarN6TaxonomyTarget :
    Prop :=
  ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasN6Representation →
    ClosedCollarWindingFreedomSimplePatchN6NormalFormClassifiedByDetailedTaxonomy →
      ClosedCollarWindingFreedomNoEmbeddedCollarNormalFormRealization

theorem section92Step4RepairedByCertifiedEmbeddedCollarN6TaxonomyTarget :
    Section92Step4RepairedByCertifiedEmbeddedCollarN6TaxonomyTarget := by
  intro hn6 hclassified V _hV G embedded
  exact
    closedCollarWindingFreedomEmbeddedCollarNormalFormRealization_false_of_radialFaceN6_of_classification
      hn6 hclassified embedded

theorem closedCollarWindingFreedomNonrealizableInNormalForm_of_embeddedCollarExtraction_of_noEmbeddedCollar
    (hextract :
      ClosedCollarWindingFreedomEveryNormalFormHasEmbeddedCollarRealization)
    (hno :
      ClosedCollarWindingFreedomNoEmbeddedCollarNormalFormRealization) :
    ClosedCollarWindingFreedomNonrealizableInNormalForm := by
  intro V G normalForm
  classical
  rcases hextract normalForm with ⟨extraction⟩
  exact hno extraction.embedded

/--
Embedded-collar extraction repaired target: once every honest normal-form
annulus produces the certified embedded collar realization, radial-face n6
extraction plus detailed taxonomy refutes all such normal-form realizations.
-/
def Section92Step4RepairedByEmbeddedCollarExtractionN6TaxonomyTarget :
    Prop :=
  ClosedCollarWindingFreedomEveryNormalFormHasEmbeddedCollarRealization →
    ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasN6Representation →
      ClosedCollarWindingFreedomSimplePatchN6NormalFormClassifiedByDetailedTaxonomy →
        ClosedCollarWindingFreedomNonrealizableInNormalForm

theorem section92Step4RepairedByEmbeddedCollarExtractionN6TaxonomyTarget :
    Section92Step4RepairedByEmbeddedCollarExtractionN6TaxonomyTarget := by
  intro hextract hn6 hclassified
  exact
    closedCollarWindingFreedomNonrealizableInNormalForm_of_embeddedCollarExtraction_of_noEmbeddedCollar
      hextract
      (section92Step4RepairedByCertifiedEmbeddedCollarN6TaxonomyTarget
        hn6 hclassified)

/--
Embedded-geometry extraction repaired target: once every honest normal-form
annulus produces the embedded collar geometry, extracting the cut-open radial
face from that geometry reduces to the identity-preserving embedded-collar
extraction target.
-/
def Section92Step4RepairedByEmbeddedGeometryExtractionRadialFaceN6TaxonomyTarget :
    Prop :=
  ClosedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization →
    ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction →
      ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasN6Representation →
        ClosedCollarWindingFreedomSimplePatchN6NormalFormClassifiedByDetailedTaxonomy →
          ClosedCollarWindingFreedomNonrealizableInNormalForm

theorem section92Step4RepairedByEmbeddedGeometryExtractionRadialFaceN6TaxonomyTarget :
    Section92Step4RepairedByEmbeddedGeometryExtractionRadialFaceN6TaxonomyTarget := by
  intro hextract hradial hn6 hclassified
  exact
    section92Step4RepairedByEmbeddedCollarExtractionN6TaxonomyTarget
      (closedCollarWindingFreedomEveryNormalFormHasEmbeddedCollarRealization_of_geometryExtraction_of_radialFace
        hextract hradial)
      hn6 hclassified

/--
Geometry/radial-face extraction repaired target: split the serious embedded
collar extraction theorem into planar collar geometry plus the cut-open radial
face selected from that geometry, then route through the identity-preserving
embedded-collar extraction target.
-/
def Section92Step4RepairedByGeometryRadialFaceExtractionN6TaxonomyTarget :
    Prop :=
  ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesGeometryData →
    ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction →
      ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasN6Representation →
        ClosedCollarWindingFreedomSimplePatchN6NormalFormClassifiedByDetailedTaxonomy →
          ClosedCollarWindingFreedomNonrealizableInNormalForm

theorem section92Step4RepairedByGeometryRadialFaceExtractionN6TaxonomyTarget :
    Section92Step4RepairedByGeometryRadialFaceExtractionN6TaxonomyTarget := by
  intro hgeometry hradial hn6 hclassified
  exact
    section92Step4RepairedByEmbeddedGeometryExtractionRadialFaceN6TaxonomyTarget
      (closedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization_of_suppliesGeometryData
        hgeometry)
      hradial
      hn6 hclassified

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

theorem closedCollarWindingFreedomSimplePatchN6NormalFormSampleForcesRadialFace_of_embeddedCollarExtraction
    (hextract :
      ClosedCollarWindingFreedomEveryNormalFormHasEmbeddedCollarRealization) :
    ClosedCollarWindingFreedomSimplePatchN6NormalFormSampleForcesRadialFace := by
  classical
  intro V G data _hsample
  rcases hextract data.normalForm with ⟨extraction⟩
  rcases extraction with ⟨embedded, hnormalForm⟩
  have hradial :
      ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
        embedded.normalForm.annular :=
    ⟨embedded.toNormalFormRadialFaceRealization.radialFace⟩
  have hnormalRadial :
      ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
        data.normalForm.annular := by
    simpa [hnormalForm] using hradial
  simpa [data.annular_eq] using hnormalRadial

theorem closedCollarWindingFreedomSimplePatchN6NormalFormSampleForcesRadialFace_of_embeddedGeometryExtraction_of_radialFace
    (hextract :
      ClosedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization)
    (hradial :
      ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction) :
    ClosedCollarWindingFreedomSimplePatchN6NormalFormSampleForcesRadialFace :=
  closedCollarWindingFreedomSimplePatchN6NormalFormSampleForcesRadialFace_of_embeddedCollarExtraction
    (closedCollarWindingFreedomEveryNormalFormHasEmbeddedCollarRealization_of_geometryExtraction_of_radialFace
      hextract hradial)

/--
Sample obstruction using the embedded-geometry extraction chain directly.  The
remaining external hypothesis is the finite lab coverage map from represented
radial-face coherent cases to the archived rotation-system count.
-/
def Section92Step4RadialFaceSampleEmbeddedGeometryObstructionTarget :
    Prop :=
  ClosedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization →
    ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction →
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCoveredByLab →
        ∀ {V : Type} {G : SimpleGraph V},
          (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
            (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
                closedCollarSimplePatchN6AnnularEmbeddingSampleCases →
              False

theorem section92Step4RadialFaceSampleEmbeddedGeometryObstructionTarget :
    Section92Step4RadialFaceSampleEmbeddedGeometryObstructionTarget := by
  intro hextract hradial hcovered V G data hsample
  exact
    section92Step4RadialFaceSampleNormalFormObstructionTarget
      hcovered
      (closedCollarWindingFreedomSimplePatchN6NormalFormSampleForcesRadialFace_of_embeddedGeometryExtraction_of_radialFace
        hextract hradial)
      data hsample

/--
Sample obstruction from actual-collar geometry data.  This is the same sampled
radial-face obstruction, but with the normal-form side phrased in the
geometry-data obligations that the serious S4 route must discharge.
-/
def Section92Step4RadialFaceSampleGeometryDataObstructionTarget :
    Prop :=
  ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesGeometryData →
    ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction →
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCoveredByLab →
        ∀ {V : Type} {G : SimpleGraph V},
          (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
            (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
                closedCollarSimplePatchN6AnnularEmbeddingSampleCases →
              False

theorem section92Step4RadialFaceSampleGeometryDataObstructionTarget :
    Section92Step4RadialFaceSampleGeometryDataObstructionTarget := by
  intro hgeometry hradial hcovered V G data hsample
  exact
    section92Step4RadialFaceSampleEmbeddedGeometryObstructionTarget
      (closedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization_of_suppliesGeometryData
        hgeometry)
      hradial hcovered data hsample

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

def closedCollarSimplePatchN6AnnularEmbeddingSlice1000789ArtifactFile :
    String :=
  "results/fourcolor/section92_closed_collar_winding_simple_patch_annular_embedding_n6_slice_1000789_500_cases2.json"

def closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Verdict :
    String :=
  "annular_embedding_slice_found_no_profile_preserving_patch"

def closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Cases :
    List (Nat × Nat) :=
  []

def closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts :
    ClosedCollarSimplePatchAnnularEmbeddingSliceCounts where
  internalVertexCount := 6
  exactPatchTopologyCount := 1858980
  patchStartIndex := 1000789
  patchTopologyLimit := 500
  nextPatchStartIndex := 1001289
  stoppedByEmbeddingCaseLimit := false
  embeddingCaseLimit := 2
  processedPatchTopologyCount := 500
  radialOrderCaseCount := 1000
  profilePreservingCaseCount := 0
  structuralSkippedCaseCount := 0
  embeddingAuditedCaseCount := 0
  radialFaceCoherentCaseCount := 0
  radialFaceIncoherentCaseCount := 0
  totalRotationSystemCount := 0
  enumeratedRotationSystemCount := 0
  planarRotationSystemCount := 0
  radialFaceCoherentRotationCount := 0
  exactDiagonalTwoPoleTemplateBlockerCount := 0
  maxRadialCutEdgesOnSingleFaceTwoCount := 0

/--
Archived evidence from the third bounded radial-face slice mode.  The scan
processed topology indices `1000789` through `1001288`, tested both radial
orders, and found no profile-preserving non-structural case; consequently no
rotation-system radial-face audit was needed for this interval.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000789NoProfilePreservingEvidence :
    Prop :=
  ClosedCollarWindingFreedomWitnessRealizationData ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000789ArtifactFile =
      "results/fourcolor/section92_closed_collar_winding_simple_patch_annular_embedding_n6_slice_1000789_500_cases2.json" ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Verdict =
      "annular_embedding_slice_found_no_profile_preserving_patch" ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Cases = [] ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.internalVertexCount =
      6 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.exactPatchTopologyCount =
      1858980 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.patchStartIndex =
      1000789 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.patchTopologyLimit =
      500 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.nextPatchStartIndex =
      1001289 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.stoppedByEmbeddingCaseLimit =
      false ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.embeddingCaseLimit =
      2 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.processedPatchTopologyCount =
      500 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.radialOrderCaseCount =
      1000 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.profilePreservingCaseCount =
      0 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.structuralSkippedCaseCount =
      0 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.embeddingAuditedCaseCount =
      0 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.radialFaceCoherentCaseCount =
      0 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.radialFaceIncoherentCaseCount =
      0 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.totalRotationSystemCount =
      0 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.enumeratedRotationSystemCount =
      0 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.planarRotationSystemCount =
      0 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.radialFaceCoherentRotationCount =
      0 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.exactDiagonalTwoPoleTemplateBlockerCount =
      0 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.maxRadialCutEdgesOnSingleFaceTwoCount =
      0

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000789NoProfilePreservingEvidence :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000789NoProfilePreservingEvidence := by
  refine ⟨closedCollarWindingFreedomWitnessRealizationData, ?_⟩
  decide

/-- Lab-side candidate for a profile-preserving case in the third bounded slice. -/
structure ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000789ProfilePreservingCandidate where
  hprofileCountPositive :
    0 <
      closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.profilePreservingCaseCount

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000789_noProfilePreservingCandidate
    (candidate :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000789ProfilePreservingCandidate) :
    False := by
  have hzero :
      closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.profilePreservingCaseCount =
        0 := rfl
  have hpos := candidate.hprofileCountPositive
  omega

def closedCollarSimplePatchN6AnnularEmbeddingSlice1000789IndexRange
    (caseKey : Nat × Nat) : Prop :=
  closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.patchStartIndex ≤
      caseKey.1 ∧
    caseKey.1 <
      closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.nextPatchStartIndex ∧
    caseKey.2 < 2

/--
Coverage obligation for the zero-profile slice: any represented six-internal
annular witness whose enumerated key lies in this scanned interval would have
been counted as profile-preserving by the lab.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000789ProfilePreservingCoveredByLab :
    Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    (representation : ClosedCollarWindingFreedomSimplePatchN6Representation G) →
      closedCollarSimplePatchN6AnnularEmbeddingSlice1000789IndexRange
        (representation.patchTopologyIndex, representation.radialOrderIndex.1) →
        Nonempty
          ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000789ProfilePreservingCandidate

/--
Graph-facing obstruction for the zero-profile slice.  The only external
obligation is the lab coverage map from an in-range represented witness to a
positive profile-preserving count.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000789NoProfilePreservingRepresentation :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000789ProfilePreservingCoveredByLab →
    ∀ {V : Type} {G : SimpleGraph V},
      (representation : ClosedCollarWindingFreedomSimplePatchN6Representation G) →
        closedCollarSimplePatchN6AnnularEmbeddingSlice1000789IndexRange
          (representation.patchTopologyIndex, representation.radialOrderIndex.1) →
          False

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000789NoProfilePreservingRepresentation :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000789NoProfilePreservingRepresentation := by
  intro hcovered V G representation hrange
  rcases hcovered representation hrange with ⟨candidate⟩
  exact
    closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000789_noProfilePreservingCandidate
      candidate

/--
Normal-form obstruction target for the zero-profile slice.  Unlike the
radial-face row archive, this interval is blocked before rotation systems are
enumerated: no represented normal-form witness in the scanned range can pass
the profile-preservation filter.
-/
def Section92Step4NoProfileSlice1000789NormalFormObstructionTarget :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000789ProfilePreservingCoveredByLab →
    ∀ {V : Type} {G : SimpleGraph V},
      (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
        closedCollarSimplePatchN6AnnularEmbeddingSlice1000789IndexRange
          (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) →
          False

theorem section92Step4NoProfileSlice1000789NormalFormObstructionTarget :
    Section92Step4NoProfileSlice1000789NormalFormObstructionTarget := by
  intro hcovered V G data hrange
  exact
    closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000789NoProfilePreservingRepresentation
      hcovered data.representation hrange

def closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Cases :
    List (Nat × Nat) :=
  [(1001293, 0), (1001293, 1)]

def closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts :
    ClosedCollarSimplePatchAnnularEmbeddingSliceCounts where
  internalVertexCount := 6
  exactPatchTopologyCount := 1858980
  patchStartIndex := 1001289
  patchTopologyLimit := 500
  nextPatchStartIndex := 1001294
  stoppedByEmbeddingCaseLimit := true
  embeddingCaseLimit := 2
  processedPatchTopologyCount := 5
  radialOrderCaseCount := 10
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
Archived evidence from the fourth bounded radial-face slice mode.  The scan
processed topology indices `1001289` through `1001293`, discovered two
profile-preserving non-structural cases at topology `1001293`, exhausted both
rotation-system searches, and found no radial-face coherent planar rotation.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceEvidence :
    Prop :=
  ClosedCollarWindingFreedomWitnessRealizationData ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Cases =
      [(1001293, 0), (1001293, 1)] ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.internalVertexCount =
      6 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.exactPatchTopologyCount =
      1858980 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.patchStartIndex =
      1001289 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.patchTopologyLimit =
      500 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.nextPatchStartIndex =
      1001294 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.stoppedByEmbeddingCaseLimit =
      true ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.embeddingCaseLimit =
      2 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.processedPatchTopologyCount =
      5 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.radialOrderCaseCount =
      10 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.profilePreservingCaseCount =
      2 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.structuralSkippedCaseCount =
      0 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.embeddingAuditedCaseCount =
      2 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.radialFaceCoherentCaseCount =
      0 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.radialFaceIncoherentCaseCount =
      2 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.totalRotationSystemCount =
      524288 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.enumeratedRotationSystemCount =
      closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.totalRotationSystemCount ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.planarRotationSystemCount =
      16 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.radialFaceCoherentRotationCount =
      0 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.exactDiagonalTwoPoleTemplateBlockerCount =
      2 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.maxRadialCutEdgesOnSingleFaceTwoCount =
      closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.planarRotationSystemCount

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceEvidence :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceEvidence := by
  refine ⟨closedCollarWindingFreedomWitnessRealizationData, ?_⟩
  decide

/--
First-blocker reading of the fourth bounded radial-face slice.  The two
discovered profile-preserving non-structural cases are already exact diagonal
two-pole template blockers, and the radial-face audit finds no coherent
cut-open face.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289ExactTemplateFirstBlockerEvidence :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceEvidence ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.profilePreservingCaseCount =
      2 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.exactDiagonalTwoPoleTemplateBlockerCount =
      2 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.profilePreservingCaseCount =
      closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.exactDiagonalTwoPoleTemplateBlockerCount ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.structuralSkippedCaseCount =
      0 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.embeddingAuditedCaseCount =
      closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.exactDiagonalTwoPoleTemplateBlockerCount ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.radialFaceCoherentRotationCount =
      0

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289ExactTemplateFirstBlockerEvidence :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289ExactTemplateFirstBlockerEvidence := by
  refine
    ⟨closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceEvidence,
      ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    decide

def closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Case0Template :
    ClosedCollarAnnularEmbeddingSliceExactTemplateCase where
  patchTopologyIndex := 1001293
  radialOrderIndex := 0
  template := ClosedCollarDiagonalTwoPoleTemplateId.reverse
  exactTemplateKey := ClosedCollarDiagonalTwoPoleTemplateId.reverse.labKey
  cutEdges := ["g0:F4F5", "g1:F1F0"]
  sideCollarVertices := ["g0:F5", "g1:F1"]
  sideVertices := ["N2", "N5", "g0:F5", "g1:F1"]
  cutSize := 2
  sideVertexCount := 4
  otherSideVertexCount := 14

def closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Case1Template :
    ClosedCollarAnnularEmbeddingSliceExactTemplateCase where
  patchTopologyIndex := 1001293
  radialOrderIndex := 1
  template := ClosedCollarDiagonalTwoPoleTemplateId.reverse
  exactTemplateKey := ClosedCollarDiagonalTwoPoleTemplateId.reverse.labKey
  cutEdges := ["g0:F4F5", "g1:F1F0"]
  sideCollarVertices := ["g0:F5", "g1:F1"]
  sideVertices := ["N2", "N5", "g0:F5", "g1:F1"]
  cutSize := 2
  sideVertexCount := 4
  otherSideVertexCount := 14

/--
Per-case template payload for the fourth bounded radial-face slice.  Both
discovered cases are again the reverse exact diagonal two-pole template.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289ReverseTemplatePayloadEvidence :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289ExactTemplateFirstBlockerEvidence ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Case0Template.patchTopologyIndex =
      1001293 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Case0Template.radialOrderIndex =
      0 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Case1Template.patchTopologyIndex =
      1001293 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Case1Template.radialOrderIndex =
      1 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Case0Template.template =
      ClosedCollarDiagonalTwoPoleTemplateId.reverse ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Case1Template.template =
      ClosedCollarDiagonalTwoPoleTemplateId.reverse ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Case0Template.exactTemplateKey =
      ClosedCollarDiagonalTwoPoleTemplateId.reverse.labKey ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Case1Template.exactTemplateKey =
      ClosedCollarDiagonalTwoPoleTemplateId.reverse.labKey ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Case0Template.cutEdges =
      ClosedCollarDiagonalTwoPoleTemplateId.reverse.cutEdges ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Case1Template.cutEdges =
      ClosedCollarDiagonalTwoPoleTemplateId.reverse.cutEdges ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Case0Template.sideCollarVertices =
      ClosedCollarDiagonalTwoPoleTemplateId.reverse.sideCollarVertices ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Case1Template.sideCollarVertices =
      ClosedCollarDiagonalTwoPoleTemplateId.reverse.sideCollarVertices ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Case0Template.sideVertices =
      ["N2", "N5", "g0:F5", "g1:F1"] ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Case1Template.sideVertices =
      ["N2", "N5", "g0:F5", "g1:F1"] ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Case0Template.cutSize =
      2 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Case1Template.cutSize =
      2 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Case0Template.sideVertexCount =
      4 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Case1Template.sideVertexCount =
      4 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Case0Template.otherSideVertexCount =
      14 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Case1Template.otherSideVertexCount =
      14

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289ReverseTemplatePayloadEvidence :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289ReverseTemplatePayloadEvidence := by
  refine
    ⟨closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289ExactTemplateFirstBlockerEvidence,
      ?_⟩
  decide

def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289NormalFormForcesReverseTemplate :
    Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
      (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
          closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Cases →
        ∃ candidate : ClosedCollarDiagonalTwoPoleTemplateCandidate G,
          candidate.template = ClosedCollarDiagonalTwoPoleTemplateId.reverse ∧
            candidate.Realizes

def Section92Step4ReverseTemplateSlice1001289NormalFormObstructionTarget :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289ReverseTemplatePayloadEvidence →
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289NormalFormForcesReverseTemplate →
      ∀ {V : Type} {G : SimpleGraph V},
        (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
          (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
              closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Cases →
            False

theorem section92Step4ReverseTemplateSlice1001289NormalFormObstructionTarget :
    Section92Step4ReverseTemplateSlice1001289NormalFormObstructionTarget := by
  intro _hevidence hforces V G data hcase
  rcases hforces data hcase with ⟨candidate, _htemplate, hrealizes⟩
  exact
    closedCollarWindingFreedomNormalFormRealization_false_of_forcedTemplate
      data.normalForm candidate hrealizes

/-- Lab-side candidate for a radial-face coherent rotation in the fourth slice. -/
structure ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRotationCandidate where
  hrotationCountPositive :
    0 <
      closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.radialFaceCoherentRotationCount

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289_noRadialFaceRotationCandidate
    (candidate :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRotationCandidate) :
    False := by
  have hzero :
      closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.radialFaceCoherentRotationCount =
        0 := rfl
  have hpos := candidate.hrotationCountPositive
  omega

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

/--
Cumulative bounded-slice evidence through topology index `1001288`.  The first
two slices find four profile-preserving cases, all reverse exact-template
blockers with zero coherent radial-face rotations; the next adjacent slice
finds no profile-preserving cases at all.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlices1000000_1001289Evidence :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlices1000000_1000789ReverseTemplateDiscoveryEvidence ∧
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000789NoProfilePreservingEvidence ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.processedPatchTopologyCount +
        closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.processedPatchTopologyCount +
          closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.processedPatchTopologyCount =
      1289 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.radialOrderCaseCount +
        closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.radialOrderCaseCount +
          closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.radialOrderCaseCount =
      2578 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.profilePreservingCaseCount +
        closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.profilePreservingCaseCount +
          closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.profilePreservingCaseCount =
      4 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.embeddingAuditedCaseCount +
        closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.embeddingAuditedCaseCount +
          closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.embeddingAuditedCaseCount =
      4 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.radialFaceCoherentRotationCount +
        closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.radialFaceCoherentRotationCount +
          closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.radialFaceCoherentRotationCount =
      0

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlices1000000_1001289Evidence :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlices1000000_1001289Evidence := by
  refine
    ⟨closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlices1000000_1000789ReverseTemplateDiscoveryEvidence,
      closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000789NoProfilePreservingEvidence,
      ?_, ?_, ?_, ?_, ?_⟩ <;>
    decide

/--
Cumulative bounded-slice evidence through topology index `1001293`.  Across
the adjacent slices from `1000000`, the lab has processed `1294` patch
topologies and `2588` radial-order cases, found six profile-preserving cases,
and every audited case is either a reverse exact-template blocker or has no
coherent radial-face rotation.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlices1000000_1001294Evidence :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlices1000000_1001289Evidence ∧
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289ReverseTemplatePayloadEvidence ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.processedPatchTopologyCount +
        closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.processedPatchTopologyCount +
          closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.processedPatchTopologyCount +
            closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.processedPatchTopologyCount =
      1294 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.radialOrderCaseCount +
        closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.radialOrderCaseCount +
          closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.radialOrderCaseCount +
            closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.radialOrderCaseCount =
      2588 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.profilePreservingCaseCount +
        closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.profilePreservingCaseCount +
          closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.profilePreservingCaseCount +
            closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.profilePreservingCaseCount =
      6 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.embeddingAuditedCaseCount +
        closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.embeddingAuditedCaseCount +
          closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.embeddingAuditedCaseCount +
            closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.embeddingAuditedCaseCount =
      6 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.planarRotationSystemCount +
        closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.planarRotationSystemCount +
          closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.planarRotationSystemCount +
            closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.planarRotationSystemCount =
      48 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.radialFaceCoherentRotationCount +
        closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.radialFaceCoherentRotationCount +
          closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.radialFaceCoherentRotationCount +
            closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.radialFaceCoherentRotationCount =
      0 ∧
    closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.exactDiagonalTwoPoleTemplateBlockerCount +
        closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.exactDiagonalTwoPoleTemplateBlockerCount +
          closedCollarSimplePatchN6AnnularEmbeddingSlice1000789Counts.exactDiagonalTwoPoleTemplateBlockerCount +
            closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.exactDiagonalTwoPoleTemplateBlockerCount =
      6

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlices1000000_1001294Evidence :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlices1000000_1001294Evidence := by
  refine
    ⟨closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlices1000000_1001289Evidence,
      closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289ReverseTemplatePayloadEvidence,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    decide

/--
Archive manifest for the radial-face annular embedding JSON verdicts.  The
indexed sample archive is split across one four-case file plus two single-case
files; the resumable slice archive has two two-case files and intentionally
overlaps the indexed archive on the `1000301` radial-order cases.
-/
structure ClosedCollarSimplePatchAnnularEmbeddingRadialFaceArchiveCounts where
  sampleArchiveJsonFileCount : Nat
  sliceArchiveJsonFileCount : Nat
  totalArchiveJsonFileCount : Nat
  sampleArchiveRadialOrderCaseCount : Nat
  sliceArchiveRadialOrderCaseCount : Nat
  archiveRadialOrderRowsWithOverlap : Nat
  overlappingRadialOrderCaseCount : Nat
  uniqueAuditedRadialOrderCaseCount : Nat
  uniqueAuditedPatchTopologyCount : Nat
  samplePlanarRotationSystemCount : Nat
  slicePlanarRotationSystemCount : Nat
  planarRotationSystemRowsWithOverlap : Nat
  uniquePlanarRotationSystemCount : Nat
  archiveRadialFaceCoherentRotationCount : Nat
  sliceExactTemplateBlockerCount : Nat

def closedCollarSimplePatchN6AnnularEmbeddingSampleArchiveFiles :
    List String :=
  ["results/fourcolor/section92_closed_collar_winding_simple_patch_annular_embedding_n6_samples.json",
    "results/fourcolor/section92_closed_collar_winding_simple_patch_annular_embedding_n6_case_1000301_r0.json",
    "results/fourcolor/section92_closed_collar_winding_simple_patch_annular_embedding_n6_case_1000301_r1.json"]

def closedCollarSimplePatchN6AnnularEmbeddingSliceArchiveFiles :
    List String :=
  ["results/fourcolor/section92_closed_collar_winding_simple_patch_annular_embedding_n6_slice_1000000_500_cases2.json",
    "results/fourcolor/section92_closed_collar_winding_simple_patch_annular_embedding_n6_slice_1000302_500_cases2.json",
    "results/fourcolor/section92_closed_collar_winding_simple_patch_annular_embedding_n6_slice_1001289_500_cases2.json"]

def closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveAuditFile :
    String :=
  "results/fourcolor/section92_closed_collar_winding_simple_patch_n6_radial_face_archive_audit.json"

def closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases :
    List (Nat × Nat) :=
  [(821205, 0), (821205, 1), (852969, 0), (852969, 1),
    (1000301, 0), (1000301, 1), (1000788, 0), (1000788, 1),
    (1001293, 0), (1001293, 1)]

def closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCounts :
    ClosedCollarSimplePatchAnnularEmbeddingRadialFaceArchiveCounts where
  sampleArchiveJsonFileCount := 3
  sliceArchiveJsonFileCount := 3
  totalArchiveJsonFileCount := 6
  sampleArchiveRadialOrderCaseCount := 6
  sliceArchiveRadialOrderCaseCount := 6
  archiveRadialOrderRowsWithOverlap := 12
  overlappingRadialOrderCaseCount := 2
  uniqueAuditedRadialOrderCaseCount := 10
  uniqueAuditedPatchTopologyCount := 5
  samplePlanarRotationSystemCount := 48
  slicePlanarRotationSystemCount := 48
  planarRotationSystemRowsWithOverlap := 96
  uniquePlanarRotationSystemCount := 80
  archiveRadialFaceCoherentRotationCount := 0
  sliceExactTemplateBlockerCount := 6

/--
Tracked archive manifest for the radial-face annular embedding verdict JSONs.
It records the six row-bearing files behind the sampled and resumable-slice
radial-face audits, the deliberate two-case overlap, and the zero coherent-rotation
aggregate used by the radial-face obstruction targets.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveEvidence :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceEvidence ∧
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlices1000000_1001294Evidence ∧
    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveAuditFile =
      "results/fourcolor/section92_closed_collar_winding_simple_patch_n6_radial_face_archive_audit.json" ∧
    closedCollarSimplePatchN6AnnularEmbeddingSampleArchiveFiles.length =
      closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCounts.sampleArchiveJsonFileCount ∧
    closedCollarSimplePatchN6AnnularEmbeddingSliceArchiveFiles.length =
      closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCounts.sliceArchiveJsonFileCount ∧
    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCounts.totalArchiveJsonFileCount =
      closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCounts.sampleArchiveJsonFileCount +
        closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCounts.sliceArchiveJsonFileCount ∧
    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCounts.sampleArchiveRadialOrderCaseCount =
      closedCollarSimplePatchN6AnnularEmbeddingSampleCounts.radialOrderCaseCount ∧
    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCounts.sliceArchiveRadialOrderCaseCount =
      closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.embeddingAuditedCaseCount +
        closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.embeddingAuditedCaseCount +
          closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.embeddingAuditedCaseCount ∧
    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCounts.archiveRadialOrderRowsWithOverlap =
      closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCounts.sampleArchiveRadialOrderCaseCount +
        closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCounts.sliceArchiveRadialOrderCaseCount ∧
    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCounts.uniqueAuditedRadialOrderCaseCount +
        closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCounts.overlappingRadialOrderCaseCount =
      closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCounts.archiveRadialOrderRowsWithOverlap ∧
    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCounts.uniqueAuditedPatchTopologyCount =
      5 ∧
    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCounts.samplePlanarRotationSystemCount =
      closedCollarSimplePatchN6AnnularEmbeddingSampleCounts.planarRotationSystemCount ∧
    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCounts.slicePlanarRotationSystemCount =
      closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.planarRotationSystemCount +
        closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.planarRotationSystemCount +
          closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.planarRotationSystemCount ∧
    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCounts.planarRotationSystemRowsWithOverlap =
      closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCounts.samplePlanarRotationSystemCount +
        closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCounts.slicePlanarRotationSystemCount ∧
    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCounts.uniquePlanarRotationSystemCount +
        closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.planarRotationSystemCount =
      closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCounts.planarRotationSystemRowsWithOverlap ∧
    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCounts.archiveRadialFaceCoherentRotationCount =
      closedCollarSimplePatchN6AnnularEmbeddingSampleCounts.radialFaceCoherentRotationCount +
        closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.radialFaceCoherentRotationCount +
          closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.radialFaceCoherentRotationCount +
            closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.radialFaceCoherentRotationCount ∧
    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCounts.archiveRadialFaceCoherentRotationCount =
      0 ∧
    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCounts.sliceExactTemplateBlockerCount =
      closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Counts.exactDiagonalTwoPoleTemplateBlockerCount +
        closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.exactDiagonalTwoPoleTemplateBlockerCount +
          closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Counts.exactDiagonalTwoPoleTemplateBlockerCount

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveEvidence :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveEvidence := by
  refine
    ⟨closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceEvidence,
      closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlices1000000_1001294Evidence,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    decide

/--
Case-list witness for the audited radial-face archive.  The list is the
overlap-corrected union of the indexed sample cases and the non-overlapping
bounded slice cases.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveCaseEvidence :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveEvidence ∧
    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases =
      [(821205, 0), (821205, 1), (852969, 0), (852969, 1),
        (1000301, 0), (1000301, 1), (1000788, 0), (1000788, 1),
        (1001293, 0), (1001293, 1)] ∧
    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases.length =
      closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCounts.uniqueAuditedRadialOrderCaseCount

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveCaseEvidence :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveCaseEvidence := by
  refine
    ⟨closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveEvidence,
      ?_, ?_⟩ <;>
    decide

/--
Row certificate extracted from the radial-face archive audit JSON.  Each row
records the source artifact and the rotation-system verdict for one audited
`(patchTopologyIndex, radialOrderIndex)` pair.
-/
structure ClosedCollarSimplePatchAnnularEmbeddingRadialFaceRowCertificate where
  archiveFamily : String
  sourceFile : String
  patchTopologyIndex : Nat
  radialOrderIndex : Nat
  enumeratedRotationSystemCount : Nat
  planarRotationSystemCount : Nat
  radialFaceCoherentRotationCount : Nat
  templateExclusionBlocker : String
  verdict : String
deriving DecidableEq, Repr

def ClosedCollarSimplePatchAnnularEmbeddingRadialFaceRowCertificate.caseKey
    (certificate :
      ClosedCollarSimplePatchAnnularEmbeddingRadialFaceRowCertificate) :
    Nat × Nat :=
  (certificate.patchTopologyIndex, certificate.radialOrderIndex)

def closedCollarSimplePatchN6AnnularEmbeddingRadialFaceSampleRowCertificates :
    List ClosedCollarSimplePatchAnnularEmbeddingRadialFaceRowCertificate :=
  [{ archiveFamily := "sample",
      sourceFile :=
        "section92_closed_collar_winding_simple_patch_annular_embedding_n6_samples.json",
      patchTopologyIndex := 821205,
      radialOrderIndex := 0,
      enumeratedRotationSystemCount := 262144,
      planarRotationSystemCount := 8,
      radialFaceCoherentRotationCount := 0,
      templateExclusionBlocker := "excluded_exact_diagonal_two_pole_template",
      verdict := "row_has_no_radial_face_coherent_rotation" },
    { archiveFamily := "sample",
      sourceFile :=
        "section92_closed_collar_winding_simple_patch_annular_embedding_n6_samples.json",
      patchTopologyIndex := 821205,
      radialOrderIndex := 1,
      enumeratedRotationSystemCount := 262144,
      planarRotationSystemCount := 8,
      radialFaceCoherentRotationCount := 0,
      templateExclusionBlocker := "excluded_exact_diagonal_two_pole_template",
      verdict := "row_has_no_radial_face_coherent_rotation" },
    { archiveFamily := "sample",
      sourceFile :=
        "section92_closed_collar_winding_simple_patch_annular_embedding_n6_samples.json",
      patchTopologyIndex := 852969,
      radialOrderIndex := 0,
      enumeratedRotationSystemCount := 262144,
      planarRotationSystemCount := 8,
      radialFaceCoherentRotationCount := 0,
      templateExclusionBlocker := "excluded_exact_diagonal_two_pole_template",
      verdict := "row_has_no_radial_face_coherent_rotation" },
    { archiveFamily := "sample",
      sourceFile :=
        "section92_closed_collar_winding_simple_patch_annular_embedding_n6_samples.json",
      patchTopologyIndex := 852969,
      radialOrderIndex := 1,
      enumeratedRotationSystemCount := 262144,
      planarRotationSystemCount := 8,
      radialFaceCoherentRotationCount := 0,
      templateExclusionBlocker := "excluded_exact_diagonal_two_pole_template",
      verdict := "row_has_no_radial_face_coherent_rotation" },
    { archiveFamily := "sample",
      sourceFile :=
        "section92_closed_collar_winding_simple_patch_annular_embedding_n6_case_1000301_r0.json",
      patchTopologyIndex := 1000301,
      radialOrderIndex := 0,
      enumeratedRotationSystemCount := 262144,
      planarRotationSystemCount := 8,
      radialFaceCoherentRotationCount := 0,
      templateExclusionBlocker := "excluded_exact_diagonal_two_pole_template",
      verdict := "row_has_no_radial_face_coherent_rotation" },
    { archiveFamily := "sample",
      sourceFile :=
        "section92_closed_collar_winding_simple_patch_annular_embedding_n6_case_1000301_r1.json",
      patchTopologyIndex := 1000301,
      radialOrderIndex := 1,
      enumeratedRotationSystemCount := 262144,
      planarRotationSystemCount := 8,
      radialFaceCoherentRotationCount := 0,
      templateExclusionBlocker := "excluded_exact_diagonal_two_pole_template",
      verdict := "row_has_no_radial_face_coherent_rotation" }]

def closedCollarSimplePatchN6AnnularEmbeddingRadialFaceSlice1000302RowCertificates :
    List ClosedCollarSimplePatchAnnularEmbeddingRadialFaceRowCertificate :=
  [{ archiveFamily := "slice",
      sourceFile :=
        "section92_closed_collar_winding_simple_patch_annular_embedding_n6_slice_1000302_500_cases2.json",
      patchTopologyIndex := 1000788,
      radialOrderIndex := 0,
      enumeratedRotationSystemCount := 262144,
      planarRotationSystemCount := 8,
      radialFaceCoherentRotationCount := 0,
      templateExclusionBlocker := "excluded_exact_diagonal_two_pole_template",
      verdict := "row_has_no_radial_face_coherent_rotation" },
    { archiveFamily := "slice",
      sourceFile :=
        "section92_closed_collar_winding_simple_patch_annular_embedding_n6_slice_1000302_500_cases2.json",
      patchTopologyIndex := 1000788,
      radialOrderIndex := 1,
      enumeratedRotationSystemCount := 262144,
      planarRotationSystemCount := 8,
      radialFaceCoherentRotationCount := 0,
      templateExclusionBlocker := "excluded_exact_diagonal_two_pole_template",
      verdict := "row_has_no_radial_face_coherent_rotation" }]

def closedCollarSimplePatchN6AnnularEmbeddingRadialFaceSlice1001289RowCertificates :
    List ClosedCollarSimplePatchAnnularEmbeddingRadialFaceRowCertificate :=
  [{ archiveFamily := "slice",
      sourceFile :=
        "section92_closed_collar_winding_simple_patch_annular_embedding_n6_slice_1001289_500_cases2.json",
      patchTopologyIndex := 1001293,
      radialOrderIndex := 0,
      enumeratedRotationSystemCount := 262144,
      planarRotationSystemCount := 8,
      radialFaceCoherentRotationCount := 0,
      templateExclusionBlocker := "excluded_exact_diagonal_two_pole_template",
      verdict := "row_has_no_radial_face_coherent_rotation" },
    { archiveFamily := "slice",
      sourceFile :=
        "section92_closed_collar_winding_simple_patch_annular_embedding_n6_slice_1001289_500_cases2.json",
      patchTopologyIndex := 1001293,
      radialOrderIndex := 1,
      enumeratedRotationSystemCount := 262144,
      planarRotationSystemCount := 8,
      radialFaceCoherentRotationCount := 0,
      templateExclusionBlocker := "excluded_exact_diagonal_two_pole_template",
      verdict := "row_has_no_radial_face_coherent_rotation" }]

def closedCollarSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageCertificates :
    List ClosedCollarSimplePatchAnnularEmbeddingRadialFaceRowCertificate :=
  closedCollarSimplePatchN6AnnularEmbeddingRadialFaceSampleRowCertificates ++
    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceSlice1000302RowCertificates ++
      closedCollarSimplePatchN6AnnularEmbeddingRadialFaceSlice1001289RowCertificates

def closedCollarSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageVerdict :
    String :=
  "radial_face_row_coverage_all_planar_rotations_incoherent"

/--
Artifact manifest for the row-coverage target.  It says exactly which archived
rows and source files back the ten row obligations used by the current
row-factored radial-face obstruction target.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageArtifactEvidence :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveCaseEvidence ∧
    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageCertificates.map
        ClosedCollarSimplePatchAnnularEmbeddingRadialFaceRowCertificate.caseKey =
      closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases ∧
    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceSampleRowCertificates.map
        ClosedCollarSimplePatchAnnularEmbeddingRadialFaceRowCertificate.caseKey =
      closedCollarSimplePatchN6AnnularEmbeddingSampleCases ∧
    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceSlice1000302RowCertificates.map
        ClosedCollarSimplePatchAnnularEmbeddingRadialFaceRowCertificate.caseKey =
      closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Cases ∧
    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceSlice1001289RowCertificates.map
        ClosedCollarSimplePatchAnnularEmbeddingRadialFaceRowCertificate.caseKey =
      closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Cases ∧
    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageCertificates.length =
      10 ∧
    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageCertificates.map
        (fun certificate => certificate.enumeratedRotationSystemCount) =
      List.replicate 10 262144 ∧
    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageCertificates.map
        (fun certificate => certificate.planarRotationSystemCount) =
      List.replicate 10 8 ∧
    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageCertificates.map
        (fun certificate => certificate.radialFaceCoherentRotationCount) =
      List.replicate 10 0 ∧
    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageCertificates.map
        (fun certificate => certificate.templateExclusionBlocker) =
      List.replicate 10 "excluded_exact_diagonal_two_pole_template" ∧
    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageCertificates.map
        (fun certificate => certificate.verdict) =
      List.replicate 10 "row_has_no_radial_face_coherent_rotation" ∧
    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageVerdict =
      "radial_face_row_coverage_all_planar_rotations_incoherent"

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageArtifactEvidence :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageArtifactEvidence := by
  refine
    ⟨closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveCaseEvidence,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    decide

/-- Lab-side candidate for a radial-face coherent rotation in the archive. -/
structure ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveRotationCandidate where
  hrotationCountPositive :
    0 <
      closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCounts.archiveRadialFaceCoherentRotationCount

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchive_noRadialFaceRotationCandidate
    (candidate :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveRotationCandidate) :
    False := by
  have hzero :
      closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCounts.archiveRadialFaceCoherentRotationCount =
        0 := rfl
  have hpos := candidate.hrotationCountPositive
  omega

/--
Archive-level coverage obligation: if an audited six-internal representation
carries a genuine cut-open radial face, then the radial-face archive would
count a coherent planar rotation.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveCoveredByLab :
    Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    (representation : ClosedCollarWindingFreedomSimplePatchN6Representation G) →
      (representation.patchTopologyIndex, representation.radialOrderIndex.1) ∈
          closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases →
        ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
          representation.annular →
          Nonempty
            ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveRotationCandidate

/--
Archive-level obstruction for radial-face coherent annular realizations.  The
finite lab coverage map remains explicit; the theorem packages the audited
zero coherent-rotation count into the graph-facing obstruction.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveNoRadialFaceCoherentRepresentation :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveCoveredByLab →
    ∀ {V : Type} {G : SimpleGraph V},
      (representation : ClosedCollarWindingFreedomSimplePatchN6Representation G) →
        (representation.patchTopologyIndex, representation.radialOrderIndex.1) ∈
            closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases →
          ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
            representation.annular →
            False

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveNoRadialFaceCoherentRepresentation :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveNoRadialFaceCoherentRepresentation := by
  intro hcovered V G representation hcase hradial
  rcases hcovered representation hcase hradial with ⟨candidate⟩
  exact
    closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchive_noRadialFaceRotationCandidate
      candidate

/--
Missing geometric reduction for using the full radial-face archive against the
normal-form regime: every audited normal-form representation must provide a
radial-face coherent cut-open annulus.
-/
def ClosedCollarWindingFreedomSimplePatchN6NormalFormArchiveForcesRadialFace :
    Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
      (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
          closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases →
        ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
          data.representation.annular

theorem closedCollarWindingFreedomSimplePatchN6NormalFormArchiveForcesRadialFace_of_embeddedCollarExtraction
    (hextract :
      ClosedCollarWindingFreedomEveryNormalFormHasEmbeddedCollarRealization) :
    ClosedCollarWindingFreedomSimplePatchN6NormalFormArchiveForcesRadialFace := by
  classical
  intro V G data _hcase
  rcases hextract data.normalForm with ⟨extraction⟩
  rcases extraction with ⟨embedded, hnormalForm⟩
  have hradial :
      ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
        embedded.normalForm.annular :=
    ⟨embedded.toNormalFormRadialFaceRealization.radialFace⟩
  have hnormalRadial :
      ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
        data.normalForm.annular := by
    simpa [hnormalForm] using hradial
  simpa [data.annular_eq] using hnormalRadial

theorem closedCollarWindingFreedomSimplePatchN6NormalFormArchiveForcesRadialFace_of_embeddedGeometryExtraction_of_radialFace
    (hextract :
      ClosedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization)
    (hradial :
      ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction) :
    ClosedCollarWindingFreedomSimplePatchN6NormalFormArchiveForcesRadialFace :=
  closedCollarWindingFreedomSimplePatchN6NormalFormArchiveForcesRadialFace_of_embeddedCollarExtraction
    (closedCollarWindingFreedomEveryNormalFormHasEmbeddedCollarRealization_of_geometryExtraction_of_radialFace
      hextract hradial)

/--
Radial-face archive obstruction target for audited six-internal normal-form
representations.  This is the archive-level version of the sampled and
bounded-slice obstruction targets.
-/
def Section92Step4RadialFaceArchiveNormalFormObstructionTarget : Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveCaseEvidence →
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveCoveredByLab →
      ClosedCollarWindingFreedomSimplePatchN6NormalFormArchiveForcesRadialFace →
        ∀ {V : Type} {G : SimpleGraph V},
          (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
            (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
                closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases →
              False

theorem section92Step4RadialFaceArchiveNormalFormObstructionTarget :
    Section92Step4RadialFaceArchiveNormalFormObstructionTarget := by
  intro _hevidence hcovered hforces V G data hcase
  exact
    closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveNoRadialFaceCoherentRepresentation
      hcovered data.representation hcase (hforces data hcase)

/--
Archive obstruction using the embedded-geometry extraction chain directly.
Only the archive finite-lab coverage map remains as an external input.
-/
def Section92Step4RadialFaceArchiveEmbeddedGeometryObstructionTarget :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveCaseEvidence →
    ClosedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization →
      ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction →
        ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveCoveredByLab →
          ∀ {V : Type} {G : SimpleGraph V},
            (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
              (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
                  closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases →
                False

theorem section92Step4RadialFaceArchiveEmbeddedGeometryObstructionTarget :
    Section92Step4RadialFaceArchiveEmbeddedGeometryObstructionTarget := by
  intro hevidence hextract hradial hcovered V G data hcase
  exact
    section92Step4RadialFaceArchiveNormalFormObstructionTarget
      hevidence
      hcovered
      (closedCollarWindingFreedomSimplePatchN6NormalFormArchiveForcesRadialFace_of_embeddedGeometryExtraction_of_radialFace
        hextract hradial)
      data hcase

/--
Archive obstruction from actual-collar geometry data.  This is the strongest
current finite-archive statement: actual collar geometry plus cut-open
radial-face extraction reduces audited archive cases to the zero coherent
rotation verdict.
-/
def Section92Step4RadialFaceArchiveGeometryDataObstructionTarget :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveCaseEvidence →
    ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesGeometryData →
      ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction →
        ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveCoveredByLab →
          ∀ {V : Type} {G : SimpleGraph V},
            (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
              (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
                  closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases →
                False

theorem section92Step4RadialFaceArchiveGeometryDataObstructionTarget :
    Section92Step4RadialFaceArchiveGeometryDataObstructionTarget := by
  intro hevidence hgeometry hradial hcovered V G data hcase
  exact
    section92Step4RadialFaceArchiveEmbeddedGeometryObstructionTarget
      hevidence
      (closedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization_of_suppliesGeometryData
        hgeometry)
      hradial hcovered data hcase

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

/--
Bounded-slice obstruction using the embedded-geometry extraction chain
directly, with only the slice-specific finite lab coverage map left as an
external input.
-/
def Section92Step4RadialFaceSlice1000000EmbeddedGeometryObstructionTarget :
    Prop :=
  ClosedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization →
    ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction →
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000RadialFaceCoveredByLab →
        ∀ {V : Type} {G : SimpleGraph V},
          (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
            (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
                closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Cases →
              False

theorem section92Step4RadialFaceSlice1000000EmbeddedGeometryObstructionTarget :
    Section92Step4RadialFaceSlice1000000EmbeddedGeometryObstructionTarget := by
  intro hextract hradial hcovered V G data hcase
  exact
    section92Step4RadialFaceSlice1000000NormalFormObstructionTarget
      hcovered
      (closedCollarWindingFreedomSimplePatchN6NormalFormSampleForcesRadialFace_of_embeddedGeometryExtraction_of_radialFace
        hextract hradial)
      data hcase

/--
Bounded-slice obstruction from actual-collar geometry data.  This packages the
normal-form side of the slice obstruction in the same geometry-data obligations
as the global repaired S4 target.
-/
def Section92Step4RadialFaceSlice1000000GeometryDataObstructionTarget :
    Prop :=
  ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesGeometryData →
    ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction →
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000000RadialFaceCoveredByLab →
        ∀ {V : Type} {G : SimpleGraph V},
          (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
            (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
                closedCollarSimplePatchN6AnnularEmbeddingSlice1000000Cases →
              False

theorem section92Step4RadialFaceSlice1000000GeometryDataObstructionTarget :
    Section92Step4RadialFaceSlice1000000GeometryDataObstructionTarget := by
  intro hgeometry hradial hcovered V G data hcase
  exact
    section92Step4RadialFaceSlice1000000EmbeddedGeometryObstructionTarget
      (closedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization_of_suppliesGeometryData
        hgeometry)
      hradial hcovered data hcase

/-- Lab-side candidate for a radial-face coherent rotation in the second slice. -/
structure ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRotationCandidate where
  hrotationCountPositive :
    0 <
      closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.radialFaceCoherentRotationCount

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302_noRadialFaceRotationCandidate
    (candidate :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRotationCandidate) :
    False := by
  have hzero :
      closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Counts.radialFaceCoherentRotationCount =
        0 := rfl
  have hpos := candidate.hrotationCountPositive
  omega

/--
Coverage obligation for the second bounded radial-face slice: if a
representation lies in one of the discovered audited cases and carries a
genuine cut-open radial face, then the slice lab would count a coherent planar
rotation.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceCoveredByLab :
    Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    (representation : ClosedCollarWindingFreedomSimplePatchN6Representation G) →
      (representation.patchTopologyIndex, representation.radialOrderIndex.1) ∈
          closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Cases →
        ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
          representation.annular →
          Nonempty
            ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRotationCandidate

/--
Second-slice obstruction for radial-face coherent annular realizations in the
resumable radial-face search mode.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302NoRadialFaceCoherentRepresentation :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceCoveredByLab →
    ∀ {V : Type} {G : SimpleGraph V},
      (representation : ClosedCollarWindingFreedomSimplePatchN6Representation G) →
        (representation.patchTopologyIndex, representation.radialOrderIndex.1) ∈
            closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Cases →
          ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
            representation.annular →
            False

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302NoRadialFaceCoherentRepresentation :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302NoRadialFaceCoherentRepresentation := by
  intro hcovered V G representation hcase hradial
  rcases hcovered representation hcase hradial with ⟨candidate⟩
  exact
    closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302_noRadialFaceRotationCandidate
      candidate

/--
Missing geometric reduction for the second bounded radial-face slice: every
normal-form representation in the slice cases must provide a radial-face
coherent cut-open annulus.
-/
def ClosedCollarWindingFreedomSimplePatchN6NormalFormSlice1000302ForcesRadialFace :
    Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
      (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
          closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Cases →
        ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
          data.representation.annular

theorem closedCollarWindingFreedomSimplePatchN6NormalFormSlice1000302ForcesRadialFace_of_embeddedCollarExtraction
    (hextract :
      ClosedCollarWindingFreedomEveryNormalFormHasEmbeddedCollarRealization) :
    ClosedCollarWindingFreedomSimplePatchN6NormalFormSlice1000302ForcesRadialFace := by
  classical
  intro V G data _hcase
  rcases hextract data.normalForm with ⟨extraction⟩
  rcases extraction with ⟨embedded, hnormalForm⟩
  have hradial :
      ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
        embedded.normalForm.annular :=
    ⟨embedded.toNormalFormRadialFaceRealization.radialFace⟩
  have hnormalRadial :
      ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
        data.normalForm.annular := by
    simpa [hnormalForm] using hradial
  simpa [data.annular_eq] using hnormalRadial

theorem closedCollarWindingFreedomSimplePatchN6NormalFormSlice1000302ForcesRadialFace_of_embeddedGeometryExtraction_of_radialFace
    (hextract :
      ClosedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization)
    (hradial :
      ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction) :
    ClosedCollarWindingFreedomSimplePatchN6NormalFormSlice1000302ForcesRadialFace :=
  closedCollarWindingFreedomSimplePatchN6NormalFormSlice1000302ForcesRadialFace_of_embeddedCollarExtraction
    (closedCollarWindingFreedomEveryNormalFormHasEmbeddedCollarRealization_of_geometryExtraction_of_radialFace
      hextract hradial)

/--
Radial-face normal-form target for the second bounded slice.
-/
def Section92Step4RadialFaceSlice1000302NormalFormObstructionTarget : Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceCoveredByLab →
    ClosedCollarWindingFreedomSimplePatchN6NormalFormSlice1000302ForcesRadialFace →
      ∀ {V : Type} {G : SimpleGraph V},
        (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
          (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
              closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Cases →
            False

theorem section92Step4RadialFaceSlice1000302NormalFormObstructionTarget :
    Section92Step4RadialFaceSlice1000302NormalFormObstructionTarget := by
  intro hcovered hforces V G data hcase
  exact
    closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302NoRadialFaceCoherentRepresentation
      hcovered data.representation hcase (hforces data hcase)

/--
Second bounded-slice obstruction using the embedded-geometry extraction chain
directly, with only the slice-specific finite lab coverage map left as an
external input.
-/
def Section92Step4RadialFaceSlice1000302EmbeddedGeometryObstructionTarget :
    Prop :=
  ClosedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization →
    ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction →
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceCoveredByLab →
        ∀ {V : Type} {G : SimpleGraph V},
          (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
            (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
                closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Cases →
              False

theorem section92Step4RadialFaceSlice1000302EmbeddedGeometryObstructionTarget :
    Section92Step4RadialFaceSlice1000302EmbeddedGeometryObstructionTarget := by
  intro hextract hradial hcovered V G data hcase
  exact
    section92Step4RadialFaceSlice1000302NormalFormObstructionTarget
      hcovered
      (closedCollarWindingFreedomSimplePatchN6NormalFormSlice1000302ForcesRadialFace_of_embeddedGeometryExtraction_of_radialFace
        hextract hradial)
      data hcase

/--
Second bounded-slice obstruction from actual-collar geometry data.
-/
def Section92Step4RadialFaceSlice1000302GeometryDataObstructionTarget :
    Prop :=
  ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesGeometryData →
    ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction →
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceCoveredByLab →
        ∀ {V : Type} {G : SimpleGraph V},
          (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
            (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
                closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Cases →
              False

theorem section92Step4RadialFaceSlice1000302GeometryDataObstructionTarget :
    Section92Step4RadialFaceSlice1000302GeometryDataObstructionTarget := by
  intro hgeometry hradial hcovered V G data hcase
  exact
    section92Step4RadialFaceSlice1000302EmbeddedGeometryObstructionTarget
      (closedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization_of_suppliesGeometryData
        hgeometry)
      hradial hcovered data hcase

/--
Coverage obligation for the fourth bounded radial-face slice: if a
representation lies in one of the newly discovered audited cases and carries
a genuine cut-open radial face, then the slice lab would count a coherent
planar rotation.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceCoveredByLab :
    Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    (representation : ClosedCollarWindingFreedomSimplePatchN6Representation G) →
      (representation.patchTopologyIndex, representation.radialOrderIndex.1) ∈
          closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Cases →
        ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
          representation.annular →
          Nonempty
            ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRotationCandidate

/--
Fourth-slice obstruction for radial-face coherent annular realizations in the
resumable radial-face search mode.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289NoRadialFaceCoherentRepresentation :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceCoveredByLab →
    ∀ {V : Type} {G : SimpleGraph V},
      (representation : ClosedCollarWindingFreedomSimplePatchN6Representation G) →
        (representation.patchTopologyIndex, representation.radialOrderIndex.1) ∈
            closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Cases →
          ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
            representation.annular →
            False

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289NoRadialFaceCoherentRepresentation :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289NoRadialFaceCoherentRepresentation := by
  intro hcovered V G representation hcase hradial
  rcases hcovered representation hcase hradial with ⟨candidate⟩
  exact
    closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289_noRadialFaceRotationCandidate
      candidate

/--
Factored archive obstruction: the audited archive cases are covered by the
indexed sample cases plus the non-overlapping bounded row slices; the first
bounded slice is the deliberate overlap on the `1000301` sample cases.
-/
theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveNoRadialFaceCoherentRepresentation_of_sample_of_slices
    (hsample :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCoveredByLab)
    (hslice1000302 :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceCoveredByLab)
    (hslice1001289 :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceCoveredByLab)
    {V : Type} {G : SimpleGraph V}
    (representation : ClosedCollarWindingFreedomSimplePatchN6Representation G)
    (hcase :
      (representation.patchTopologyIndex, representation.radialOrderIndex.1) ∈
        closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases)
    (hradial :
      ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
        representation.annular) :
    False := by
  have hsample_or_slice :
      (representation.patchTopologyIndex, representation.radialOrderIndex.1) ∈
          closedCollarSimplePatchN6AnnularEmbeddingSampleCases ∨
        (representation.patchTopologyIndex, representation.radialOrderIndex.1) ∈
            closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Cases ∨
          (representation.patchTopologyIndex, representation.radialOrderIndex.1) ∈
            closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Cases := by
    simp [closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases,
      closedCollarSimplePatchN6AnnularEmbeddingSampleCases,
      closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Cases,
      closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Cases] at hcase ⊢
    tauto
  rcases hsample_or_slice with hsampleCase | hsliceCase
  · exact
      closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleNoRadialFaceCoherentRepresentation
        hsample representation hsampleCase hradial
  · rcases hsliceCase with hslice1000302Case | hslice1001289Case
    · exact
        closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302NoRadialFaceCoherentRepresentation
          hslice1000302 representation hslice1000302Case hradial
    · exact
        closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289NoRadialFaceCoherentRepresentation
          hslice1001289 representation hslice1001289Case hradial

/--
Archive obstruction target with the finite coverage map factored into the
sample coverage and the non-overlapping second-slice coverage.
-/
def Section92Step4RadialFaceArchiveFactoredCoverageNormalFormObstructionTarget :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveCaseEvidence →
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCoveredByLab →
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceCoveredByLab →
        ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceCoveredByLab →
          ClosedCollarWindingFreedomSimplePatchN6NormalFormArchiveForcesRadialFace →
            ∀ {V : Type} {G : SimpleGraph V},
              (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
                (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
                    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases →
                  False

theorem section92Step4RadialFaceArchiveFactoredCoverageNormalFormObstructionTarget :
    Section92Step4RadialFaceArchiveFactoredCoverageNormalFormObstructionTarget := by
  intro _hevidence hsample hslice1000302 hslice1001289 hforces V G data hcase
  exact
    closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveNoRadialFaceCoherentRepresentation_of_sample_of_slices
      hsample hslice1000302 hslice1001289 data.representation hcase
      (hforces data hcase)

/--
Factored archive obstruction using embedded-geometry extraction directly.
-/
def Section92Step4RadialFaceArchiveFactoredCoverageEmbeddedGeometryObstructionTarget :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveCaseEvidence →
    ClosedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization →
      ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction →
        ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCoveredByLab →
          ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceCoveredByLab →
            ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceCoveredByLab →
              ∀ {V : Type} {G : SimpleGraph V},
                (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
                  (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
                      closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases →
                    False

theorem section92Step4RadialFaceArchiveFactoredCoverageEmbeddedGeometryObstructionTarget :
    Section92Step4RadialFaceArchiveFactoredCoverageEmbeddedGeometryObstructionTarget := by
  intro hevidence hextract hradial hsample hslice1000302 hslice1001289 V G data hcase
  exact
    section92Step4RadialFaceArchiveFactoredCoverageNormalFormObstructionTarget
      hevidence hsample hslice1000302 hslice1001289
      (closedCollarWindingFreedomSimplePatchN6NormalFormArchiveForcesRadialFace_of_embeddedGeometryExtraction_of_radialFace
        hextract hradial)
      data hcase

/--
Factored archive obstruction from actual-collar geometry data, without the
monolithic archive coverage hypothesis.
-/
def Section92Step4RadialFaceArchiveFactoredCoverageGeometryDataObstructionTarget :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveCaseEvidence →
    ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesGeometryData →
      ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction →
        ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCoveredByLab →
          ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceCoveredByLab →
            ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceCoveredByLab →
              ∀ {V : Type} {G : SimpleGraph V},
                (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
                  (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
                      closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases →
                    False

theorem section92Step4RadialFaceArchiveFactoredCoverageGeometryDataObstructionTarget :
    Section92Step4RadialFaceArchiveFactoredCoverageGeometryDataObstructionTarget := by
  intro hevidence hgeometry hradial hsample hslice1000302 hslice1001289 V G data hcase
  exact
    section92Step4RadialFaceArchiveFactoredCoverageEmbeddedGeometryObstructionTarget
      hevidence
      (closedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization_of_suppliesGeometryData
        hgeometry)
      hradial hsample hslice1000302 hslice1001289 data hcase

/--
Per-case finite lab coverage for a sampled radial-face row.  This is the
row-level form that a JSON archive certificate should discharge before it is
assembled into the sample-wide coverage map.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCaseCoveredByLab
    (caseKey : Nat × Nat) :
    Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    (representation : ClosedCollarWindingFreedomSimplePatchN6Representation G) →
      (representation.patchTopologyIndex, representation.radialOrderIndex.1) =
          caseKey →
        ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
          representation.annular →
          Nonempty
            ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRotationCandidate

/-- The six sampled radial-face rows are individually covered by the lab. -/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCasesCoveredByLab :
    Prop :=
  ∀ caseKey,
    caseKey ∈ closedCollarSimplePatchN6AnnularEmbeddingSampleCases →
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCaseCoveredByLab
        caseKey

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCoveredByLab_of_cases
    (hcases :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCasesCoveredByLab) :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCoveredByLab := by
  intro V G representation hcase hradial
  exact
    hcases (representation.patchTopologyIndex, representation.radialOrderIndex.1)
      hcase representation rfl hradial

/--
Per-case finite lab coverage for a second-slice radial-face row.  Keeping this
separate from the sampled rows preserves the archive overlap accounting.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceCaseCoveredByLab
    (caseKey : Nat × Nat) :
    Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    (representation : ClosedCollarWindingFreedomSimplePatchN6Representation G) →
      (representation.patchTopologyIndex, representation.radialOrderIndex.1) =
          caseKey →
        ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
          representation.annular →
          Nonempty
            ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRotationCandidate

/-- The two non-overlapping second-slice radial-face rows are covered by the lab. -/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceCasesCoveredByLab :
    Prop :=
  ∀ caseKey,
    caseKey ∈ closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Cases →
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceCaseCoveredByLab
        caseKey

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceCoveredByLab_of_cases
    (hcases :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceCasesCoveredByLab) :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceCoveredByLab := by
  intro V G representation hcase hradial
  exact
    hcases (representation.patchTopologyIndex, representation.radialOrderIndex.1)
      hcase representation rfl hradial

/--
Per-case finite lab coverage for a fourth-slice radial-face row.  Keeping this
separate from the sampled rows preserves the archive overlap accounting.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceCaseCoveredByLab
    (caseKey : Nat × Nat) :
    Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    (representation : ClosedCollarWindingFreedomSimplePatchN6Representation G) →
      (representation.patchTopologyIndex, representation.radialOrderIndex.1) =
          caseKey →
        ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
          representation.annular →
          Nonempty
            ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRotationCandidate

/-- The two non-overlapping fourth-slice radial-face rows are covered by the lab. -/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceCasesCoveredByLab :
    Prop :=
  ∀ caseKey,
    caseKey ∈ closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Cases →
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceCaseCoveredByLab
        caseKey

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceCoveredByLab_of_cases
    (hcases :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceCasesCoveredByLab) :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceCoveredByLab := by
  intro V G representation hcase hradial
  exact
    hcases (representation.patchTopologyIndex, representation.radialOrderIndex.1)
      hcase representation rfl hradial

/--
Archive obstruction from row-level coverage certificates.  This is the form
the finite lab should aim to provide: one obligation per archived row, then
the Lean bridge assembles the normal-form obstruction.
-/
theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveNoRadialFaceCoherentRepresentation_of_case_coverage
    (hsample :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCasesCoveredByLab)
    (hslice1000302 :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceCasesCoveredByLab)
    (hslice1001289 :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceCasesCoveredByLab)
    {V : Type} {G : SimpleGraph V}
    (representation : ClosedCollarWindingFreedomSimplePatchN6Representation G)
    (hcase :
      (representation.patchTopologyIndex, representation.radialOrderIndex.1) ∈
        closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases)
    (hradial :
      ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
        representation.annular) :
    False :=
  closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveNoRadialFaceCoherentRepresentation_of_sample_of_slices
    (closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCoveredByLab_of_cases
      hsample)
    (closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceCoveredByLab_of_cases
      hslice1000302)
    (closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceCoveredByLab_of_cases
      hslice1001289)
    representation hcase hradial

/--
Normal-form archive target with the finite lab side factored all the way down
to exact per-row coverage obligations.
-/
def Section92Step4RadialFaceArchiveCaseFactoredCoverageNormalFormObstructionTarget :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveCaseEvidence →
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCasesCoveredByLab →
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceCasesCoveredByLab →
        ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceCasesCoveredByLab →
          ClosedCollarWindingFreedomSimplePatchN6NormalFormArchiveForcesRadialFace →
            ∀ {V : Type} {G : SimpleGraph V},
              (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
                (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
                    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases →
                  False

theorem section92Step4RadialFaceArchiveCaseFactoredCoverageNormalFormObstructionTarget :
    Section92Step4RadialFaceArchiveCaseFactoredCoverageNormalFormObstructionTarget := by
  intro _hevidence hsample hslice1000302 hslice1001289 hforces V G data hcase
  exact
    closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveNoRadialFaceCoherentRepresentation_of_case_coverage
      hsample hslice1000302 hslice1001289 data.representation hcase
      (hforces data hcase)

/--
Embedded-geometry archive target with row-level finite lab coverage.
-/
def Section92Step4RadialFaceArchiveCaseFactoredCoverageEmbeddedGeometryObstructionTarget :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveCaseEvidence →
    ClosedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization →
      ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction →
        ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCasesCoveredByLab →
          ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceCasesCoveredByLab →
            ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceCasesCoveredByLab →
              ∀ {V : Type} {G : SimpleGraph V},
                (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
                  (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
                      closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases →
                    False

theorem section92Step4RadialFaceArchiveCaseFactoredCoverageEmbeddedGeometryObstructionTarget :
    Section92Step4RadialFaceArchiveCaseFactoredCoverageEmbeddedGeometryObstructionTarget := by
  intro hevidence hextract hradial hsample hslice1000302 hslice1001289 V G data hcase
  exact
    section92Step4RadialFaceArchiveCaseFactoredCoverageNormalFormObstructionTarget
      hevidence hsample hslice1000302 hslice1001289
      (closedCollarWindingFreedomSimplePatchN6NormalFormArchiveForcesRadialFace_of_embeddedGeometryExtraction_of_radialFace
        hextract hradial)
      data hcase

/--
Geometry-data archive target with row-level finite lab coverage.  This is the
current most factored finite-archive S4 obstruction statement.
-/
def Section92Step4RadialFaceArchiveCaseFactoredCoverageGeometryDataObstructionTarget :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveCaseEvidence →
    ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesGeometryData →
      ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction →
        ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCasesCoveredByLab →
          ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceCasesCoveredByLab →
            ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceCasesCoveredByLab →
              ∀ {V : Type} {G : SimpleGraph V},
                (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
                  (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
                      closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases →
                    False

theorem section92Step4RadialFaceArchiveCaseFactoredCoverageGeometryDataObstructionTarget :
    Section92Step4RadialFaceArchiveCaseFactoredCoverageGeometryDataObstructionTarget := by
  intro hevidence hgeometry hradial hsample hslice1000302 hslice1001289 V G data hcase
  exact
    section92Step4RadialFaceArchiveCaseFactoredCoverageEmbeddedGeometryObstructionTarget
      hevidence
      (closedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization_of_suppliesGeometryData
        hgeometry)
      hradial hsample hslice1000302 hslice1001289 data hcase

/--
Semantic soundness obligation for the sampled row certificates: every honest
radial-face coherent representation whose row key appears in the sampled
certificate manifest is covered by the matching finite lab row.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowCertificateSound :
    Prop :=
  ∀ caseKey,
    caseKey ∈
        closedCollarSimplePatchN6AnnularEmbeddingRadialFaceSampleRowCertificates.map
          ClosedCollarSimplePatchAnnularEmbeddingRadialFaceRowCertificate.caseKey →
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCaseCoveredByLab
        caseKey

/--
Semantic soundness obligation for the second-slice row certificates.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowCertificateSound :
    Prop :=
  ∀ caseKey,
    caseKey ∈
        closedCollarSimplePatchN6AnnularEmbeddingRadialFaceSlice1000302RowCertificates.map
          ClosedCollarSimplePatchAnnularEmbeddingRadialFaceRowCertificate.caseKey →
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceCaseCoveredByLab
        caseKey

/--
Semantic soundness obligation for the fourth-slice row certificates.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowCertificateSound :
    Prop :=
  ∀ caseKey,
    caseKey ∈
        closedCollarSimplePatchN6AnnularEmbeddingRadialFaceSlice1001289RowCertificates.map
          ClosedCollarSimplePatchAnnularEmbeddingRadialFaceRowCertificate.caseKey →
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceCaseCoveredByLab
        caseKey

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCasesCoveredByLab_of_rowCertificateSound
    (hartifact :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageArtifactEvidence)
    (hsound :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowCertificateSound) :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCasesCoveredByLab := by
  intro caseKey hcase
  rcases hartifact with
    ⟨_archiveCases, _archiveRows, hsampleRows, _slice1000302Rows,
      _slice1001289Rows, _length,
      _enumerated, _planar, _coherent, _template, _verdicts, _rowVerdict⟩
  exact hsound caseKey (by simpa [hsampleRows] using hcase)

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceCasesCoveredByLab_of_rowCertificateSound
    (hartifact :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageArtifactEvidence)
    (hsound :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowCertificateSound) :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceCasesCoveredByLab := by
  intro caseKey hcase
  rcases hartifact with
    ⟨_archiveCases, _archiveRows, _sampleRows, hsliceRows, _slice1001289Rows,
      _length,
      _enumerated, _planar, _coherent, _template, _verdicts, _rowVerdict⟩
  exact hsound caseKey (by simpa [hsliceRows] using hcase)

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceCasesCoveredByLab_of_rowCertificateSound
    (hartifact :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageArtifactEvidence)
    (hsound :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowCertificateSound) :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceCasesCoveredByLab := by
  intro caseKey hcase
  rcases hartifact with
    ⟨_archiveCases, _archiveRows, _sampleRows, _slice1000302Rows,
      hsliceRows, _length,
      _enumerated, _planar, _coherent, _template, _verdicts, _rowVerdict⟩
  exact hsound caseKey (by simpa [hsliceRows] using hcase)

/--
Normal-form archive target with the finite lab side reduced to artifact row
certificate soundness.
-/
def Section92Step4RadialFaceArchiveRowCertificateSoundNormalFormObstructionTarget :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageArtifactEvidence →
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowCertificateSound →
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowCertificateSound →
        ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowCertificateSound →
          ClosedCollarWindingFreedomSimplePatchN6NormalFormArchiveForcesRadialFace →
            ∀ {V : Type} {G : SimpleGraph V},
              (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
                (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
                    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases →
                  False

theorem section92Step4RadialFaceArchiveRowCertificateSoundNormalFormObstructionTarget :
    Section92Step4RadialFaceArchiveRowCertificateSoundNormalFormObstructionTarget := by
  intro hartifact hsampleSound hslice1000302Sound hslice1001289Sound hforces V G data hcase
  exact
    section92Step4RadialFaceArchiveCaseFactoredCoverageNormalFormObstructionTarget
      hartifact.1
      (closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCasesCoveredByLab_of_rowCertificateSound
        hartifact hsampleSound)
      (closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceCasesCoveredByLab_of_rowCertificateSound
        hartifact hslice1000302Sound)
      (closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceCasesCoveredByLab_of_rowCertificateSound
        hartifact hslice1001289Sound)
      hforces data hcase

/--
Embedded-geometry archive target with the finite lab side reduced to artifact
row certificate soundness.
-/
def Section92Step4RadialFaceArchiveRowCertificateSoundEmbeddedGeometryObstructionTarget :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageArtifactEvidence →
  ClosedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization →
    ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction →
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowCertificateSound →
        ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowCertificateSound →
          ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowCertificateSound →
            ∀ {V : Type} {G : SimpleGraph V},
              (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
                (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
                    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases →
                  False

theorem section92Step4RadialFaceArchiveRowCertificateSoundEmbeddedGeometryObstructionTarget :
    Section92Step4RadialFaceArchiveRowCertificateSoundEmbeddedGeometryObstructionTarget := by
  intro hartifact hextract hradial hsampleSound hslice1000302Sound hslice1001289Sound V G data hcase
  exact
    section92Step4RadialFaceArchiveRowCertificateSoundNormalFormObstructionTarget
      hartifact hsampleSound hslice1000302Sound hslice1001289Sound
      (closedCollarWindingFreedomSimplePatchN6NormalFormArchiveForcesRadialFace_of_embeddedGeometryExtraction_of_radialFace
        hextract hradial)
      data hcase

/--
Geometry-data archive target with the finite lab side reduced to artifact row
certificate soundness.  This is the current sharpest statement of the serious
S4 radial-face obstruction route.
-/
def Section92Step4RadialFaceArchiveRowCertificateSoundGeometryDataObstructionTarget :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageArtifactEvidence →
  ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesGeometryData →
    ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction →
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowCertificateSound →
        ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowCertificateSound →
          ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowCertificateSound →
            ∀ {V : Type} {G : SimpleGraph V},
              (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
                (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
                    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases →
                  False

theorem section92Step4RadialFaceArchiveRowCertificateSoundGeometryDataObstructionTarget :
    Section92Step4RadialFaceArchiveRowCertificateSoundGeometryDataObstructionTarget := by
  intro hartifact hgeometry hradial hsampleSound hslice1000302Sound hslice1001289Sound V G data hcase
  exact
    section92Step4RadialFaceArchiveRowCertificateSoundEmbeddedGeometryObstructionTarget
      hartifact
      (closedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization_of_suppliesGeometryData
        hgeometry)
      hradial hsampleSound hslice1000302Sound hslice1001289Sound data hcase

/--
Archive-specific n6 extraction datum: an honest normal-form annulus is
represented by one of the audited radial-face archive rows.  This is stronger
than bare n6 extraction because it records the finite archive case membership
needed by the row-certificate obstruction.
-/
structure ClosedCollarWindingFreedomNormalFormArchiveN6RepresentationExtraction
    {V : Type} {G : SimpleGraph V}
    (normalForm : ClosedCollarWindingFreedomNormalFormRealization G) where
  data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G
  normalForm_eq : data.normalForm = normalForm
  case_mem_archive :
    (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
      closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases

/--
Global archive-extraction obligation: every honest normal-form realization of
the winding-freedom witness must land in one of the audited radial-face archive
rows.
-/
def ClosedCollarWindingFreedomEveryNormalFormHasArchiveN6Representation :
    Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    (normalForm : ClosedCollarWindingFreedomNormalFormRealization G) →
      Nonempty
        (ClosedCollarWindingFreedomNormalFormArchiveN6RepresentationExtraction
          normalForm)

theorem closedCollarWindingFreedomEveryNormalFormHasN6Representation_of_archiveN6
    (hextract :
      ClosedCollarWindingFreedomEveryNormalFormHasArchiveN6Representation) :
    ClosedCollarWindingFreedomEveryNormalFormHasN6Representation := by
  intro V G normalForm
  rcases hextract normalForm with ⟨archiveExtraction⟩
  exact
    ⟨{
      data := archiveExtraction.data
      normalForm_eq := archiveExtraction.normalForm_eq
    }⟩

theorem closedCollarWindingFreedomNonrealizableInNormalForm_of_archiveN6Representation_of_radialFaceRowCertificates
    (hextract :
      ClosedCollarWindingFreedomEveryNormalFormHasArchiveN6Representation)
    (hartifact :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageArtifactEvidence)
    (hgeometry :
      ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesGeometryData)
    (hradial :
      ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction)
    (hsampleSound :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowCertificateSound)
    (hslice1000302Sound :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowCertificateSound)
    (hslice1001289Sound :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowCertificateSound) :
    ClosedCollarWindingFreedomNonrealizableInNormalForm := by
  intro V G normalForm
  rcases hextract normalForm with ⟨archiveExtraction⟩
  exact
    section92Step4RadialFaceArchiveRowCertificateSoundGeometryDataObstructionTarget
      hartifact hgeometry hradial hsampleSound hslice1000302Sound hslice1001289Sound
      archiveExtraction.data archiveExtraction.case_mem_archive

/--
Repaired Section 9.2 Step 4 archive target: if the normal-form geometry
extracts every honest witness into the audited radial-face n6 archive, and
the row certificates are semantically sound, the residual winding-freedom
witness has no normal-form realization.
-/
def Section92Step4RepairedByArchiveN6ExtractionAndRadialFaceRowCertificatesTarget :
    Prop :=
  ClosedCollarWindingFreedomEveryNormalFormHasArchiveN6Representation →
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageArtifactEvidence →
        ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesGeometryData →
          ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction →
            ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowCertificateSound →
              ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowCertificateSound →
                ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowCertificateSound →
                  ClosedCollarWindingFreedomNonrealizableInNormalForm

theorem section92Step4RepairedByArchiveN6ExtractionAndRadialFaceRowCertificatesTarget :
    Section92Step4RepairedByArchiveN6ExtractionAndRadialFaceRowCertificatesTarget := by
  intro hextract hartifact hgeometry hradial hsampleSound hslice1000302Sound hslice1001289Sound
  exact
    closedCollarWindingFreedomNonrealizableInNormalForm_of_archiveN6Representation_of_radialFaceRowCertificates
      hextract hartifact hgeometry hradial hsampleSound hslice1000302Sound hslice1001289Sound

/--
Radial-face archive extraction datum: a normal-form annulus that already has
the cut-open radial face is represented by one of the audited radial-face n6
archive rows.
-/
structure ClosedCollarWindingFreedomRadialFaceArchiveN6RepresentationExtraction
    {V : Type} {G : SimpleGraph V}
    (normalFormRadialFace :
      ClosedCollarWindingFreedomNormalFormRadialFaceRealization G) where
  data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRadialFaceRepresentation G
  normalFormRadialFace_eq : data.normalFormRadialFace = normalFormRadialFace
  case_mem_archive :
    (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
      closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases

/--
Radial-face archive extraction obligation: every radial-face normal-form
annulus for the winding-freedom witness lands in the audited n6 archive rows.
-/
def ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasArchiveN6Representation :
    Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    (normalFormRadialFace :
      ClosedCollarWindingFreedomNormalFormRadialFaceRealization G) →
      Nonempty
        (ClosedCollarWindingFreedomRadialFaceArchiveN6RepresentationExtraction
          normalFormRadialFace)

theorem closedCollarWindingFreedomEveryNormalFormHasArchiveN6Representation_of_radialFace_of_radialFaceArchiveN6
    (hradial : ClosedCollarWindingFreedomEveryNormalFormHasRadialFace)
    (hn6 :
      ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasArchiveN6Representation) :
    ClosedCollarWindingFreedomEveryNormalFormHasArchiveN6Representation := by
  intro V G normalForm
  rcases hradial normalForm with ⟨radialExtraction⟩
  rcases hn6 radialExtraction.normalFormRadialFace with ⟨n6Extraction⟩
  let data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G :=
    { normalForm := n6Extraction.data.normalFormRadialFace.normalForm
      representation := n6Extraction.data.representation
      annular_eq := n6Extraction.data.annular_eq.symm }
  refine ⟨⟨data, ?_, ?_⟩⟩
  · dsimp [data]
    rw [n6Extraction.normalFormRadialFace_eq, radialExtraction.normalForm_eq]
  · simpa [data] using n6Extraction.case_mem_archive

theorem closedCollarWindingFreedomNonrealizableInNormalForm_of_radialFaceArchiveN6Representation_of_radialFaceRowCertificates
    (hradial : ClosedCollarWindingFreedomEveryNormalFormHasRadialFace)
    (hn6 :
      ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasArchiveN6Representation)
    (hartifact :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageArtifactEvidence)
    (hsampleSound :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowCertificateSound)
    (hslice1000302Sound :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowCertificateSound)
    (hslice1001289Sound :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowCertificateSound) :
    ClosedCollarWindingFreedomNonrealizableInNormalForm := by
  intro V G normalForm
  rcases hradial normalForm with ⟨radialExtraction⟩
  rcases hn6 radialExtraction.normalFormRadialFace with ⟨n6Extraction⟩
  have hcoherentNormal :
      ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
        n6Extraction.data.normalFormRadialFace.normalForm.annular :=
    ⟨n6Extraction.data.normalFormRadialFace.radialFace⟩
  have hcoherentRepresentation :
      ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
        n6Extraction.data.representation.annular := by
    simpa [n6Extraction.data.annular_eq] using hcoherentNormal
  exact
    closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveNoRadialFaceCoherentRepresentation_of_case_coverage
      (closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCasesCoveredByLab_of_rowCertificateSound
        hartifact hsampleSound)
      (closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceCasesCoveredByLab_of_rowCertificateSound
        hartifact hslice1000302Sound)
      (closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceCasesCoveredByLab_of_rowCertificateSound
        hartifact hslice1001289Sound)
      n6Extraction.data.representation
      n6Extraction.case_mem_archive
      hcoherentRepresentation

/--
Repaired Section 9.2 Step 4 radial-face archive target: once every honest
normal-form witness has a cut-open radial face and every such radial-face
witness extracts to the audited n6 archive rows, row-certificate soundness
refutes the residual winding-freedom witness directly.
-/
def Section92Step4RepairedByRadialFaceArchiveN6ExtractionAndRowCertificatesTarget :
    Prop :=
  ClosedCollarWindingFreedomEveryNormalFormHasRadialFace →
    ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasArchiveN6Representation →
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageArtifactEvidence →
        ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowCertificateSound →
          ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowCertificateSound →
            ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowCertificateSound →
              ClosedCollarWindingFreedomNonrealizableInNormalForm

theorem section92Step4RepairedByRadialFaceArchiveN6ExtractionAndRowCertificatesTarget :
    Section92Step4RepairedByRadialFaceArchiveN6ExtractionAndRowCertificatesTarget := by
  intro hradial hn6 hartifact hsampleSound hslice1000302Sound hslice1001289Sound
  exact
    closedCollarWindingFreedomNonrealizableInNormalForm_of_radialFaceArchiveN6Representation_of_radialFaceRowCertificates
      hradial hn6 hartifact hsampleSound hslice1000302Sound hslice1001289Sound

/--
Archive-membership theorem needed after radial-face n6 extraction: every
radial-face n6 normal-form representation of the winding-freedom witness lands
in one of the audited archive rows.  This separates the geometric extraction
of an n6 representation from the finite archive coverage theorem for its row
key.
-/
def ClosedCollarWindingFreedomEveryRadialFaceN6RepresentationInArchive :
    Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    (data :
      ClosedCollarWindingFreedomSimplePatchN6NormalFormRadialFaceRepresentation
        G) →
      (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
        closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases

theorem closedCollarWindingFreedomEveryRadialFaceNormalFormHasArchiveN6Representation_of_radialFaceN6_of_archiveMembership
    (hn6 :
      ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasN6Representation)
    (hmembership :
      ClosedCollarWindingFreedomEveryRadialFaceN6RepresentationInArchive) :
    ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasArchiveN6Representation := by
  intro V G normalFormRadialFace
  rcases hn6 normalFormRadialFace with ⟨n6Extraction⟩
  exact
    ⟨{
      data := n6Extraction.data
      normalFormRadialFace_eq := n6Extraction.normalFormRadialFace_eq
      case_mem_archive := hmembership n6Extraction.data
    }⟩

theorem closedCollarWindingFreedomNonrealizableInNormalForm_of_radialFaceN6ArchiveMembership_of_rowCertificates
    (hradial : ClosedCollarWindingFreedomEveryNormalFormHasRadialFace)
    (hn6 :
      ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasN6Representation)
    (hmembership :
      ClosedCollarWindingFreedomEveryRadialFaceN6RepresentationInArchive)
    (hartifact :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageArtifactEvidence)
    (hsampleSound :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowCertificateSound)
    (hslice1000302Sound :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowCertificateSound)
    (hslice1001289Sound :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowCertificateSound) :
    ClosedCollarWindingFreedomNonrealizableInNormalForm :=
  closedCollarWindingFreedomNonrealizableInNormalForm_of_radialFaceArchiveN6Representation_of_radialFaceRowCertificates
    hradial
    (closedCollarWindingFreedomEveryRadialFaceNormalFormHasArchiveN6Representation_of_radialFaceN6_of_archiveMembership
      hn6 hmembership)
    hartifact hsampleSound hslice1000302Sound hslice1001289Sound

/--
Repaired Section 9.2 Step 4 target with the remaining radial-face archive
extraction split into two independent obligations: extract an n6
representation from every radial-face normal-form witness, and prove the
extracted row key belongs to the audited radial-face archive.
-/
def Section92Step4RepairedByRadialFaceN6ExtractionArchiveMembershipAndRowCertificatesTarget :
    Prop :=
  ClosedCollarWindingFreedomEveryNormalFormHasRadialFace →
    ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasN6Representation →
      ClosedCollarWindingFreedomEveryRadialFaceN6RepresentationInArchive →
        ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageArtifactEvidence →
          ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowCertificateSound →
            ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowCertificateSound →
              ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowCertificateSound →
                ClosedCollarWindingFreedomNonrealizableInNormalForm

theorem section92Step4RepairedByRadialFaceN6ExtractionArchiveMembershipAndRowCertificatesTarget :
    Section92Step4RepairedByRadialFaceN6ExtractionArchiveMembershipAndRowCertificatesTarget := by
  intro hradial hn6 hmembership hartifact hsampleSound hslice1000302Sound hslice1001289Sound
  exact
    closedCollarWindingFreedomNonrealizableInNormalForm_of_radialFaceN6ArchiveMembership_of_rowCertificates
      hradial hn6 hmembership hartifact hsampleSound hslice1000302Sound hslice1001289Sound

/--
Explicit ten-row key spectrum for the audited radial-face n6 archive.  A
future geometric coverage proof can target this concrete disjunction instead
of reasoning directly about list membership.
-/
def closedCollarSimplePatchN6RadialFaceAuditedArchiveKeySpectrum
    (caseKey : Nat × Nat) : Prop :=
  caseKey = (821205, 0) ∨
    caseKey = (821205, 1) ∨
      caseKey = (852969, 0) ∨
        caseKey = (852969, 1) ∨
          caseKey = (1000301, 0) ∨
            caseKey = (1000301, 1) ∨
              caseKey = (1000788, 0) ∨
                caseKey = (1000788, 1) ∨
                  caseKey = (1001293, 0) ∨
                    caseKey = (1001293, 1)

theorem closedCollarSimplePatchN6RadialFaceAuditedArchiveKeySpectrum_mem
    {caseKey : Nat × Nat}
    (hkey :
      closedCollarSimplePatchN6RadialFaceAuditedArchiveKeySpectrum
        caseKey) :
    caseKey ∈
      closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases := by
  rcases hkey with
    hkey | hkey | hkey | hkey | hkey | hkey | hkey | hkey | hkey | hkey
  · subst caseKey
    simp [closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases]
  · subst caseKey
    simp [closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases]
  · subst caseKey
    simp [closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases]
  · subst caseKey
    simp [closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases]
  · subst caseKey
    simp [closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases]
  · subst caseKey
    simp [closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases]
  · subst caseKey
    simp [closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases]
  · subst caseKey
    simp [closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases]
  · subst caseKey
    simp [closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases]
  · subst caseKey
    simp [closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases]

/--
Key-spectrum version of archive membership: every radial-face n6 normal-form
representation has one of the ten audited row keys.
-/
def ClosedCollarWindingFreedomEveryRadialFaceN6RepresentationHasAuditedArchiveKey :
    Prop :=
  ∀ {V : Type} {G : SimpleGraph V},
    (data :
      ClosedCollarWindingFreedomSimplePatchN6NormalFormRadialFaceRepresentation
        G) →
      closedCollarSimplePatchN6RadialFaceAuditedArchiveKeySpectrum
        (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1)

theorem closedCollarWindingFreedomEveryRadialFaceN6RepresentationInArchive_of_auditedArchiveKey
    (hkeys :
      ClosedCollarWindingFreedomEveryRadialFaceN6RepresentationHasAuditedArchiveKey) :
    ClosedCollarWindingFreedomEveryRadialFaceN6RepresentationInArchive := by
  intro V G data
  exact
    closedCollarSimplePatchN6RadialFaceAuditedArchiveKeySpectrum_mem
      (hkeys data)

theorem closedCollarWindingFreedomNonrealizableInNormalForm_of_radialFaceN6AuditedArchiveKey_of_rowCertificates
    (hradial : ClosedCollarWindingFreedomEveryNormalFormHasRadialFace)
    (hn6 :
      ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasN6Representation)
    (hkeys :
      ClosedCollarWindingFreedomEveryRadialFaceN6RepresentationHasAuditedArchiveKey)
    (hartifact :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageArtifactEvidence)
    (hsampleSound :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowCertificateSound)
    (hslice1000302Sound :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowCertificateSound)
    (hslice1001289Sound :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowCertificateSound) :
    ClosedCollarWindingFreedomNonrealizableInNormalForm :=
  closedCollarWindingFreedomNonrealizableInNormalForm_of_radialFaceN6ArchiveMembership_of_rowCertificates
    hradial hn6
    (closedCollarWindingFreedomEveryRadialFaceN6RepresentationInArchive_of_auditedArchiveKey
      hkeys)
    hartifact hsampleSound hslice1000302Sound hslice1001289Sound

/--
Repaired Section 9.2 Step 4 target with the finite archive side exposed as an
explicit ten-row key spectrum.  The remaining geometric proof must force one
of those ten audited row keys for every radial-face n6 witness.
-/
def Section92Step4RepairedByRadialFaceN6ExtractionAuditedKeysAndRowCertificatesTarget :
    Prop :=
  ClosedCollarWindingFreedomEveryNormalFormHasRadialFace →
    ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasN6Representation →
      ClosedCollarWindingFreedomEveryRadialFaceN6RepresentationHasAuditedArchiveKey →
        ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageArtifactEvidence →
          ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowCertificateSound →
            ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowCertificateSound →
              ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowCertificateSound →
                ClosedCollarWindingFreedomNonrealizableInNormalForm

theorem section92Step4RepairedByRadialFaceN6ExtractionAuditedKeysAndRowCertificatesTarget :
    Section92Step4RepairedByRadialFaceN6ExtractionAuditedKeysAndRowCertificatesTarget := by
  intro hradial hn6 hkeys hartifact hsampleSound hslice1000302Sound hslice1001289Sound
  exact
    closedCollarWindingFreedomNonrealizableInNormalForm_of_radialFaceN6AuditedArchiveKey_of_rowCertificates
      hradial hn6 hkeys hartifact hsampleSound hslice1000302Sound hslice1001289Sound

/--
Explicit row-level lab coverage for the six sampled radial-face archive rows.
These are the concrete `(patchTopologyIndex, radialOrderIndex)` obligations
that the sampled JSON certificates must discharge.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowsCoveredByLab :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCaseCoveredByLab
      (821205, 0) ∧
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCaseCoveredByLab
      (821205, 1) ∧
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCaseCoveredByLab
      (852969, 0) ∧
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCaseCoveredByLab
      (852969, 1) ∧
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCaseCoveredByLab
      (1000301, 0) ∧
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCaseCoveredByLab
      (1000301, 1)

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCasesCoveredByLab_of_rows
    (hrows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowsCoveredByLab) :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCasesCoveredByLab := by
  intro caseKey hcase
  rcases hrows with
    ⟨h8212050, h8212051, h8529690, h8529691, h10003010, h10003011⟩
  simp [closedCollarSimplePatchN6AnnularEmbeddingSampleCases] at hcase
  rcases hcase with hcase | hcase | hcase | hcase | hcase | hcase
  · subst caseKey
    exact h8212050
  · subst caseKey
    exact h8212051
  · subst caseKey
    exact h8529690
  · subst caseKey
    exact h8529691
  · subst caseKey
    exact h10003010
  · subst caseKey
    exact h10003011

/--
Explicit row-level lab coverage for the two non-overlapping second-slice
radial-face archive rows.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowsCoveredByLab :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceCaseCoveredByLab
      (1000788, 0) ∧
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceCaseCoveredByLab
      (1000788, 1)

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceCasesCoveredByLab_of_rows
    (hrows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowsCoveredByLab) :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceCasesCoveredByLab := by
  intro caseKey hcase
  rcases hrows with ⟨h10007880, h10007881⟩
  simp [closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Cases] at hcase
  rcases hcase with hcase | hcase
  · subst caseKey
    exact h10007880
  · subst caseKey
    exact h10007881

/--
Explicit row-level lab coverage for the two non-overlapping fourth-slice
radial-face archive rows.
-/
def ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowsCoveredByLab :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceCaseCoveredByLab
      (1001293, 0) ∧
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceCaseCoveredByLab
      (1001293, 1)

theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceCasesCoveredByLab_of_rows
    (hrows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowsCoveredByLab) :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceCasesCoveredByLab := by
  intro caseKey hcase
  rcases hrows with ⟨h10012930, h10012931⟩
  simp [closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Cases] at hcase
  rcases hcase with hcase | hcase
  · subst caseKey
    exact h10012930
  · subst caseKey
    exact h10012931

/--
Exact row coverage discharges the row-certificate soundness obligation for
the sampled archive rows.
-/
theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowCertificateSound_of_rows
    (hrows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowsCoveredByLab) :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowCertificateSound := by
  intro caseKey hcase
  exact
    closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCasesCoveredByLab_of_rows
      hrows caseKey
      (by
        simpa [closedCollarSimplePatchN6AnnularEmbeddingRadialFaceSampleRowCertificates,
          ClosedCollarSimplePatchAnnularEmbeddingRadialFaceRowCertificate.caseKey,
          closedCollarSimplePatchN6AnnularEmbeddingSampleCases] using hcase)

/--
Exact row coverage discharges the row-certificate soundness obligation for
the non-overlapping `1000302` slice rows.
-/
theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowCertificateSound_of_rows
    (hrows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowsCoveredByLab) :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowCertificateSound := by
  intro caseKey hcase
  exact
    closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceCasesCoveredByLab_of_rows
      hrows caseKey
      (by
        simpa [closedCollarSimplePatchN6AnnularEmbeddingRadialFaceSlice1000302RowCertificates,
          ClosedCollarSimplePatchAnnularEmbeddingRadialFaceRowCertificate.caseKey,
          closedCollarSimplePatchN6AnnularEmbeddingSlice1000302Cases] using hcase)

/--
Exact row coverage discharges the row-certificate soundness obligation for
the non-overlapping `1001289` slice rows.
-/
theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowCertificateSound_of_rows
    (hrows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowsCoveredByLab) :
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowCertificateSound := by
  intro caseKey hcase
  exact
    closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceCasesCoveredByLab_of_rows
      hrows caseKey
      (by
        simpa [closedCollarSimplePatchN6AnnularEmbeddingRadialFaceSlice1001289RowCertificates,
          ClosedCollarSimplePatchAnnularEmbeddingRadialFaceRowCertificate.caseKey,
          closedCollarSimplePatchN6AnnularEmbeddingSlice1001289Cases] using hcase)

/--
Archive obstruction from exact row-level coverage certificates.
-/
theorem closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveNoRadialFaceCoherentRepresentation_of_row_coverage
    (hsample :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowsCoveredByLab)
    (hslice1000302 :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowsCoveredByLab)
    (hslice1001289 :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowsCoveredByLab)
    {V : Type} {G : SimpleGraph V}
    (representation : ClosedCollarWindingFreedomSimplePatchN6Representation G)
    (hcase :
      (representation.patchTopologyIndex, representation.radialOrderIndex.1) ∈
        closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases)
    (hradial :
      ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
        representation.annular) :
    False :=
  closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveNoRadialFaceCoherentRepresentation_of_case_coverage
    (closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceCasesCoveredByLab_of_rows
      hsample)
    (closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceCasesCoveredByLab_of_rows
      hslice1000302)
    (closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceCasesCoveredByLab_of_rows
      hslice1001289)
    representation hcase hradial

/--
Normal-form archive target with the finite lab side exposed as exact row
coverage certificates.
-/
def Section92Step4RadialFaceArchiveRowFactoredCoverageNormalFormObstructionTarget :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveCaseEvidence →
    ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowsCoveredByLab →
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowsCoveredByLab →
        ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowsCoveredByLab →
          ClosedCollarWindingFreedomSimplePatchN6NormalFormArchiveForcesRadialFace →
            ∀ {V : Type} {G : SimpleGraph V},
              (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
                (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
                    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases →
                  False

theorem section92Step4RadialFaceArchiveRowFactoredCoverageNormalFormObstructionTarget :
    Section92Step4RadialFaceArchiveRowFactoredCoverageNormalFormObstructionTarget := by
  intro _hevidence hsample hslice1000302 hslice1001289 hforces V G data hcase
  exact
    closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveNoRadialFaceCoherentRepresentation_of_row_coverage
      hsample hslice1000302 hslice1001289 data.representation hcase
      (hforces data hcase)

/--
Embedded-geometry archive target with exact row-level finite lab coverage.
-/
def Section92Step4RadialFaceArchiveRowFactoredCoverageEmbeddedGeometryObstructionTarget :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveCaseEvidence →
  ClosedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization →
    ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction →
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowsCoveredByLab →
        ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowsCoveredByLab →
          ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowsCoveredByLab →
            ∀ {V : Type} {G : SimpleGraph V},
              (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
                (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
                    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases →
                  False

theorem section92Step4RadialFaceArchiveRowFactoredCoverageEmbeddedGeometryObstructionTarget :
    Section92Step4RadialFaceArchiveRowFactoredCoverageEmbeddedGeometryObstructionTarget := by
  intro hevidence hextract hradial hsample hslice1000302 hslice1001289 V G data hcase
  exact
    section92Step4RadialFaceArchiveRowFactoredCoverageNormalFormObstructionTarget
      hevidence hsample hslice1000302 hslice1001289
      (closedCollarWindingFreedomSimplePatchN6NormalFormArchiveForcesRadialFace_of_embeddedGeometryExtraction_of_radialFace
        hextract hradial)
      data hcase

/--
Geometry-data archive target with exact row-level finite lab coverage.  This is
the row-certificate form of the current finite-archive S4 obstruction.
-/
def Section92Step4RadialFaceArchiveRowFactoredCoverageGeometryDataObstructionTarget :
    Prop :=
  ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveCaseEvidence →
  ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesGeometryData →
    ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction →
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowsCoveredByLab →
        ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowsCoveredByLab →
          ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowsCoveredByLab →
            ∀ {V : Type} {G : SimpleGraph V},
              (data : ClosedCollarWindingFreedomSimplePatchN6NormalFormRepresentation G) →
                (data.representation.patchTopologyIndex, data.representation.radialOrderIndex.1) ∈
                    closedCollarSimplePatchN6AnnularEmbeddingRadialFaceArchiveCases →
                  False

theorem section92Step4RadialFaceArchiveRowFactoredCoverageGeometryDataObstructionTarget :
    Section92Step4RadialFaceArchiveRowFactoredCoverageGeometryDataObstructionTarget := by
  intro hevidence hgeometry hradial hsample hslice1000302 hslice1001289 V G data hcase
  exact
    section92Step4RadialFaceArchiveRowFactoredCoverageEmbeddedGeometryObstructionTarget
      hevidence
      (closedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization_of_suppliesGeometryData
        hgeometry)
      hradial hsample hslice1000302 hslice1001289 data hcase

theorem closedCollarWindingFreedomNonrealizableInNormalForm_of_radialFaceN6AuditedArchiveKey_of_rowCoverage
    (hradial : ClosedCollarWindingFreedomEveryNormalFormHasRadialFace)
    (hn6 :
      ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasN6Representation)
    (hkeys :
      ClosedCollarWindingFreedomEveryRadialFaceN6RepresentationHasAuditedArchiveKey)
    (hartifact :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageArtifactEvidence)
    (hsampleRows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowsCoveredByLab)
    (hslice1000302Rows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowsCoveredByLab)
    (hslice1001289Rows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowsCoveredByLab) :
    ClosedCollarWindingFreedomNonrealizableInNormalForm :=
  closedCollarWindingFreedomNonrealizableInNormalForm_of_radialFaceN6AuditedArchiveKey_of_rowCertificates
    hradial hn6 hkeys hartifact
    (closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowCertificateSound_of_rows
      hsampleRows)
    (closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowCertificateSound_of_rows
      hslice1000302Rows)
    (closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowCertificateSound_of_rows
      hslice1001289Rows)

/--
Repaired Section 9.2 Step 4 target with the finite archive side reduced to
the explicit ten audited row-coverage obligations.  The remaining geometric
work is to prove radial-face extraction, n6 extraction, and the ten-row key
spectrum for honest normal-form witnesses.
-/
def Section92Step4RepairedByRadialFaceN6ExtractionAuditedKeysAndRowCoverageTarget :
    Prop :=
  ClosedCollarWindingFreedomEveryNormalFormHasRadialFace →
    ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasN6Representation →
      ClosedCollarWindingFreedomEveryRadialFaceN6RepresentationHasAuditedArchiveKey →
        ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageArtifactEvidence →
          ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowsCoveredByLab →
            ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowsCoveredByLab →
              ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowsCoveredByLab →
                ClosedCollarWindingFreedomNonrealizableInNormalForm

theorem section92Step4RepairedByRadialFaceN6ExtractionAuditedKeysAndRowCoverageTarget :
    Section92Step4RepairedByRadialFaceN6ExtractionAuditedKeysAndRowCoverageTarget := by
  intro hradial hn6 hkeys hartifact hsampleRows hslice1000302Rows hslice1001289Rows
  exact
    closedCollarWindingFreedomNonrealizableInNormalForm_of_radialFaceN6AuditedArchiveKey_of_rowCoverage
      hradial hn6 hkeys hartifact hsampleRows hslice1000302Rows hslice1001289Rows

theorem closedCollarWindingFreedomNonrealizableInNormalForm_of_radialFaceArchiveN6Representation_of_rowCoverage
    (hradial : ClosedCollarWindingFreedomEveryNormalFormHasRadialFace)
    (hn6 :
      ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasArchiveN6Representation)
    (hsampleRows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowsCoveredByLab)
    (hslice1000302Rows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowsCoveredByLab)
    (hslice1001289Rows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowsCoveredByLab) :
    ClosedCollarWindingFreedomNonrealizableInNormalForm := by
  intro V G normalForm
  rcases hradial normalForm with ⟨radialExtraction⟩
  rcases hn6 radialExtraction.normalFormRadialFace with ⟨n6Extraction⟩
  have hcoherentNormal :
      ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
        n6Extraction.data.normalFormRadialFace.normalForm.annular :=
    ⟨n6Extraction.data.normalFormRadialFace.radialFace⟩
  have hcoherentRepresentation :
      ClosedCollarWindingFreedomAnnularRealization.RadialFaceCoherent
        n6Extraction.data.representation.annular := by
    simpa [n6Extraction.data.annular_eq] using hcoherentNormal
  exact
    closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveNoRadialFaceCoherentRepresentation_of_row_coverage
      hsampleRows hslice1000302Rows hslice1001289Rows
      n6Extraction.data.representation
      n6Extraction.case_mem_archive
      hcoherentRepresentation

/--
Repaired Section 9.2 Step 4 radial-face archive target with the finite lab
side reduced to exact row coverage.  The remaining geometric work is to
extract a radial face and an archive n6 representation from every honest
normal-form witness.
-/
def Section92Step4RepairedByRadialFaceArchiveN6ExtractionAndRowCoverageTarget :
    Prop :=
  ClosedCollarWindingFreedomEveryNormalFormHasRadialFace →
    ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasArchiveN6Representation →
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowsCoveredByLab →
        ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowsCoveredByLab →
          ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowsCoveredByLab →
            ClosedCollarWindingFreedomNonrealizableInNormalForm

theorem section92Step4RepairedByRadialFaceArchiveN6ExtractionAndRowCoverageTarget :
    Section92Step4RepairedByRadialFaceArchiveN6ExtractionAndRowCoverageTarget := by
  intro hradial hn6 hsampleRows hslice1000302Rows hslice1001289Rows
  exact
    closedCollarWindingFreedomNonrealizableInNormalForm_of_radialFaceArchiveN6Representation_of_rowCoverage
      hradial hn6 hsampleRows hslice1000302Rows hslice1001289Rows

theorem closedCollarWindingFreedomNonrealizableInNormalForm_of_radialFaceN6ArchiveMembership_of_rowCoverage
    (hradial : ClosedCollarWindingFreedomEveryNormalFormHasRadialFace)
    (hn6 :
      ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasN6Representation)
    (hmembership :
      ClosedCollarWindingFreedomEveryRadialFaceN6RepresentationInArchive)
    (hsampleRows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowsCoveredByLab)
    (hslice1000302Rows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowsCoveredByLab)
    (hslice1001289Rows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowsCoveredByLab) :
    ClosedCollarWindingFreedomNonrealizableInNormalForm :=
  closedCollarWindingFreedomNonrealizableInNormalForm_of_radialFaceArchiveN6Representation_of_rowCoverage
    hradial
    (closedCollarWindingFreedomEveryRadialFaceNormalFormHasArchiveN6Representation_of_radialFaceN6_of_archiveMembership
      hn6 hmembership)
    hsampleRows hslice1000302Rows hslice1001289Rows

/--
Repaired Section 9.2 Step 4 radial-face n6 target with archive membership and
exact row coverage exposed directly.  This removes the row-certificate
artifact layer from the finite obstruction statement.
-/
def Section92Step4RepairedByRadialFaceN6ExtractionArchiveMembershipAndRowCoverageTarget :
    Prop :=
  ClosedCollarWindingFreedomEveryNormalFormHasRadialFace →
    ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasN6Representation →
      ClosedCollarWindingFreedomEveryRadialFaceN6RepresentationInArchive →
        ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowsCoveredByLab →
          ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowsCoveredByLab →
            ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowsCoveredByLab →
              ClosedCollarWindingFreedomNonrealizableInNormalForm

theorem section92Step4RepairedByRadialFaceN6ExtractionArchiveMembershipAndRowCoverageTarget :
    Section92Step4RepairedByRadialFaceN6ExtractionArchiveMembershipAndRowCoverageTarget := by
  intro hradial hn6 hmembership hsampleRows hslice1000302Rows hslice1001289Rows
  exact
    closedCollarWindingFreedomNonrealizableInNormalForm_of_radialFaceN6ArchiveMembership_of_rowCoverage
      hradial hn6 hmembership hsampleRows hslice1000302Rows hslice1001289Rows

theorem closedCollarWindingFreedomNonrealizableInNormalForm_of_radialFaceN6AuditedArchiveKey_of_exactRowCoverage
    (hradial : ClosedCollarWindingFreedomEveryNormalFormHasRadialFace)
    (hn6 :
      ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasN6Representation)
    (hkeys :
      ClosedCollarWindingFreedomEveryRadialFaceN6RepresentationHasAuditedArchiveKey)
    (hsampleRows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowsCoveredByLab)
    (hslice1000302Rows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowsCoveredByLab)
    (hslice1001289Rows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowsCoveredByLab) :
    ClosedCollarWindingFreedomNonrealizableInNormalForm :=
  closedCollarWindingFreedomNonrealizableInNormalForm_of_radialFaceN6ArchiveMembership_of_rowCoverage
    hradial hn6
    (closedCollarWindingFreedomEveryRadialFaceN6RepresentationInArchive_of_auditedArchiveKey
      hkeys)
    hsampleRows hslice1000302Rows hslice1001289Rows

/--
Repaired Section 9.2 Step 4 target with the finite archive side reduced to
the explicit ten-row key spectrum plus exact row coverage.
-/
def Section92Step4RepairedByRadialFaceN6ExtractionAuditedKeysAndExactRowCoverageTarget :
    Prop :=
  ClosedCollarWindingFreedomEveryNormalFormHasRadialFace →
    ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasN6Representation →
      ClosedCollarWindingFreedomEveryRadialFaceN6RepresentationHasAuditedArchiveKey →
        ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowsCoveredByLab →
          ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowsCoveredByLab →
            ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowsCoveredByLab →
              ClosedCollarWindingFreedomNonrealizableInNormalForm

theorem section92Step4RepairedByRadialFaceN6ExtractionAuditedKeysAndExactRowCoverageTarget :
    Section92Step4RepairedByRadialFaceN6ExtractionAuditedKeysAndExactRowCoverageTarget := by
  intro hradial hn6 hkeys hsampleRows hslice1000302Rows hslice1001289Rows
  exact
    closedCollarWindingFreedomNonrealizableInNormalForm_of_radialFaceN6AuditedArchiveKey_of_exactRowCoverage
      hradial hn6 hkeys hsampleRows hslice1000302Rows hslice1001289Rows

theorem closedCollarWindingFreedomNonrealizableInNormalForm_of_archiveN6Representation_of_rowCoverage
    (hextract :
      ClosedCollarWindingFreedomEveryNormalFormHasArchiveN6Representation)
    (hgeometry :
      ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesGeometryData)
    (hradial :
      ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction)
    (hsampleRows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowsCoveredByLab)
    (hslice1000302Rows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowsCoveredByLab)
    (hslice1001289Rows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowsCoveredByLab) :
    ClosedCollarWindingFreedomNonrealizableInNormalForm := by
  intro V G normalForm
  rcases hextract normalForm with ⟨archiveExtraction⟩
  exact
    closedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceArchiveNoRadialFaceCoherentRepresentation_of_row_coverage
      hsampleRows hslice1000302Rows hslice1001289Rows
      archiveExtraction.data.representation
      archiveExtraction.case_mem_archive
      ((closedCollarWindingFreedomSimplePatchN6NormalFormArchiveForcesRadialFace_of_embeddedGeometryExtraction_of_radialFace
          (closedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization_of_suppliesGeometryData
            hgeometry)
          hradial)
        archiveExtraction.data archiveExtraction.case_mem_archive)

/--
Repaired Section 9.2 Step 4 archive-extraction target with exact row coverage.
This is the archive-level serious repair route: once actual collar geometry
forces radial-face coherence for extracted archive rows, the audited row
coverage refutes the residual winding-freedom witness.
-/
def Section92Step4RepairedByArchiveN6ExtractionAndRowCoverageTarget :
    Prop :=
  ClosedCollarWindingFreedomEveryNormalFormHasArchiveN6Representation →
    ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesGeometryData →
      ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction →
        ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowsCoveredByLab →
          ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowsCoveredByLab →
            ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowsCoveredByLab →
              ClosedCollarWindingFreedomNonrealizableInNormalForm

theorem section92Step4RepairedByArchiveN6ExtractionAndRowCoverageTarget :
    Section92Step4RepairedByArchiveN6ExtractionAndRowCoverageTarget := by
  intro hextract hgeometry hradial hsampleRows hslice1000302Rows hslice1001289Rows
  exact
    closedCollarWindingFreedomNonrealizableInNormalForm_of_archiveN6Representation_of_rowCoverage
      hextract hgeometry hradial hsampleRows hslice1000302Rows hslice1001289Rows

theorem closedCollarWindingFreedomNonrealizableInNormalForm_of_geometryRadialFaceArchiveN6Representation_of_rowCoverage
    (hgeometry :
      ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesGeometryData)
    (hradial :
      ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction)
    (hn6 :
      ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasArchiveN6Representation)
    (hsampleRows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowsCoveredByLab)
    (hslice1000302Rows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowsCoveredByLab)
    (hslice1001289Rows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowsCoveredByLab) :
    ClosedCollarWindingFreedomNonrealizableInNormalForm :=
  closedCollarWindingFreedomNonrealizableInNormalForm_of_radialFaceArchiveN6Representation_of_rowCoverage
    (closedCollarWindingFreedomEveryNormalFormHasRadialFace_of_geometryData_of_radialFaceExtraction
      hgeometry hradial)
    hn6 hsampleRows hslice1000302Rows hslice1001289Rows

/--
Repaired Section 9.2 Step 4 target with actual-collar geometry and archive
n6 extraction exposed directly, and the finite side reduced to exact row
coverage.
-/
def Section92Step4RepairedByGeometryRadialFaceArchiveN6ExtractionAndRowCoverageTarget :
    Prop :=
  ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesGeometryData →
    ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction →
      ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasArchiveN6Representation →
        ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowsCoveredByLab →
          ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowsCoveredByLab →
            ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowsCoveredByLab →
              ClosedCollarWindingFreedomNonrealizableInNormalForm

theorem section92Step4RepairedByGeometryRadialFaceArchiveN6ExtractionAndRowCoverageTarget :
    Section92Step4RepairedByGeometryRadialFaceArchiveN6ExtractionAndRowCoverageTarget := by
  intro hgeometry hradial hn6 hsampleRows hslice1000302Rows hslice1001289Rows
  exact
    closedCollarWindingFreedomNonrealizableInNormalForm_of_geometryRadialFaceArchiveN6Representation_of_rowCoverage
      hgeometry hradial hn6 hsampleRows hslice1000302Rows hslice1001289Rows

theorem closedCollarWindingFreedomNonrealizableInNormalForm_of_embeddedGeometryN6AuditedArchiveKey_of_exactRowCoverage
    (hextract :
      ClosedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization)
    (hradial :
      ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction)
    (hn6 :
      ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasN6Representation)
    (hkeys :
      ClosedCollarWindingFreedomEveryRadialFaceN6RepresentationHasAuditedArchiveKey)
    (hsampleRows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowsCoveredByLab)
    (hslice1000302Rows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowsCoveredByLab)
    (hslice1001289Rows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowsCoveredByLab) :
    ClosedCollarWindingFreedomNonrealizableInNormalForm :=
  closedCollarWindingFreedomNonrealizableInNormalForm_of_radialFaceN6AuditedArchiveKey_of_exactRowCoverage
    (closedCollarWindingFreedomEveryNormalFormHasRadialFace_of_embeddedGeometryExtraction_of_radialFace
      hextract hradial)
    hn6 hkeys hsampleRows hslice1000302Rows hslice1001289Rows

/--
Repaired Section 9.2 Step 4 target with embedded collar geometry, radial-face
extraction, audited key spectrum, and exact row coverage.
-/
def Section92Step4RepairedByEmbeddedGeometryExtractionN6AuditedKeysAndExactRowCoverageTarget :
    Prop :=
  ClosedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization →
    ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction →
      ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasN6Representation →
        ClosedCollarWindingFreedomEveryRadialFaceN6RepresentationHasAuditedArchiveKey →
          ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowsCoveredByLab →
            ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowsCoveredByLab →
              ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowsCoveredByLab →
                ClosedCollarWindingFreedomNonrealizableInNormalForm

theorem section92Step4RepairedByEmbeddedGeometryExtractionN6AuditedKeysAndExactRowCoverageTarget :
    Section92Step4RepairedByEmbeddedGeometryExtractionN6AuditedKeysAndExactRowCoverageTarget := by
  intro hextract hradial hn6 hkeys hsampleRows hslice1000302Rows hslice1001289Rows
  exact
    closedCollarWindingFreedomNonrealizableInNormalForm_of_embeddedGeometryN6AuditedArchiveKey_of_exactRowCoverage
      hextract hradial hn6 hkeys hsampleRows hslice1000302Rows hslice1001289Rows

theorem closedCollarWindingFreedomNonrealizableInNormalForm_of_geometryN6AuditedArchiveKey_of_exactRowCoverage
    (hgeometry :
      ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesGeometryData)
    (hradial :
      ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction)
    (hn6 :
      ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasN6Representation)
    (hkeys :
      ClosedCollarWindingFreedomEveryRadialFaceN6RepresentationHasAuditedArchiveKey)
    (hsampleRows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowsCoveredByLab)
    (hslice1000302Rows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowsCoveredByLab)
    (hslice1001289Rows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowsCoveredByLab) :
    ClosedCollarWindingFreedomNonrealizableInNormalForm :=
  closedCollarWindingFreedomNonrealizableInNormalForm_of_embeddedGeometryN6AuditedArchiveKey_of_exactRowCoverage
    (closedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization_of_suppliesGeometryData
      hgeometry)
    hradial hn6 hkeys hsampleRows hslice1000302Rows hslice1001289Rows

/--
Repaired Section 9.2 Step 4 target with actual-collar geometry, radial-face
extraction, audited key spectrum, and exact row coverage.
-/
def Section92Step4RepairedByGeometryRadialFaceExtractionN6AuditedKeysAndExactRowCoverageTarget :
    Prop :=
  ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesGeometryData →
    ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction →
      ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasN6Representation →
        ClosedCollarWindingFreedomEveryRadialFaceN6RepresentationHasAuditedArchiveKey →
          ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowsCoveredByLab →
            ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowsCoveredByLab →
              ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowsCoveredByLab →
                ClosedCollarWindingFreedomNonrealizableInNormalForm

theorem section92Step4RepairedByGeometryRadialFaceExtractionN6AuditedKeysAndExactRowCoverageTarget :
    Section92Step4RepairedByGeometryRadialFaceExtractionN6AuditedKeysAndExactRowCoverageTarget := by
  intro hgeometry hradial hn6 hkeys hsampleRows hslice1000302Rows hslice1001289Rows
  exact
    closedCollarWindingFreedomNonrealizableInNormalForm_of_geometryN6AuditedArchiveKey_of_exactRowCoverage
      hgeometry hradial hn6 hkeys hsampleRows hslice1000302Rows hslice1001289Rows

theorem closedCollarWindingFreedomNonrealizableInNormalForm_of_previousBoundaryGeometryN6AuditedArchiveKey_of_exactRowCoverage
    (hgeometry :
      ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesPreviousBoundaryGeometryData)
    (hradial :
      ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction)
    (hn6 :
      ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasN6Representation)
    (hkeys :
      ClosedCollarWindingFreedomEveryRadialFaceN6RepresentationHasAuditedArchiveKey)
    (hsampleRows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowsCoveredByLab)
    (hslice1000302Rows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowsCoveredByLab)
    (hslice1001289Rows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowsCoveredByLab) :
    ClosedCollarWindingFreedomNonrealizableInNormalForm :=
  closedCollarWindingFreedomNonrealizableInNormalForm_of_geometryN6AuditedArchiveKey_of_exactRowCoverage
    (closedCollarWindingFreedomActualCollarEmbeddingSuppliesGeometryData_of_previousBoundaryGeometryData
      hgeometry)
    hradial hn6 hkeys hsampleRows hslice1000302Rows hslice1001289Rows

/--
Repaired Section 9.2 Step 4 target through the stronger previous-boundary
witness geometry surface.  This pins the winding obstruction to the repaired
annulus-geometry interface: previous-boundary geometry, radial-face extraction,
radial-face n6 extraction, audited ten-key spectrum, and exact row coverage
refute the residual winding-freedom witness.
-/
def Section92Step4RepairedByPreviousBoundaryGeometryRadialFaceExtractionN6AuditedKeysAndExactRowCoverageTarget :
    Prop :=
  ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesPreviousBoundaryGeometryData →
    ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction →
      ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasN6Representation →
        ClosedCollarWindingFreedomEveryRadialFaceN6RepresentationHasAuditedArchiveKey →
          ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowsCoveredByLab →
            ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowsCoveredByLab →
              ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowsCoveredByLab →
                ClosedCollarWindingFreedomNonrealizableInNormalForm

theorem section92Step4RepairedByPreviousBoundaryGeometryRadialFaceExtractionN6AuditedKeysAndExactRowCoverageTarget :
    Section92Step4RepairedByPreviousBoundaryGeometryRadialFaceExtractionN6AuditedKeysAndExactRowCoverageTarget := by
  intro hgeometry hradial hn6 hkeys hsampleRows hslice1000302Rows hslice1001289Rows
  exact
    closedCollarWindingFreedomNonrealizableInNormalForm_of_previousBoundaryGeometryN6AuditedArchiveKey_of_exactRowCoverage
      hgeometry hradial hn6 hkeys hsampleRows hslice1000302Rows hslice1001289Rows

theorem closedCollarWindingFreedomNonrealizableInNormalForm_of_embeddedGeometryN6AuditedArchiveKey_of_rowCoverage
    (hextract :
      ClosedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization)
    (hradial :
      ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction)
    (hn6 :
      ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasN6Representation)
    (hkeys :
      ClosedCollarWindingFreedomEveryRadialFaceN6RepresentationHasAuditedArchiveKey)
    (hartifact :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageArtifactEvidence)
    (hsampleRows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowsCoveredByLab)
    (hslice1000302Rows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowsCoveredByLab)
    (hslice1001289Rows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowsCoveredByLab) :
    ClosedCollarWindingFreedomNonrealizableInNormalForm :=
  closedCollarWindingFreedomNonrealizableInNormalForm_of_radialFaceN6AuditedArchiveKey_of_rowCoverage
    (closedCollarWindingFreedomEveryNormalFormHasRadialFace_of_embeddedGeometryExtraction_of_radialFace
      hextract hradial)
    hn6 hkeys hartifact hsampleRows hslice1000302Rows hslice1001289Rows

/--
Repaired Section 9.2 Step 4 target with the geometric side exposed as
embedded collar geometry plus cut-open radial-face extraction.  The remaining
finite side is the exact ten-row archive coverage and audited key spectrum.
-/
def Section92Step4RepairedByEmbeddedGeometryExtractionN6AuditedKeysAndRowCoverageTarget :
    Prop :=
  ClosedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization →
    ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction →
      ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasN6Representation →
        ClosedCollarWindingFreedomEveryRadialFaceN6RepresentationHasAuditedArchiveKey →
          ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageArtifactEvidence →
            ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowsCoveredByLab →
              ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowsCoveredByLab →
                ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowsCoveredByLab →
                  ClosedCollarWindingFreedomNonrealizableInNormalForm

theorem section92Step4RepairedByEmbeddedGeometryExtractionN6AuditedKeysAndRowCoverageTarget :
    Section92Step4RepairedByEmbeddedGeometryExtractionN6AuditedKeysAndRowCoverageTarget := by
  intro hextract hradial hn6 hkeys hartifact hsampleRows hslice1000302Rows hslice1001289Rows
  exact
    closedCollarWindingFreedomNonrealizableInNormalForm_of_embeddedGeometryN6AuditedArchiveKey_of_rowCoverage
      hextract hradial hn6 hkeys hartifact hsampleRows hslice1000302Rows hslice1001289Rows

theorem closedCollarWindingFreedomNonrealizableInNormalForm_of_geometryN6AuditedArchiveKey_of_rowCoverage
    (hgeometry :
      ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesGeometryData)
    (hradial :
      ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction)
    (hn6 :
      ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasN6Representation)
    (hkeys :
      ClosedCollarWindingFreedomEveryRadialFaceN6RepresentationHasAuditedArchiveKey)
    (hartifact :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageArtifactEvidence)
    (hsampleRows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowsCoveredByLab)
    (hslice1000302Rows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowsCoveredByLab)
    (hslice1001289Rows :
      ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowsCoveredByLab) :
    ClosedCollarWindingFreedomNonrealizableInNormalForm :=
  closedCollarWindingFreedomNonrealizableInNormalForm_of_embeddedGeometryN6AuditedArchiveKey_of_rowCoverage
    (closedCollarWindingFreedomEveryNormalFormHasEmbeddedGeometryRealization_of_suppliesGeometryData
      hgeometry)
    hradial hn6 hkeys hartifact hsampleRows hslice1000302Rows hslice1001289Rows

/--
Repaired Section 9.2 Step 4 target with the actual-collar geometry side split
into embedded geometry data and radial-face extraction, and the finite side
split into n6 extraction, audited key spectrum, and exact ten-row coverage.
-/
def Section92Step4RepairedByGeometryRadialFaceExtractionN6AuditedKeysAndRowCoverageTarget :
    Prop :=
  ClosedCollarWindingFreedomActualCollarEmbeddingSuppliesGeometryData →
    ClosedCollarWindingFreedomActualCollarGeometrySuppliesRadialFaceExtraction →
      ClosedCollarWindingFreedomEveryRadialFaceNormalFormHasN6Representation →
        ClosedCollarWindingFreedomEveryRadialFaceN6RepresentationHasAuditedArchiveKey →
          ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingRadialFaceRowCoverageArtifactEvidence →
            ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSampleRadialFaceRowsCoveredByLab →
              ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1000302RadialFaceRowsCoveredByLab →
                ClosedCollarWindingFreedomSimplePatchN6AnnularEmbeddingSlice1001289RadialFaceRowsCoveredByLab →
                  ClosedCollarWindingFreedomNonrealizableInNormalForm

theorem section92Step4RepairedByGeometryRadialFaceExtractionN6AuditedKeysAndRowCoverageTarget :
    Section92Step4RepairedByGeometryRadialFaceExtractionN6AuditedKeysAndRowCoverageTarget := by
  intro hgeometry hradial hn6 hkeys hartifact hsampleRows hslice1000302Rows hslice1001289Rows
  exact
    closedCollarWindingFreedomNonrealizableInNormalForm_of_geometryN6AuditedArchiveKey_of_rowCoverage
      hgeometry hradial hn6 hkeys hartifact hsampleRows hslice1000302Rows hslice1001289Rows

end GoertzelLemma818ClosedCollarWindingRealization

end Mettapedia.GraphTheory.FourColor
