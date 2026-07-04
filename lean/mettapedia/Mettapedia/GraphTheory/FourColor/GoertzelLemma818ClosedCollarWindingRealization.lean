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

end GoertzelLemma818ClosedCollarWindingRealization

end Mettapedia.GraphTheory.FourColor
