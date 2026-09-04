import Mettapedia.GraphTheory.FourColor.GoertzelV24ConnectedBranchDecompositionForest
import Mettapedia.GraphTheory.FourColor.GoertzelV24ConnectedVertexSideEdgeShore
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedDualCycleExactBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24LiteralShoreReplacement
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalFaceIntersections

/-!
# Literal replacement from actual facial-dual nooses

The physical replacement theorem is indexed by connected edge shores.  A
geometric sphere cut, however, is presented by a simple cycle in the actual
facial dual.  This file connects those two representations without storing
any replacement or planarity conclusion in the input data.

A `DualNooseSide` contains only a facial-dual cycle and one component after
deleting the primal edges crossed by that cycle.  Spherical parity saturation
then proves that those edges are the exact component boundary and that both
vertex sides are connected.  Assigning every edge incident with the chosen
vertex side to its shore gives connected complementary edge shores.  The
middle vertices of this shore inject into the actual crossing darts, so the
noose length bounds the finite-state width.

The final theorem consumes two such nooses.  Proper nesting and equality of
their computed phased states are the decomposition/pigeonhole inputs; all
physical gluing and digon normalization remain internal.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DualNooseLiteralReplacement

open GoertzelV24ConnectedBranchDecompositionForest
open GoertzelV24ConnectedEdgeShoreMajority
open GoertzelV24ConnectedShoreLiteralNode
open GoertzelV24ConnectedVertexSideEdgeShore
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24FramedDualCycleExactBoundary
open GoertzelV24IteratedDigonNormalization
open GoertzelV24LiteralShoreReplacement
open GoertzelV24MinimalFaceIntersections
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24SphereCutMaterial
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-! ## Actual facial-dual nooses -/

/-- An oriented side of an actual combinatorial noose.  The only stored data
are a simple closed walk in the literal facial dual and a connected component
of the graph after deleting its crossed primal edges.  Exact boundary,
connected complementary sides, caps, profiles and replacement are not fields.
-/
structure DualNooseSide
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData) where
  start : AmbientFace
    (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
  walk : (interiorDualGraph
    (orbitFaceBoundary graphData.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace graphData.toRotationSystem))).Walk start start
  isCycle : walk.IsCycle
  component :
    (G.deleteEdges (edgeFinsetValueSet
      (dualWalkCrossingEdges
        (orbitFaceBoundary graphData.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace graphData.toRotationSystem))
        (pairwiseUniqueSharedInteriorEdges graphData minimal) walk))).ConnectedComponent

namespace DualNooseSide

/-- The actual set of primal edges crossed by the noose. -/
noncomputable def crossingEdges
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    (noose : DualNooseSide graphData minimal) : Finset G.edgeSet :=
  dualWalkCrossingEdges
    (orbitFaceBoundary graphData.toRotationSystem)
    (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
    (pairwiseUniqueSharedInteriorEdges graphData minimal) noose.walk

/-- The selected primal vertex side of the noose. -/
def side
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    (noose : DualNooseSide graphData minimal) (vertex : V) : Prop :=
  vertex ∈ noose.component.supp

/-- The monotone edge shore associated to the selected side. -/
noncomputable def shore
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    (noose : DualNooseSide graphData minimal) : Finset G.edgeSet :=
  incidentEdgeShore G noose.side

/-- A minimal spherical map is connected also in its graph-backed simple
graph presentation. -/
private theorem graph_connected
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData} :
    G.Connected := by
  rw [← rotationPrimalGraph_toRotationSystem_eq G graphData]
  exact minimal.primalConnected

/-- A facial-dual noose has its literal crossed-edge set as the exact boundary
of the chosen component, and both resulting vertex sides are connected. -/
theorem exactBoundary_connectedSides
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    (noose : DualNooseSide graphData minimal) :
    componentCrossingEdges noose.crossingEdges noose.component =
        noose.crossingEdges ∧
      (G.induce noose.side).Connected ∧
      (G.induce (fun vertex => ¬ noose.side vertex)).Connected := by
  let hdual := orbitFaceInteriorDual_connected
    graphData.toRotationSystem minimal.spherical.cubic
      minimal.primalConnected minimal.vertexRotationCyclic
  change componentCrossingEdges noose.crossingEdges noose.component =
        noose.crossingEdges ∧
      (G.induce (fun vertex => vertex ∈ noose.component.supp)).Connected ∧
      (G.induce (fun vertex => vertex ∉ noose.component.supp)).Connected
  simpa only [crossingEdges] using
    (component_exactBoundary_connectedSides_of_dualCycle
      graphData minimal.facesTwoSided hdual
      (graph_connected (G := G) (graphData := graphData) (minimal := minimal))
      minimal.spherical.euler
      (pairwiseUniqueSharedInteriorEdges graphData minimal)
      noose.walk noose.isCycle noose.component)

/-- The middle width of the noose shore is bounded by the literal length of
the facial-dual cycle. -/
theorem middle_card_le_walk_length
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    (noose : DualNooseSide graphData minimal) :
    (edgeShoreMiddleVertices G noose.shore).card ≤ noose.walk.length := by
  have hgeometry := noose.exactBoundary_connectedSides
  calc
    (edgeShoreMiddleVertices G noose.shore).card ≤
        Fintype.card (CrossingSideDart G noose.side) :=
      card_middle_incidentEdgeShore_le_crossingSideDart noose.side
    _ ≤ noose.crossingEdges.card := by
      apply card_crossingSideDart_le_card_removed noose.side noose.crossingEdges
      intro dart
      rw [← hgeometry.1, mem_componentCrossingEdges_iff]
      exact ⟨dart.1.fst, dart.1.snd,
        Sym2.mem_mk_left _ _, Sym2.mem_mk_right _ _,
        dart.2.1, dart.2.2⟩
    _ = noose.walk.length := by
      exact card_dualWalkCrossingEdges_eq_length_of_isCycle
        (orbitFaceBoundary graphData.toRotationSystem)
        (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
        (orbitFace_incidence_le_two graphData.toRotationSystem)
        (pairwiseUniqueSharedInteriorEdges graphData minimal)
        noose.walk noose.isCycle

/-- An admissible bounded noose produces the exact connected-shore node used
by finite descent.  The sole nondegeneracy premise says that at least two
edges remain wholly on the opposite side; all geometric fields are derived
from the actual dual cycle. -/
noncomputable def toConnectedShoreNode
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    (noose : DualNooseSide graphData minimal)
    (w : Nat) (hlength : noose.walk.length ≤ w)
    (hcomplementTwo : 2 ≤ (Finset.univ \ noose.shore).card) :
    ConnectedShoreNode (G := G) w w := by
  have hgeometry := noose.exactBoundary_connectedSides
  have hconnectedShores := connected_edgeShores_of_connected_vertexSides
    (G := G) noose.side hgeometry.2.1 hgeometry.2.2
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have hshoreTwo : 2 ≤ noose.shore.card := by
    obtain ⟨vertex, hvertex⟩ := noose.component.nonempty_supp
    have hsubset : incidentEdgeFinset G vertex ⊆ noose.shore := by
      intro edge hedge
      exact (mem_incidentEdgeShore_iff noose.side edge).2
        ⟨vertex, by simpa [incidentEdgeFinset] using hedge, hvertex⟩
    have hthree : 3 ≤ noose.shore.card := by
      rw [← hcubic vertex]
      exact Finset.card_le_card hsubset
    omega
  have hmiddle : (edgeShoreMiddleVertices G noose.shore).card ≤ w :=
    noose.middle_card_le_walk_length.trans hlength
  exact (ConnectedCutCondition.ofConnectedTwo noose.shore hcubic
    hconnectedShores.1 hconnectedShores.2 hshoreTwo hcomplementTwo
    hmiddle hmiddle).toNode

@[simp]
theorem toConnectedShoreNode_shore
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    (noose : DualNooseSide graphData minimal)
    (w : Nat) (hlength : noose.walk.length ≤ w)
    (hcomplementTwo : 2 ≤ (Finset.univ \ noose.shore).card) :
    (noose.toConnectedShoreNode w hlength hcomplementTwo).shore = noose.shore :=
  rfl

end DualNooseSide

/-! ## Two compatible nooses physically shorten the map -/

/-- **Actual-noose consumer form of M2.**  Two bounded facial-dual nooses in
a vertex-minimal spherical Tait counterexample, with nondegenerate exterior
shores, strictly nested induced edge shores, and equal computed phased states,
construct a strictly smaller endpoint-simple counterexample.  Exact boundary,
connectedness, width control, cap geometry, Count preservation, sewing and
digon normalization are all theorem consequences rather than input fields. -/
theorem exists_endpointSimple_replacement_of_nested_dualNooses
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (w : Nat)
    (oldNoose newNoose : DualNooseSide graphData minimal)
    (hOldLength : oldNoose.walk.length ≤ w)
    (hNewLength : newNoose.walk.length ≤ w)
    (hOldComplementTwo :
      2 ≤ (Finset.univ \ oldNoose.shore).card)
    (hNewComplementTwo :
      2 ≤ (Finset.univ \ newNoose.shore).card)
    (hproper : newNoose.shore ⊂ oldNoose.shore)
    (heq :
      (oldNoose.toConnectedShoreNode w hOldLength hOldComplementTwo).cardPhasedState
          graphData minimal =
        (newNoose.toConnectedShoreNode w hNewLength hNewComplementTwo).cardPhasedState
          graphData minimal) :
    EndpointSimpleCounterexampleBelow.{u} (Fintype.card V) := by
  let oldNode :=
    (oldNoose.toConnectedShoreNode w hOldLength hOldComplementTwo).toLiteral
      graphData minimal
  let newNode :=
    (newNoose.toConnectedShoreNode w hNewLength hNewComplementTwo).toLiteral
      graphData minimal
  apply exists_endpointSimple_replacement_of_cardPhasedState_eq
    graphData minimal.toBridgelessSphericalCubicMapData minimal.notColorable
    oldNode newNode
  · simpa [oldNode, newNode] using hproper
  · simpa [oldNode, newNode, ConnectedShoreNode.cardPhasedState] using heq

end

end GoertzelV24DualNooseLiteralReplacement

end Mettapedia.GraphTheory.FourColor
