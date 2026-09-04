import Mettapedia.GraphTheory.FourColor.GoertzelV24ConnectedBranchDecompositionForest
import Mettapedia.GraphTheory.FourColor.GoertzelV24ConnectedVertexSideEdgeShore
import Mettapedia.GraphTheory.FourColor.GoertzelV24LiteralShoreReplacement
import Mettapedia.GraphTheory.FourColor.CyclicCutSaturation

/-!
# Connected shore states from cyclic edge cuts

The geometric decomposition layer naturally produces a vertex bipartition
whose exact boundary is a finite cyclic edge cut.  The exact-support descent,
on the other hand, consumes connected edge shores.  This file gives the
generic adapter between those two mathematical representations.

For connected complementary vertex sides, assign an edge to the chosen shore
when it has an endpoint on that side.  The two resulting edge shores are
connected, the cycles on the two sides make their majority regions nonempty,
and every middle vertex injects into an outgoing cut dart.  Hence the literal
middle width is no larger than the number of cut edges.

No planarity or catalogue data occur here.  Planarity is responsible for
supplying the cyclic cut; this adapter only turns that cut into the exact
finite state already consumed by physical replacement.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace CyclicEdgeCutRealization

open GoertzelV24ConnectedEdgeShoreMajority
open GoertzelV24ConnectedShoreLiteralNode
open GoertzelV24ConnectedVertexSideEdgeShore
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24IteratedDigonNormalization
open GoertzelV24LiteralShoreReplacement
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24SimpleGraphFaceDualConnectedness
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

/-- The incident-edge shore of a connected realized cyclic cut has middle
width bounded by the number of edges in the cut. -/
theorem card_middle_incidentEdgeShore_le_edgeCut
    {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut) :
    (edgeShoreMiddleVertices G
      (incidentEdgeShore G realization.side)).card ≤ edgeCut.card := by
  calc
    (edgeShoreMiddleVertices G
        (incidentEdgeShore G realization.side)).card ≤
        Fintype.card (CrossingSideDart G realization.side) :=
      card_middle_incidentEdgeShore_le_crossingSideDart realization.side
    _ ≤ edgeCut.card := by
      apply card_crossingSideDart_le_card_removed realization.side edgeCut
      intro dart
      apply (realization.hcut_eq
        (⟨dart.1.edge, dart.1.edge_mem⟩ : G.edgeSet)).2
      exact ⟨dart.1.fst, dart.1.snd,
        Sym2.mem_mk_left _ _, Sym2.mem_mk_right _ _,
        dart.2.1, dart.2.2⟩

/-- A realized cyclic cut with connected induced sides canonically becomes
the connected-shore node used by the exact finite-state descent.  All node
fields are derived from the cut geometry and cubicity. -/
noncomputable def toConnectedShoreNodeOfConnectedSides
    {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (hside : (G.induce realization.side).Connected)
    (hcomplement :
      (G.induce (fun vertex => ¬ realization.side vertex)).Connected)
    (bound : Nat) (hcard : edgeCut.card ≤ bound) :
    ConnectedShoreNode (G := G) bound bound := by
  have hgeometry :=
    connected_edgeShores_and_nonempty_majoritySides_of_cycles
      (G := G) hcubic realization.side hside hcomplement
      realization.hinside_cycle realization.houtside_cycle
  have hmiddle :
      (edgeShoreMiddleVertices G
        (incidentEdgeShore G realization.side)).card ≤ bound :=
    (realization.card_middle_incidentEdgeShore_le_edgeCut).trans hcard
  exact
    { shore := incidentEdgeShore G realization.side
      shoreConnected := hgeometry.1
      complementConnected := hgeometry.2.1
      majorityNonempty := hgeometry.2.2.1
      complementNonempty := hgeometry.2.2.2
      widthMiddle := hmiddle
      middleBound := hmiddle }

@[simp]
theorem toConnectedShoreNodeOfConnectedSides_shore
    {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (hside : (G.induce realization.side).Connected)
    (hcomplement :
      (G.induce (fun vertex => ¬ realization.side vertex)).Connected)
    (bound : Nat) (hcard : edgeCut.card ≤ bound) :
    (realization.toConnectedShoreNodeOfConnectedSides hcubic hside
      hcomplement bound hcard).shore =
      incidentEdgeShore G realization.side :=
  rfl

/-- In a graph-backed least counterexample, cubicity is already part of the
normal form, so a connected realized cut needs no additional algebraic input
to become an exact-support shore node. -/
noncomputable def toConnectedShoreNodeOfVertexMinimal
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut)
    (hside : (G.induce realization.side).Connected)
    (hcomplement :
      (G.induce (fun vertex => ¬ realization.side vertex)).Connected)
    (bound : Nat) (hcard : edgeCut.card ≤ bound) :
    ConnectedShoreNode (G := G) bound bound :=
  realization.toConnectedShoreNodeOfConnectedSides
    (incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      rotation minimal.spherical.cubic)
    hside hcomplement bound hcard

@[simp]
theorem toConnectedShoreNodeOfVertexMinimal_shore
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut)
    (hside : (G.induce realization.side).Connected)
    (hcomplement :
      (G.induce (fun vertex => ¬ realization.side vertex)).Connected)
    (bound : Nat) (hcard : edgeCut.card ≤ bound) :
    (realization.toConnectedShoreNodeOfVertexMinimal rotation minimal
      hside hcomplement bound hcard).shore =
      incidentEdgeShore G realization.side :=
  rfl

/-- A saturated bounded cyclic-cut receipt canonically carries the exact
connected shore state of a graph-backed least counterexample. -/
noncomputable def ConnectedAtWidth.toConnectedShoreNode
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {bound : Nat} (cut : ConnectedAtWidth G bound) :
    ConnectedShoreNode (G := G) bound bound :=
  cut.realization.toConnectedShoreNodeOfVertexMinimal rotation minimal
    cut.side_connected cut.complement_connected bound cut.card_le

@[simp]
theorem ConnectedAtWidth.toConnectedShoreNode_shore
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {bound : Nat} (cut : ConnectedAtWidth G bound) :
    (cut.toConnectedShoreNode rotation minimal).shore =
      incidentEdgeShore G cut.realization.side :=
  rfl

/-- Consumer-facing form of the bounded-cut horn: in a graph-backed least
counterexample, every bounded cyclic-cut witness supplies a connected shore
node with its literal exact support state. -/
theorem exists_connectedShoreNode_of_hasCyclicEdgeCutOfSizeAtMost
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (bound : Nat) (hcut : HasCyclicEdgeCutOfSizeAtMost G bound) :
    Nonempty (ConnectedShoreNode (G := G) bound bound) := by
  have hconnected : G.Connected := by
    rw [← rotationPrimalGraph_toRotationSystem_eq G rotation]
    exact minimal.primalConnected
  rcases exists_connectedAtWidth_of_hasCyclicEdgeCutOfSizeAtMost
      (G := G) hconnected bound hcut with ⟨cut⟩
  exact ⟨cut.toConnectedShoreNode rotation minimal⟩

/-- **Cyclic-cut consumer form of physical replacement.**  Two strictly
nested connected cyclic-cut shores with the same exact phased support state
produce a strictly smaller endpoint-simple counterexample.  This theorem is
the direct M1-to-M2 seam: the inputs are literal graph cuts, not abstract
state-supply hypotheses. -/
theorem exists_endpointSimple_replacement_of_nested_connected_cyclicCuts
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (bound : Nat)
    {oldCut newCut : Finset G.edgeSet}
    (oldRealization : CyclicEdgeCutRealization G oldCut)
    (newRealization : CyclicEdgeCutRealization G newCut)
    (hOldSide : (G.induce oldRealization.side).Connected)
    (hOldComplement :
      (G.induce (fun vertex => ¬ oldRealization.side vertex)).Connected)
    (hNewSide : (G.induce newRealization.side).Connected)
    (hNewComplement :
      (G.induce (fun vertex => ¬ newRealization.side vertex)).Connected)
    (hOldCard : oldCut.card ≤ bound)
    (hNewCard : newCut.card ≤ bound)
    (hproper : incidentEdgeShore G newRealization.side ⊂
      incidentEdgeShore G oldRealization.side)
    (heq :
      (oldRealization.toConnectedShoreNodeOfVertexMinimal rotation minimal
        hOldSide hOldComplement bound hOldCard).cardPhasedState
          rotation minimal =
      (newRealization.toConnectedShoreNodeOfVertexMinimal rotation minimal
        hNewSide hNewComplement bound hNewCard).cardPhasedState
          rotation minimal) :
    EndpointSimpleCounterexampleBelow.{u} (Fintype.card V) := by
  let oldNode :=
    (oldRealization.toConnectedShoreNodeOfVertexMinimal rotation minimal
      hOldSide hOldComplement bound hOldCard).toLiteral rotation minimal
  let newNode :=
    (newRealization.toConnectedShoreNodeOfVertexMinimal rotation minimal
      hNewSide hNewComplement bound hNewCard).toLiteral rotation minimal
  apply exists_endpointSimple_replacement_of_cardPhasedState_eq
    rotation minimal.toBridgelessSphericalCubicMapData minimal.notColorable
    oldNode newNode
  · simpa [oldNode, newNode] using hproper
  · simpa [oldNode, newNode, ConnectedShoreNode.cardPhasedState] using heq

end

end CyclicEdgeCutRealization

end Mettapedia.GraphTheory.FourColor
