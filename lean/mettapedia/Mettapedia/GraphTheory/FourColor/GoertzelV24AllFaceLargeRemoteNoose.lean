import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicShortReentry
import Mettapedia.GraphTheory.FourColor.GoertzelV24DualNooseLiteralReplacement

/-!
# Large all-face separators as literal dual nooses

The all-face formation machine produces a `RemoteDualCycle` when it reaches
its large-separator outcome.  The physical replacement theorem is phrased in
terms of `DualNooseSide`.  This file identifies those two representations.

No separator geometry is stored as an additional hypothesis.  An anchor
vertex merely orients the already-existing facial-dual cycle by selecting its
component after the crossed primal edges are deleted.  Exact boundary and
connectedness of both sides then follow from the generic spherical-noose
theorem.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AllFaceLargeRemoteNoose

open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairBoundary
open GoertzelV24ConnectedEdgeShoreMajority
open GoertzelV24DualCycleCollar
open GoertzelV24DualNooseLiteralReplacement
open GoertzelV24DualPathTransversal
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24FramedDualCycleExactBoundary
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : GoertzelV24AdjacentPairBoundary.AdjacentPairData G}
  {rebaseCircuit :
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.CrossCentralExactFaceCertifiedRebaseCircuit
      graphData minimal baseData}

/-- Orient a remote facial-dual cycle by the component containing `anchor`.
The walk and its simplicity certificate are reused literally. -/
noncomputable def toDualNooseSideAt
    (cycle :
      GoertzelV24AdjacentPairInsertion.AdjacentPairData.CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    (anchor : V) : DualNooseSide graphData minimal where
  start := cycle.start
  walk := cycle.walk
  isCycle := cycle.isCycle
  component :=
    (G.deleteEdges (edgeFinsetValueSet cycle.crossingEdges)).connectedComponentMk
      anchor

@[simp]
theorem toDualNooseSideAt_walk
    (cycle :
      GoertzelV24AdjacentPairInsertion.AdjacentPairData.CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    (anchor : V) :
    (toDualNooseSideAt cycle anchor).walk = cycle.walk :=
  rfl

@[simp]
theorem toDualNooseSideAt_crossingEdges
    (cycle :
      GoertzelV24AdjacentPairInsertion.AdjacentPairData.CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    (anchor : V) :
    (toDualNooseSideAt cycle anchor).crossingEdges = cycle.crossingEdges :=
  rfl

/-- A large remote separator supplies the literal noose geometry consumed by
physical replacement: length at least five, exact crossed-edge boundary, and
connected vertex sides. -/
theorem dualNooseSideAt_geometry
    {cycle :
      AdjacentPairData.CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    (profile : cycle.LongPrimalCutProfile)
    (anchor : V) :
    5 ≤ (toDualNooseSideAt cycle anchor).walk.length ∧
      componentCrossingEdges
          (toDualNooseSideAt cycle anchor).crossingEdges
          (toDualNooseSideAt cycle anchor).component =
        (toDualNooseSideAt cycle anchor).crossingEdges ∧
      (G.induce (toDualNooseSideAt cycle anchor).side).Connected ∧
      (G.induce
          (fun vertex => ¬ (toDualNooseSideAt cycle anchor).side vertex)).Connected ∧
      (edgeShoreMiddleVertices G
          (toDualNooseSideAt cycle anchor).shore).card ≤
        (toDualNooseSideAt cycle anchor).walk.length := by
  let noose := toDualNooseSideAt cycle anchor
  have hgeometry := noose.exactBoundary_connectedSides
  exact ⟨profile.length_ge_five, hgeometry.1, hgeometry.2.1,
    hgeometry.2.2, noose.middle_card_le_walk_length⟩

/-- Consumer form of the large-separator terminal: at every chosen anchor it
produces one literal dual-noose side with the exact connected geometry used by
the replacement layer.  Boundedness, proper nesting, and state repetition are
deliberately not conclusions of this theorem. -/
theorem exists_dualNooseSideAt_of_largeRemotePrimalCutAtDart
    {source : G.Dart}
    (large :
      GoertzelV24AdjacentPairInsertion.AdjacentPairData.RotationOrderedFusionLargeRemotePrimalCutAtDart
        graphData minimal source)
    (anchor : V) :
    ∃ noose : DualNooseSide graphData minimal,
      5 ≤ noose.walk.length ∧
        componentCrossingEdges noose.crossingEdges noose.component =
          noose.crossingEdges ∧
        (G.induce noose.side).Connected ∧
        (G.induce (fun vertex => ¬ noose.side vertex)).Connected ∧
        (edgeShoreMiddleVertices G noose.shore).card ≤ noose.walk.length := by
  rcases large with
    ⟨baseData, circuit, cycle, _hsource, _hminimal, ⟨profile⟩⟩
  let noose := toDualNooseSideAt cycle anchor
  refine ⟨noose, ?_⟩
  simpa [noose] using dualNooseSideAt_geometry profile anchor

end

end GoertzelV24AllFaceLargeRemoteNoose

end Mettapedia.GraphTheory.FourColor
