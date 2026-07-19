import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitPortPairingDescent
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphTaitBridge

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24RotationEdgeBridge
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- A word compatible with the alternate square pairing and simultaneously
blocked at the restored adjacent pair is necessarily all-equal. -/
theorem SquareBoundaryWord.allEqual_of_join12_30_compatible_of_sameSidePairs
    (word : SquareBoundaryWord)
    (hcompatible : SquareReductionSide.join12_30.Compatible word)
    (hsame : word 0 = word 1 ∧ word 2 = word 3) :
    word.AllEqual := by
  have halternate : word 1 = word 2 ∧ word 3 = word 0 := by
    simpa [SquareReductionSide.Compatible,
      SquareReductionSide.join01_23,
      SquareReductionSide.join12_30] using hcompatible
  exact ⟨hsame.1, halternate.1, hsame.2⟩

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- If the alternate `12|30` planar reduction is bridge-free, vertex
minimality colors it.  Restriction to the actual four-pole is compatible
with `12|30`; ambient noncolorability then forces that boundary word into
the all-equal sector. -/
theorem exists_deletedColoring_allEqual_of_reductionJoin12_30_edgeBridgeFree_of_order
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (horder : data.PortsFollowCyclicDeletedBoundaryOrder graphData)
    (hbridgeFree : EdgeBridgeFree
      (data.reductionRotationSystem graphData
        SquareReductionSide.join12_30)) :
    ∃ deletedColoring :
        (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).EdgeColoring Color,
      IsTaitEdgeColoring
          (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
          deletedColoring ∧
        SquareBoundaryWord.AllEqual
          (data.degreeTwoBoundaryData.colorWord deletedColoring) := by
  let hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have hcolorable : RotationSystemTaitColorable
      (data.reductionRotationSystem graphData
        SquareReductionSide.join12_30) :=
    data.reductionTaitColorable_of_edgeBridgeFree_of_order graphData minimal
      horder SquareReductionSide.join12_30 hbridgeFree
  rcases data.exists_deletedColoring_compatible_of_reductionTaitColorable
      graphData hcubic SquareReductionSide.join12_30 hcolorable with
    ⟨deletedColoring, hdeleted, hcompatible⟩
  have hsame :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.sameSidePairs_of_not_taitColorable
      data hcubic
        (graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
          graphData minimal)
        deletedColoring hdeleted
  exact ⟨deletedColoring, hdeleted,
    SquareBoundaryWord.allEqual_of_join12_30_compatible_of_sameSidePairs
      (data.degreeTwoBoundaryData.colorWord deletedColoring)
      hcompatible hsame⟩

/-- Thus the alternate reduction of an ordered adjacent pair has an exact
semantic dichotomy: it contains a bridge, or it yields a genuine all-equal
Tait state of the deleted four-pole. -/
theorem reductionJoin12_30_not_edgeBridgeFree_or_exists_deletedColoring_allEqual_of_order
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (horder : data.PortsFollowCyclicDeletedBoundaryOrder graphData) :
    (¬ EdgeBridgeFree (data.reductionRotationSystem graphData
        SquareReductionSide.join12_30)) ∨
      ∃ deletedColoring :
          (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).EdgeColoring Color,
        IsTaitEdgeColoring
            (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
            deletedColoring ∧
          SquareBoundaryWord.AllEqual
            (data.degreeTwoBoundaryData.colorWord deletedColoring) := by
  by_cases hbridgeFree : EdgeBridgeFree
      (data.reductionRotationSystem graphData
        SquareReductionSide.join12_30)
  · exact Or.inr
      (exists_deletedColoring_allEqual_of_reductionJoin12_30_edgeBridgeFree_of_order
        graphData minimal data horder hbridgeFree)
  · exact Or.inl hbridgeFree

/-- The unified geometric descent now lands in standard coloring and graph
obstructions.  The canonical pairing has an honest compatible deletion
coloring.  The alternate pairing either exposes a bridge in its planar
reduction or produces an honest all-equal deletion coloring. -/
theorem LocalizedStrictPortPairingDescent.exists_canonicalColoring_or_alternateBridge_or_allEqual
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    (horder : data.PortsFollowCyclicDeletedBoundaryOrder graphData)
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (descent : LocalizedStrictPortPairingDescent pair oldCross face) :
    (descent.reductionSide = SquareReductionSide.join01_23 ∧
      ∃ deletedColoring :
          (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).EdgeColoring Color,
        IsTaitEdgeColoring
            (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
            deletedColoring ∧
          SquareReductionSide.join01_23.Compatible
            (data.degreeTwoBoundaryData.colorWord deletedColoring)) ∨
      (descent.reductionSide = SquareReductionSide.join12_30 ∧
        ((¬ EdgeBridgeFree (data.reductionRotationSystem graphData
            SquareReductionSide.join12_30)) ∨
          ∃ deletedColoring :
              (DeletedAdjacentPairGraph G data.firstVertex
                data.secondVertex).EdgeColoring Color,
            IsTaitEdgeColoring
                (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
                deletedColoring ∧
              SquareBoundaryWord.AllEqual
                (data.degreeTwoBoundaryData.colorWord deletedColoring))) := by
  cases descent with
  | sameSide _ =>
      left
      refine ⟨rfl, ?_⟩
      exact data.exists_deletedColoring_join01_23_compatible_of_order
        graphData minimal horder
  | mixedPort _ =>
      right
      refine ⟨rfl, ?_⟩
      exact
        reductionJoin12_30_not_edgeBridgeFree_or_exists_deletedColoring_allEqual_of_order
          graphData minimal data horder

/-- Named semantic form of the preceding reduction dichotomy. -/
def LocalizedStrictPortPairingDescent.ReductionObstructionOutcome
    {graphData : Data G}
    {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (descent : LocalizedStrictPortPairingDescent pair oldCross face) : Prop :=
  (descent.reductionSide = SquareReductionSide.join01_23 ∧
    ∃ deletedColoring :
        (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).EdgeColoring Color,
      IsTaitEdgeColoring
          (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
          deletedColoring ∧
        SquareReductionSide.join01_23.Compatible
          (data.degreeTwoBoundaryData.colorWord deletedColoring)) ∨
    (descent.reductionSide = SquareReductionSide.join12_30 ∧
      ((¬ EdgeBridgeFree (data.reductionRotationSystem graphData
          SquareReductionSide.join12_30)) ∨
        ∃ deletedColoring :
            (DeletedAdjacentPairGraph G data.firstVertex
              data.secondVertex).EdgeColoring Color,
          IsTaitEdgeColoring
              (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
              deletedColoring ∧
            SquareBoundaryWord.AllEqual
              (data.degreeTwoBoundaryData.colorWord deletedColoring)))

theorem LocalizedStrictPortPairingDescent.reductionObstructionOutcome
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    (horder : data.PortsFollowCyclicDeletedBoundaryOrder graphData)
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (descent : LocalizedStrictPortPairingDescent pair oldCross face) :
    descent.ReductionObstructionOutcome :=
  descent.exists_canonicalColoring_or_alternateBridge_or_allEqual
    minimal horder

/-- Every certified facial arc ends not only in strict geometric descent,
but in the corresponding standard reduction obstruction. -/
theorem CrossCentralExactFaceCertifiedRebaseArc.target_exists_portPairingReductionObstruction
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    (arc : CrossCentralExactFaceCertifiedRebaseArc graphData minimal
      baseData) :
    ∃ descent : LocalizedStrictPortPairingDescent
        arc.target.retainedIntersectionProfile arc.source.1
          arc.selectedFace,
      descent.ReductionObstructionOutcome := by
  rcases arc.target_strictPortPairingDescent with ⟨descent⟩
  refine ⟨descent, descent.reductionObstructionOutcome minimal ?_⟩
  exact baseData.rotationOrderedData_portsFollowCyclicDeletedBoundaryOrder
    graphData minimal.spherical.cubic minimal.vertexRotationCyclic

namespace CrossCentralExactFaceCertifiedRebaseInvolutionCell

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

/-- Both orientations of a constant-face cell carry the semantic reduction
obstruction attached to their strict port-pairing descents. -/
def EndpointPortPairingReductionObstruction
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData) : Prop :=
  (∃ descent : LocalizedStrictPortPairingDescent
      cell.source.retainedIntersectionProfile cell.target.1 cell.face,
    descent.ReductionObstructionOutcome) ∧
  (∃ descent : LocalizedStrictPortPairingDescent
      cell.target.retainedIntersectionProfile cell.source.1 cell.face,
    descent.ReductionObstructionOutcome)

theorem endpoint_portPairingReductionObstruction
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData) :
    cell.EndpointPortPairingReductionObstruction := by
  rcases cell.endpoint_strictPortPairingDescent with
    ⟨⟨sourceDescent⟩, ⟨targetDescent⟩⟩
  have horder :=
    baseData.rotationOrderedData_portsFollowCyclicDeletedBoundaryOrder
      graphData minimal.spherical.cubic minimal.vertexRotationCyclic
  exact
    ⟨⟨sourceDescent,
        sourceDescent.reductionObstructionOutcome minimal horder⟩,
      ⟨targetDescent,
        targetDescent.reductionObstructionOutcome minimal horder⟩⟩

end CrossCentralExactFaceCertifiedRebaseInvolutionCell

namespace CrossCentralExactFaceCertifiedRebaseCircuit

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

/-- The shortest-circuit trichotomy with the constant-face branch consumed
through square-reduction colorability and bridge obstruction. -/
theorem IsLengthMinimal.exists_endpointPortPairingReductionObstruction_or_remoteDualCycle_or_rotated_recoveryFaceTransfer
    {circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    (hminimal : circuit.IsLengthMinimal) :
    (∃ cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
        minimal baseData,
      cell.EndpointPortPairingReductionObstruction) ∨
      Nonempty (RemoteDualCycle circuit) ∨
      ∃ rotated : CrossCentralExactFaceCertifiedRebaseCircuit graphData
          minimal baseData,
        rotated.arcLength = circuit.arcLength ∧
          Nonempty (ClosureRecoveryFaceTransfer rotated) := by
  rcases
      hminimal.exists_endpointStrictPortPairingDescent_or_remoteDualCycle_or_rotated_recoveryFaceTransfer
    with hcell | hremote | htransfer
  · rcases hcell with ⟨cell, _hdescent⟩
    exact Or.inl ⟨cell, cell.endpoint_portPairingReductionObstruction⟩
  · exact Or.inr (Or.inl hremote)
  · exact Or.inr (Or.inr htransfer)

end CrossCentralExactFaceCertifiedRebaseCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
