import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferPrimalCutCollarChordCrossingRecovery
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitPortPairingReductionObstruction

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24DualPathTransversal
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24MinimalFaceIntersections
open GoertzelV24MinimalTriangleFree
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

/-- Any primal edge different from the restored central edge names a
genuinely different adjacent pair. -/
theorem exists_distinct_adjacentPair_of_edge_ne_central
    (edge : G.edgeSet)
    (hedge :
      centralEdge
          (RecoveredRotationOrderedData graphData minimal baseData) ≠
        edge) :
    ∃ first second : V,
      first ≠ second ∧ G.Adj first second ∧
        centralEdgeValue
            (RecoveredRotationOrderedData graphData minimal baseData) ≠
          s(first, second) := by
  have hedgeRepresentation :
      ∃ first second : V, edge.1 = s(first, second) := by
    refine Sym2.inductionOn (f := fun value : Sym2 V =>
      ∃ first second : V, value = s(first, second)) edge.1 ?_
    intro first second
    exact ⟨first, second, rfl⟩
  rcases hedgeRepresentation with ⟨first, second, hedgeValue⟩
  have hadj : G.Adj first second := by
    apply (SimpleGraph.mem_edgeSet G).mp
    rw [← hedgeValue]
    exact edge.2
  refine ⟨first, second, hadj.ne, hadj, ?_⟩
  intro hcentralValue
  apply hedge
  apply Subtype.ext
  exact hcentralValue.trans hedgeValue.symm

namespace CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- Any remote facial-dual cycle crosses a primal edge different from the
restored central edge.  Its two endpoints therefore give a genuinely new
adjacent pair, without a bound on the cycle length. -/
theorem exists_distinct_adjacentPair
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit) :
    ∃ first second : V,
      first ≠ second ∧ G.Adj first second ∧
        centralEdgeValue
            (RecoveredRotationOrderedData graphData minimal baseData) ≠
          s(first, second) := by
  have hpositive : 0 < cycle.walk.length := by
    have hthree := cycle.isCycle.three_le_length
    omega
  let step : Fin cycle.walk.length := ⟨0, hpositive⟩
  let crossing : G.edgeSet :=
    dualWalkCrossingEdge
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))
      (pairwiseUniqueSharedInteriorEdges graphData minimal)
      cycle.walk step
  have hcrossingFace : crossing ∈
      orbitFaceBoundary graphData.toRotationSystem
        (cycle.walk.getVert step.val).1 := by
    exact dualWalkCrossingEdge_mem_leftFace
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))
      (pairwiseUniqueSharedInteriorEdges graphData minimal)
      cycle.walk step
  have hcentralOff :
      centralEdge
          (RecoveredRotationOrderedData graphData minimal baseData) ∉
        orbitFaceBoundary graphData.toRotationSystem
          (cycle.walk.getVert step.val).1 :=
    cycle.central_not_mem (cycle.walk.getVert step.val)
      (cycle.walk.getVert_mem_support step.val)
  have hcentralNe :
      centralEdge
          (RecoveredRotationOrderedData graphData minimal baseData) ≠
        crossing := by
    intro hedge
    exact hcentralOff (hedge ▸ hcrossingFace)
  exact exists_distinct_adjacentPair_of_edge_ne_central crossing hcentralNe

/-- The remote-cycle branch is recursive in the same all-face dynamics:
one crossed primal edge gives a different adjacent pair whose complete
rotation-ordered fusion normal form either stops structurally or launches
certified exact-state pumping. -/
theorem exists_fusionTerminal_or_rebasePumping_at_distinct_adjacentPair
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit) :
    ∃ first second : V,
      first ≠ second ∧ G.Adj first second ∧
        centralEdgeValue
            (RecoveredRotationOrderedData graphData minimal baseData) ≠
          s(first, second) ∧
        HasRotationOrderedFusionTerminalOrRebasePumping
          graphData minimal first second := by
  rcases cycle.exists_distinct_adjacentPair with
    ⟨first, second, hne, hadj, hcentral⟩
  have hnormal :=
    exists_rotationOrderedCyclicKempeFusionChainNormalForm_of_vertexMinimalTaitCounterexample
      graphData minimal hadj
  exact ⟨first, second, hne, hadj, hcentral,
    hasRotationOrderedFusionTerminalOrRebasePumping_of_normalForm
      graphData minimal hnormal⟩

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

namespace ClosureRecoveryFaceTransfer

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- A concrete recovery gain itself lies on a selected face and therefore
names an adjacent pair different from the restored source pair. -/
theorem exists_distinct_adjacentPair
    (transfer : ClosureRecoveryFaceTransfer rebaseCircuit) :
    ∃ first second : V,
      first ≠ second ∧ G.Adj first second ∧
        centralEdgeValue
            (RecoveredRotationOrderedData graphData minimal baseData) ≠
          s(first, second) := by
  have hedgeFace : transfer.recovery.edge ∈
      orbitFaceBoundary graphData.toRotationSystem
        transfer.recovery.recoveryArc.selectedFace := by
    rw [transfer.recovery.recoveryArc_selectedFace]
    exact transfer.recovery.edge_mem_targetFace
  have hcentralOff :
      centralEdge
          (RecoveredRotationOrderedData graphData minimal baseData) ∉
        orbitFaceBoundary graphData.toRotationSystem
          transfer.recovery.recoveryArc.selectedFace :=
    transfer.recovery.recoveryArc.transition.central_not_mem_face
  have hcentralNe :
      centralEdge
          (RecoveredRotationOrderedData graphData minimal baseData) ≠
        transfer.recovery.edge := by
    intro hedge
    exact hcentralOff (hedge ▸ hedgeFace)
  exact exists_distinct_adjacentPair_of_edge_ne_central
    transfer.recovery.edge hcentralNe

/-- A single recovery transfer re-enters the complete adjacent-pair
fusion machine immediately; no transfer-cycle saturation premise is
needed. -/
theorem exists_fusionTerminal_or_rebasePumping_at_distinct_adjacentPair
    (transfer : ClosureRecoveryFaceTransfer rebaseCircuit) :
    ∃ first second : V,
      first ≠ second ∧ G.Adj first second ∧
        centralEdgeValue
            (RecoveredRotationOrderedData graphData minimal baseData) ≠
          s(first, second) ∧
        HasRotationOrderedFusionTerminalOrRebasePumping
          graphData minimal first second := by
  rcases transfer.exists_distinct_adjacentPair with
    ⟨first, second, hne, hadj, hcentral⟩
  have hnormal :=
    exists_rotationOrderedCyclicKempeFusionChainNormalForm_of_vertexMinimalTaitCounterexample
      graphData minimal hadj
  exact ⟨first, second, hne, hadj, hcentral,
    hasRotationOrderedFusionTerminalOrRebasePumping_of_normalForm
      graphData minimal hnormal⟩

end ClosureRecoveryFaceTransfer

namespace CrossCentralExactFaceCertifiedRebaseCircuit

/-- The shortest rebase-circuit trichotomy with its remote-dual-cycle
branch composed back into the adjacent-pair machine at a different primal
edge. -/
theorem IsLengthMinimal.exists_endpointPortPairingReductionObstruction_or_distinctAdjacentPairReentry_or_rotated_recoveryFaceTransfer
    {circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    (hminimal : circuit.IsLengthMinimal) :
    (∃ cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
        minimal baseData,
      cell.EndpointPortPairingReductionObstruction) ∨
      (∃ first second : V,
        first ≠ second ∧ G.Adj first second ∧
          centralEdgeValue
              (RecoveredRotationOrderedData graphData minimal baseData) ≠
            s(first, second) ∧
          HasRotationOrderedFusionTerminalOrRebasePumping
            graphData minimal first second) ∨
      ∃ rotated : CrossCentralExactFaceCertifiedRebaseCircuit graphData
          minimal baseData,
        rotated.arcLength = circuit.arcLength ∧
          Nonempty (ClosureRecoveryFaceTransfer rotated) := by
  rcases
      hminimal.exists_endpointPortPairingReductionObstruction_or_remoteDualCycle_or_rotated_recoveryFaceTransfer
    with hcell | hremote | htransfer
  · exact Or.inl hcell
  · rcases hremote with ⟨remote⟩
    exact Or.inr (Or.inl
      remote.exists_fusionTerminal_or_rebasePumping_at_distinct_adjacentPair)
  · exact Or.inr (Or.inr htransfer)

/-- Every shortest exact rebase loop is now consumed compositionally.
The constant-face cell exposes its standard square-reduction obstruction;
every nonconstant branch re-enters the complete fusion/pumping machine at
a different primal edge. -/
theorem IsLengthMinimal.exists_endpointPortPairingReductionObstruction_or_distinctAdjacentPairReentry
    {circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    (hminimal : circuit.IsLengthMinimal) :
    (∃ cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
        minimal baseData,
      cell.EndpointPortPairingReductionObstruction) ∨
      ∃ first second : V,
        first ≠ second ∧ G.Adj first second ∧
          centralEdgeValue
              (RecoveredRotationOrderedData graphData minimal baseData) ≠
            s(first, second) ∧
          HasRotationOrderedFusionTerminalOrRebasePumping
            graphData minimal first second := by
  rcases
      hminimal.exists_endpointPortPairingReductionObstruction_or_distinctAdjacentPairReentry_or_rotated_recoveryFaceTransfer
    with hcell | hreentry | htransfer
  · exact Or.inl hcell
  · exact Or.inr hreentry
  · rcases htransfer with ⟨_rotated, _hlength, ⟨transfer⟩⟩
    exact Or.inr
      transfer.exists_fusionTerminal_or_rebasePumping_at_distinct_adjacentPair

end CrossCentralExactFaceCertifiedRebaseCircuit

/-- A certified pumping outcome no longer leaves an opaque finite-state
loop.  Either a certified stop is reachable from the displayed exact cut
pair, or a shortest loop exposes the local port-pairing obstruction, or
the all-face fusion machine restarts at a different primal edge. -/
theorem CrossCentralExactFaceCutPair.exists_reachable_certifiedStopping_or_endpointPortPairingReductionObstruction_or_distinctAdjacentPairReentry
    {cross : (DeletedAdjacentPairGraph G baseData.firstVertex
      baseData.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) cross)
    (outcome : pair.CertifiedRebasePumpingOutcome minimal baseData) :
    (∃ finish,
        Relation.ReflTransGen
            (CrossCentralExactFaceCertifiedRebaseTransition graphData
              minimal baseData) ⟨cross, pair⟩ finish ∧
          finish.CertifiedStoppingOutcome graphData minimal baseData) ∨
      (∃ cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell
          graphData minimal baseData,
        cell.EndpointPortPairingReductionObstruction) ∨
      ∃ first second : V,
        first ≠ second ∧ G.Adj first second ∧
          centralEdgeValue
              (RecoveredRotationOrderedData graphData minimal baseData) ≠
            s(first, second) ∧
          HasRotationOrderedFusionTerminalOrRebasePumping
            graphData minimal first second := by
  unfold CrossCentralExactFaceCutPair.CertifiedRebasePumpingOutcome at outcome
  dsimp only at outcome
  rcases outcome with hstop | hcycle
  · exact Or.inl hstop
  · rcases hcycle with ⟨cycleState, _hreachable, hclosed⟩
    rcases
        CrossCentralExactFaceCertifiedRebaseCircuit.exists_lengthMinimal_of_transGen_cycle
          hclosed with
      ⟨circuit, hminimal⟩
    rcases
        hminimal.exists_endpointPortPairingReductionObstruction_or_distinctAdjacentPairReentry
      with hcell | hreentry
    · exact Or.inr (Or.inl hcell)
    · exact Or.inr (Or.inr hreentry)

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
