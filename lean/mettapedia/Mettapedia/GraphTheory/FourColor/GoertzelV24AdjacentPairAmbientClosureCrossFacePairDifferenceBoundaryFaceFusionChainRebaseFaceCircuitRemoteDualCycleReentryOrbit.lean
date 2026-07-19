import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRemoteDualCycleReentry

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

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every ambient edge has adjacent endpoints representing its unordered
edge value. -/
theorem exists_adjacent_endpoints_of_edge
    (edge : G.edgeSet) :
    ∃ first second : V,
      first ≠ second ∧ G.Adj first second ∧ edge.1 = s(first, second) := by
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
  exact ⟨first, second, hadj.ne, hadj, hedgeValue⟩

/-- A cross-face restart indexed by its literal target primal edge.  The
target carries a complete adjacent-pair fusion normal form, while the
geometry records whether it was crossed by a remote facial-dual cycle or
was the gain edge of a closure-recovery face transfer. -/
structure CrossFaceAdjacentPairReentry
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : AdjacentPairData G)
    (targetEdge : G.edgeSet) : Prop where
  target_ne_central :
    centralEdge
        (RecoveredRotationOrderedData graphData minimal baseData) ≠
      targetEdge
  target_fusion :
    ∃ firstVertex secondVertex : V,
      firstVertex ≠ secondVertex ∧
        G.Adj firstVertex secondVertex ∧
        targetEdge.1 = s(firstVertex, secondVertex) ∧
        HasRotationOrderedFusionTerminalOrRebasePumping
          graphData minimal firstVertex secondVertex
  geometry :
    (∃ circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
          minimal baseData,
        circuit.IsLengthMinimal ∧
          ∃ cycle :
              CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
                circuit,
            targetEdge ∈ dualWalkCrossingEdges
              (orbitFaceBoundary graphData.toRotationSystem)
              (Finset.univ : Finset
                (OrbitFace graphData.toRotationSystem))
              (pairwiseUniqueSharedInteriorEdges graphData minimal)
              cycle.walk) ∨
      ∃ circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
          minimal baseData,
        circuit.IsLengthMinimal ∧
          ∃ rotated : CrossCentralExactFaceCertifiedRebaseCircuit graphData
              minimal baseData,
            rotated.arcLength = circuit.arcLength ∧
              ∃ transfer : ClosureRecoveryFaceTransfer rotated,
                targetEdge = transfer.recovery.edge

namespace CrossCentralExactFaceCertifiedRebaseCircuit

/-- The shortest exact rebase circuit either exposes the constant-face
port-pairing obstruction or supplies a geometrically witnessed restart at
a different primal edge. -/
theorem IsLengthMinimal.exists_endpointPortPairingReductionObstruction_or_crossFaceAdjacentPairReentry
    {circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    (hminimal : circuit.IsLengthMinimal) :
    (∃ cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
        minimal baseData,
      cell.EndpointPortPairingReductionObstruction) ∨
      ∃ targetEdge : G.edgeSet,
        CrossFaceAdjacentPairReentry graphData minimal baseData targetEdge := by
  rcases
      hminimal.exists_endpointPortPairingReductionObstruction_or_remoteDualCycle_or_rotated_recoveryFaceTransfer
    with hcell | hremote | htransfer
  · exact Or.inl hcell
  · rcases hremote with ⟨cycle⟩
    have hpositive : 0 < cycle.walk.length := by
      have hthree := cycle.isCycle.three_le_length
      omega
    let step : Fin cycle.walk.length := ⟨0, hpositive⟩
    let targetEdge : G.edgeSet :=
      dualWalkCrossingEdge
        (orbitFaceBoundary graphData.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace graphData.toRotationSystem))
        (pairwiseUniqueSharedInteriorEdges graphData minimal)
        cycle.walk step
    have htargetFace : targetEdge ∈
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
          targetEdge := by
      intro hedge
      exact hcentralOff (hedge ▸ htargetFace)
    rcases exists_adjacent_endpoints_of_edge targetEdge with
      ⟨first, second, hne, hadj, htargetValue⟩
    have hnormal :=
      exists_rotationOrderedCyclicKempeFusionChainNormalForm_of_vertexMinimalTaitCounterexample
        graphData minimal hadj
    refine Or.inr ⟨targetEdge, {
      target_ne_central := hcentralNe
      target_fusion :=
        ⟨first, second, hne, hadj, htargetValue,
          hasRotationOrderedFusionTerminalOrRebasePumping_of_normalForm
            graphData minimal hnormal⟩
      geometry := Or.inl ⟨circuit, hminimal, cycle, ?_⟩ }⟩
    exact (mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))
      (pairwiseUniqueSharedInteriorEdges graphData minimal)
      cycle.walk targetEdge).2 ⟨step, rfl⟩
  · rcases htransfer with
      ⟨rotated, hlength, ⟨transfer⟩⟩
    let targetEdge : G.edgeSet := transfer.recovery.edge
    have htargetFace : targetEdge ∈
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
          targetEdge := by
      intro hedge
      exact hcentralOff (hedge ▸ htargetFace)
    rcases exists_adjacent_endpoints_of_edge targetEdge with
      ⟨first, second, hne, hadj, htargetValue⟩
    have hnormal :=
      exists_rotationOrderedCyclicKempeFusionChainNormalForm_of_vertexMinimalTaitCounterexample
        graphData minimal hadj
    exact Or.inr ⟨targetEdge, {
      target_ne_central := hcentralNe
      target_fusion :=
        ⟨first, second, hne, hadj, htargetValue,
          hasRotationOrderedFusionTerminalOrRebasePumping_of_normalForm
            graphData minimal hnormal⟩
      geometry := Or.inr
        ⟨circuit, hminimal, rotated, hlength, transfer, rfl⟩ }⟩

end CrossCentralExactFaceCertifiedRebaseCircuit

/-- A finite exact-state pumping run reaches a certified stop, exposes the
constant-face port-pairing obstruction, or returns a geometrically
witnessed successor edge for the adjacent-pair machine. -/
theorem CrossCentralExactFaceCutPair.exists_reachable_certifiedStopping_or_endpointPortPairingReductionObstruction_or_crossFaceAdjacentPairReentry
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
      ∃ targetEdge : G.edgeSet,
        CrossFaceAdjacentPairReentry graphData minimal baseData targetEdge := by
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
        hminimal.exists_endpointPortPairingReductionObstruction_or_crossFaceAdjacentPairReentry
      with hcell | hreentry
    · exact Or.inr (Or.inl hcell)
    · exact Or.inr (Or.inr hreentry)

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

namespace GoertzelV24RecoveredAdjacentPairFusionChainNormalForm

open GoertzelV24AdjacentPairInsertion.AdjacentPairData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

namespace RotationOrderedCyclicKempeFusionChainNormalForm

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}
  {normal : RotationOrderedCyclicKempeFusionChainNormalForm graphData
    minimal baseData}

/-- A launched exact-state pumping run retains either its reachable stop,
its local constant-face obstruction, or the full geometry of a cross-face
successor edge. -/
theorem CertifiedRebasePumpingLaunch.exists_reachable_certifiedStopping_or_endpointPortPairingReductionObstruction_or_crossFaceAdjacentPairReentry
    (launch : normal.CertifiedRebasePumpingLaunch) :
    (∃ (cross : (DeletedAdjacentPairGraph G
          (RecoveredRotationOrderedData graphData minimal baseData).firstVertex
          (RecoveredRotationOrderedData graphData minimal baseData).secondVertex).edgeSet)
        (pair : CrossCentralExactFaceCutPair graphData
          (RecoveredRotationOrderedData graphData minimal baseData) cross)
        (finish : CrossCentralExactFaceCutState graphData
          (RecoveredRotationOrderedData graphData minimal baseData)),
      Relation.ReflTransGen
          (CrossCentralExactFaceCertifiedRebaseTransition graphData minimal
            baseData) ⟨cross, pair⟩ finish ∧
        finish.CertifiedStoppingOutcome graphData minimal baseData) ∨
      (∃ cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell
          graphData minimal baseData,
        cell.EndpointPortPairingReductionObstruction) ∨
      ∃ targetEdge : G.edgeSet,
        CrossFaceAdjacentPairReentry graphData minimal baseData targetEdge := by
  unfold CertifiedRebasePumpingLaunch at launch
  dsimp only at launch
  rcases launch with hbc | hcb
  · rcases hbc with ⟨site, pair, _hprefix, _hsuffix, outcome⟩
    rcases
        pair.exists_reachable_certifiedStopping_or_endpointPortPairingReductionObstruction_or_crossFaceAdjacentPairReentry
          outcome with
      hstop | hloop
    · rcases hstop with ⟨finish, hreachable, hfinish⟩
      exact Or.inl ⟨site.1, pair, finish, hreachable, hfinish⟩
    · rcases hloop with hcell | hreentry
      · exact Or.inr (Or.inl hcell)
      · exact Or.inr (Or.inr hreentry)
  · rcases hcb with ⟨site, pair, _hprefix, _hsuffix, outcome⟩
    rcases
        pair.exists_reachable_certifiedStopping_or_endpointPortPairingReductionObstruction_or_crossFaceAdjacentPairReentry
          outcome with
      hstop | hloop
    · rcases hstop with ⟨finish, hreachable, hfinish⟩
      exact Or.inl ⟨site.1, pair, finish, hreachable, hfinish⟩
    · rcases hloop with hcell | hreentry
      · exact Or.inr (Or.inl hcell)
      · exact Or.inr (Or.inr hreentry)

/-- The complete adjacent-pair normal form has four explicit outcomes:
a fusion terminal, a reachable certified rebase stop, the constant-face
port-pairing obstruction, or a geometrically witnessed cross-face
successor edge. -/
theorem terminalFusion_or_reachable_certifiedStopping_or_endpointPortPairingReductionObstruction_or_crossFaceAdjacentPairReentry
    (normal : RotationOrderedCyclicKempeFusionChainNormalForm graphData
      minimal baseData) :
    normal.TerminalFusionOutcome ∨
      (∃ (cross : (DeletedAdjacentPairGraph G
            (RecoveredRotationOrderedData graphData minimal baseData).firstVertex
            (RecoveredRotationOrderedData graphData minimal baseData).secondVertex).edgeSet)
          (pair : CrossCentralExactFaceCutPair graphData
            (RecoveredRotationOrderedData graphData minimal baseData) cross)
          (finish : CrossCentralExactFaceCutState graphData
            (RecoveredRotationOrderedData graphData minimal baseData)),
        Relation.ReflTransGen
            (CrossCentralExactFaceCertifiedRebaseTransition graphData minimal
              baseData) ⟨cross, pair⟩ finish ∧
          finish.CertifiedStoppingOutcome graphData minimal baseData) ∨
      (∃ cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell
          graphData minimal baseData,
        cell.EndpointPortPairingReductionObstruction) ∨
      ∃ targetEdge : G.edgeSet,
        CrossFaceAdjacentPairReentry graphData minimal baseData targetEdge := by
  rcases normal.terminalFusion_or_certifiedRebasePumpingLaunch with
    hterminal | hlaunch
  · exact Or.inl hterminal
  · rcases
        hlaunch.exists_reachable_certifiedStopping_or_endpointPortPairingReductionObstruction_or_crossFaceAdjacentPairReentry
      with hstop | hloop
    · exact Or.inr (Or.inl hstop)
    · rcases hloop with hcell | hreentry
      · exact Or.inr (Or.inr (Or.inl hcell))
      · exact Or.inr (Or.inr (Or.inr hreentry))

end RotationOrderedCyclicKempeFusionChainNormalForm

end GoertzelV24RecoveredAdjacentPairFusionChainNormalForm

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- A structural target of the all-face adjacent-pair machine, indexed by
the directed ambient edge whose ordered endpoints were deleted. -/
def RotationOrderedFusionStructuralTargetAtDart
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (dart : G.Dart) : Prop :=
  ∃ (baseData : AdjacentPairData G)
      (normal : RotationOrderedCyclicKempeFusionChainNormalForm graphData
        minimal baseData),
    centralDart
        (RecoveredRotationOrderedData graphData minimal
          baseData).centralAdjacent = dart ∧
      (normal.TerminalFusionOutcome ∨
        (∃ (cross : (DeletedAdjacentPairGraph G
              (RecoveredRotationOrderedData graphData minimal
                baseData).firstVertex
              (RecoveredRotationOrderedData graphData minimal
                baseData).secondVertex).edgeSet)
            (pair : CrossCentralExactFaceCutPair graphData
              (RecoveredRotationOrderedData graphData minimal baseData)
              cross)
            (finish : CrossCentralExactFaceCutState graphData
              (RecoveredRotationOrderedData graphData minimal baseData)),
          Relation.ReflTransGen
              (CrossCentralExactFaceCertifiedRebaseTransition graphData
                minimal baseData) ⟨cross, pair⟩ finish ∧
            finish.CertifiedStoppingOutcome graphData minimal baseData) ∨
        ∃ cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell
            graphData minimal baseData,
          cell.EndpointPortPairingReductionObstruction)

/-- The cross-face successor relation on directed ambient edges.  Every
step retains the source orientation, the target orientation and fusion
normal form, and the complete remote-cycle or recovery-edge geometry. -/
def RotationOrderedFusionCrossFaceDartReentry
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (source target : G.Dart) : Prop :=
  ∃ (baseData : AdjacentPairData G) (targetEdge : G.edgeSet),
    centralDart
        (RecoveredRotationOrderedData graphData minimal
          baseData).centralAdjacent = source ∧
      CrossFaceAdjacentPairReentry graphData minimal baseData targetEdge ∧
      targetEdge.1 = target.edge ∧
      HasRotationOrderedFusionTerminalOrRebasePumping
        graphData minimal target.fst target.snd

/-- A cross-face successor is supported on a genuinely different ambient
edge, hence it is also a different directed edge. -/
theorem RotationOrderedFusionCrossFaceDartReentry.ne
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {source target : G.Dart}
    (reentry : RotationOrderedFusionCrossFaceDartReentry graphData minimal
      source target) :
    source ≠ target := by
  rcases reentry with
    ⟨baseData, targetEdge, hsource, htarget, hedge, _htargetFusion⟩
  intro heq
  apply htarget.target_ne_central
  apply Subtype.ext
  have hdartEdge := congrArg SimpleGraph.Dart.edge (hsource.trans heq)
  exact hdartEdge.trans hedge.symm

/-- At every directed ambient edge, the complete all-face machine either
reaches a named structural target or supplies a geometrically certified
successor with an aligned target orientation.  No restriction on face
sizes enters this alternative. -/
theorem rotationOrderedFusionStructuralTarget_or_exists_crossFaceDartReentry
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (source : G.Dart) :
    RotationOrderedFusionStructuralTargetAtDart graphData minimal source ∨
      ∃ target : G.Dart,
        RotationOrderedFusionCrossFaceDartReentry graphData minimal source
          target := by
  rcases
      exists_rotationOrderedCyclicKempeFusionChainNormalForm_of_vertexMinimalTaitCounterexample
        graphData minimal source.2 with
    ⟨baseData, hfirst, hsecond, ⟨normal⟩⟩
  have hcentral :
      centralDart
          (RecoveredRotationOrderedData graphData minimal
            baseData).centralAdjacent = source := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext hfirst hsecond
  rcases
      normal.terminalFusion_or_reachable_certifiedStopping_or_endpointPortPairingReductionObstruction_or_crossFaceAdjacentPairReentry
    with hterminal | hrest
  · exact Or.inl ⟨baseData, normal, hcentral, Or.inl hterminal⟩
  · rcases hrest with hstop | hrest
    · exact Or.inl ⟨baseData, normal, hcentral,
        Or.inr (Or.inl hstop)⟩
    · rcases hrest with hcell | hreentry
      · exact Or.inl ⟨baseData, normal, hcentral,
          Or.inr (Or.inr hcell)⟩
      · rcases hreentry with ⟨targetEdge, htarget⟩
        rcases htarget.target_fusion with
          ⟨first, second, _hne, hadj, htargetValue, htargetFusion⟩
        let target : G.Dart := centralDart hadj
        have hedge : targetEdge.1 = target.edge := by
          exact htargetValue
        have hfusion :
            HasRotationOrderedFusionTerminalOrRebasePumping
              graphData minimal target.fst target.snd := by
          simpa [target, centralDart] using htargetFusion
        exact Or.inr
          ⟨target, baseData, targetEdge, hcentral, htarget, hedge, hfusion⟩

/-- Starting from any directed ambient edge, finiteness now supplies the
complementary all-face existence arm: a structural target is reachable,
or a nonempty closed orbit of geometrically witnessed, orientation-aligned
cross-face re-entries is reachable. -/
theorem exists_reachable_rotationOrderedFusionStructuralTarget_or_crossFaceDartReentryCycle
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (start : G.Dart) :
    (∃ finish : G.Dart,
        Relation.ReflTransGen
            (RotationOrderedFusionCrossFaceDartReentry graphData minimal)
            start finish ∧
          RotationOrderedFusionStructuralTargetAtDart graphData minimal
            finish) ∨
      ∃ cycleDart : G.Dart,
        Relation.ReflTransGen
            (RotationOrderedFusionCrossFaceDartReentry graphData minimal)
            start cycleDart ∧
          Relation.TransGen
            (RotationOrderedFusionCrossFaceDartReentry graphData minimal)
            cycleDart cycleDart := by
  exact finite_reflTransGen_terminal_or_transGen_cycle
    (RotationOrderedFusionCrossFaceDartReentry graphData minimal)
    (RotationOrderedFusionStructuralTargetAtDart graphData minimal)
    (rotationOrderedFusionStructuralTarget_or_exists_crossFaceDartReentry
      graphData minimal) start

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
