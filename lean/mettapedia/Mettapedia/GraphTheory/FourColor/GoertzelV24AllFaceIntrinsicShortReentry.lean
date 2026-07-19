import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceAdjacentPairTriangleRefinement

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24DualPathTransversal
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24MinimalFaceIntersections
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

namespace CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- An intrinsic target of a short remote primal cut.  The short cycle is
a source-supported dual triangle, and the target is one of its crossed
singleton-star edges. -/
def IntrinsicShortFusionTarget
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    (targetEdge : G.edgeSet) : Prop :=
  ∃ first second : V,
    first ≠ second ∧ G.Adj first second ∧
      targetEdge.1 = s(first, second) ∧
      centralEdge
          (RecoveredRotationOrderedData graphData minimal baseData) ≠
        targetEdge ∧
      (∀ port : Fin 4,
        boundaryEdge
            (baseData.rotationOrderedData graphData
              minimal.spherical.cubic minimal.vertexRotationCyclic) port ≠
          targetEdge) ∧
      HasRotationOrderedFusionKempeOrbitEscape
        graphData minimal first second ∧
      Nonempty cycle.SingletonPrimalCutProfile ∧
      targetEdge ∈ cycle.crossingEdges

/-- A singleton cut supplies a crossed star edge carrying a complete
fusion/Kempe package. -/
theorem SingletonPrimalCutProfile.exists_intrinsicShortFusionTarget
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    (profile : cycle.SingletonPrimalCutProfile) :
    ∃ targetEdge : G.edgeSet,
      cycle.IntrinsicShortFusionTarget targetEdge := by
  have hpositive : 0 < cycle.walk.length := by
    rw [profile.length_eq_three]
    omega
  let step : Fin cycle.walk.length := ⟨0, hpositive⟩
  let targetEdge : G.edgeSet :=
    dualWalkCrossingEdge
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))
      (pairwiseUniqueSharedInteriorEdges graphData minimal)
      cycle.walk step
  have htargetCrossing : targetEdge ∈ cycle.crossingEdges := by
    exact (mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
      (pairwiseUniqueSharedInteriorEdges graphData minimal)
      cycle.walk targetEdge).2 ⟨step, rfl⟩
  rcases exists_adjacent_endpoints_of_edge targetEdge with
    ⟨first, second, hne, hadj, hvalue⟩
  have hfusion :=
    GoertzelV24MinimalTriangleFree.exists_rotationOrderedFusionTerminalOrRebasePumping_of_vertexMinimalTaitCounterexample
      graphData minimal hadj
  have hkempe : HasRotationOrderedFusionKempeOrbitEscape
      graphData minimal first second :=
    hasRotationOrderedFusionKempeOrbitEscape_of_terminalOrRebasePumping
      graphData minimal hfusion
  exact ⟨targetEdge, first, second, hne, hadj, hvalue,
    cycle.crossingEdge_ne_central htargetCrossing,
    fun port => cycle.crossingEdge_ne_boundary htargetCrossing port,
    hkempe, ⟨profile⟩, htargetCrossing⟩

/-- Every remote cycle either exits through a large exact separator or
refines to a source-supported singleton triangle supplying an intrinsic
target. -/
theorem exists_longPrimalCut_or_intrinsicShortFusionTarget
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit) :
    Nonempty cycle.LongPrimalCutProfile ∨
      ∃ shortCycle :
          CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
            rebaseCircuit,
        ∃ targetEdge : G.edgeSet,
          shortCycle.IntrinsicShortFusionTarget targetEdge := by
  rcases cycle.exists_longPrimalCut_or_singletonTriangleRefinement with
    hlong | ⟨shortCycle, ⟨profile⟩⟩
  · exact Or.inl hlong
  · exact Or.inr ⟨shortCycle,
      profile.exists_intrinsicShortFusionTarget⟩

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

/-- A recursive all-face step is supported either by the intrinsic target
of a short remote cut or by a literal recovery transfer. -/
def IntrinsicShortOrRecoveryGeometry
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : AdjacentPairData G)
    (targetEdge : G.edgeSet) : Prop :=
  (∃ circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
        minimal baseData,
      circuit.IsLengthMinimal ∧
        ∃ cycle :
            CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
              circuit,
          cycle.IntrinsicShortFusionTarget targetEdge) ∨
    ∃ circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
        minimal baseData,
      circuit.IsLengthMinimal ∧
        ∃ rotated : CrossCentralExactFaceCertifiedRebaseCircuit graphData
            minimal baseData,
          rotated.arcLength = circuit.arcLength ∧
            ∃ transfer : ClosureRecoveryFaceTransfer rotated,
              targetEdge = transfer.recovery.edge

/-- A long remote primal separator reached from a directed source edge. -/
def RotationOrderedFusionLargeRemotePrimalCutAtDart
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (source : G.Dart) : Prop :=
  ∃ (baseData : AdjacentPairData G)
      (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
        minimal baseData)
      (cycle :
        CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
          circuit),
    centralDart
        (RecoveredRotationOrderedData graphData minimal
          baseData).centralAdjacent = source ∧
      circuit.IsLengthMinimal ∧ Nonempty cycle.LongPrimalCutProfile

/-- The recursive relation after large separators have been split off.
Every remote target is intrinsic to a singleton-star triangle; the other
constructor is a literal recovery edge. -/
def RotationOrderedFusionIntrinsicShortOrRecoveryDartReentry
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (source target : G.Dart) : Prop :=
  ∃ (baseData : AdjacentPairData G) (targetEdge : G.edgeSet),
    centralDart
        (RecoveredRotationOrderedData graphData minimal
          baseData).centralAdjacent = source ∧
      centralEdge
          (RecoveredRotationOrderedData graphData minimal baseData) ≠
        targetEdge ∧
      targetEdge.1 = target.edge ∧
      HasRotationOrderedFusionKempeOrbitEscape
        graphData minimal target.fst target.snd ∧
      IntrinsicShortOrRecoveryGeometry graphData minimal baseData targetEdge

/-- An intrinsic-short/recovery step changes the directed ambient edge. -/
theorem RotationOrderedFusionIntrinsicShortOrRecoveryDartReentry.ne
    {source target : G.Dart}
    (reentry : RotationOrderedFusionIntrinsicShortOrRecoveryDartReentry
      graphData minimal source target) :
    source ≠ target := by
  rcases reentry with
    ⟨_baseData, targetEdge, hsource, hne, hedge, _hkempe, _hgeometry⟩
  intro heq
  apply hne
  apply Subtype.ext
  have hdartEdge := congrArg SimpleGraph.Dart.edge (hsource.trans heq)
  exact hdartEdge.trans hedge.symm

/-- At every dart, the all-face machine reaches a structural target,
exposes a large exact remote separator, or takes an intrinsic-short/recovery
step. -/
theorem rotationOrderedFusionStructuralTarget_or_largeRemotePrimalCut_or_exists_intrinsicShortOrRecoveryDartReentry
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (source : G.Dart) :
    RotationOrderedFusionStructuralTargetAtDart graphData minimal source ∨
      RotationOrderedFusionLargeRemotePrimalCutAtDart graphData minimal
        source ∨
      ∃ target : G.Dart,
        RotationOrderedFusionIntrinsicShortOrRecoveryDartReentry
          graphData minimal source target := by
  rcases rotationOrderedFusionStructuralTarget_or_exists_crossFaceDartReentry
      graphData minimal source with hterminal | ⟨target, hreentry⟩
  · exact Or.inl hterminal
  · rcases hreentry with
      ⟨baseData, targetEdge, hsource, htarget, hedge, hfusion⟩
    rcases htarget.geometry with hremote | hrecovery
    · rcases hremote with ⟨circuit, hminimal, cycle, _htargetCrossing⟩
      rcases cycle.exists_longPrimalCut_or_intrinsicShortFusionTarget with
        hlong | ⟨shortCycle, intrinsicEdge, hintrinsic⟩
      · exact Or.inr (Or.inl
          ⟨baseData, circuit, cycle, hsource, hminimal, hlong⟩)
      · have hintrinsic' := hintrinsic
        rcases hintrinsic with
          ⟨first, second, _hne, hadj, hvalue, hintrinsicNe,
            _hboundary, hkempe, _hshortGeometry⟩
        let intrinsicTarget : G.Dart := centralDart hadj
        have hedgeIntrinsic : intrinsicEdge.1 = intrinsicTarget.edge :=
          hvalue
        exact Or.inr (Or.inr ⟨intrinsicTarget, baseData, intrinsicEdge,
          hsource, hintrinsicNe, hedgeIntrinsic, hkempe,
          Or.inl ⟨circuit, hminimal, shortCycle, hintrinsic'⟩⟩)
    · have hkempe : HasRotationOrderedFusionKempeOrbitEscape graphData
          minimal target.fst target.snd :=
        hasRotationOrderedFusionKempeOrbitEscape_of_terminalOrRebasePumping
          graphData minimal hfusion
      exact Or.inr (Or.inr ⟨target, baseData, targetEdge, hsource,
        htarget.target_ne_central, hedge, hkempe, Or.inr hrecovery⟩)

/-- Finite all-face iteration now has three honest outcomes: a structural
target, a reachable large separator, or a nonempty closed orbit made only
of intrinsic short-cut and recovery steps. -/
theorem exists_reachable_rotationOrderedFusionStructuralTarget_or_largeRemotePrimalCut_or_intrinsicShortOrRecoveryDartReentryCycle
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (start : G.Dart) :
    (∃ finish : G.Dart,
        Relation.ReflTransGen
            (RotationOrderedFusionIntrinsicShortOrRecoveryDartReentry
              graphData minimal) start finish ∧
          RotationOrderedFusionStructuralTargetAtDart graphData minimal
            finish) ∨
      (∃ finish : G.Dart,
        Relation.ReflTransGen
            (RotationOrderedFusionIntrinsicShortOrRecoveryDartReentry
              graphData minimal) start finish ∧
          RotationOrderedFusionLargeRemotePrimalCutAtDart graphData minimal
            finish) ∨
      ∃ cycleDart : G.Dart,
        Relation.ReflTransGen
            (RotationOrderedFusionIntrinsicShortOrRecoveryDartReentry
              graphData minimal) start cycleDart ∧
          Relation.TransGen
            (RotationOrderedFusionIntrinsicShortOrRecoveryDartReentry
              graphData minimal) cycleDart cycleDart := by
  let transition :=
    RotationOrderedFusionIntrinsicShortOrRecoveryDartReentry
      graphData minimal
  let terminal := fun dart : G.Dart =>
    RotationOrderedFusionStructuralTargetAtDart graphData minimal dart ∨
      RotationOrderedFusionLargeRemotePrimalCutAtDart graphData minimal dart
  have hterminalOrStep : ∀ dart : G.Dart,
      terminal dart ∨ ∃ target, transition dart target := by
    intro dart
    rcases
        rotationOrderedFusionStructuralTarget_or_largeRemotePrimalCut_or_exists_intrinsicShortOrRecoveryDartReentry
          graphData minimal dart with hstructural | hlarge | hstep
    · exact Or.inl (Or.inl hstructural)
    · exact Or.inl (Or.inr hlarge)
    · exact Or.inr hstep
  rcases finite_reflTransGen_terminal_or_transGen_cycle transition terminal
      hterminalOrStep start with hfinish | hcycle
  · rcases hfinish with ⟨finish, hreach, hstructural | hlarge⟩
    · exact Or.inl ⟨finish, hreach, hstructural⟩
    · exact Or.inr (Or.inl ⟨finish, hreach, hlarge⟩)
  · exact Or.inr (Or.inr hcycle)

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
