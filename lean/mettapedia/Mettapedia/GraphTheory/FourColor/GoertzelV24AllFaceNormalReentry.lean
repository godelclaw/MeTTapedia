import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicTargetSourceArcCollar

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

namespace GoertzelV24AdjacentPairBoundary.AdjacentPairData

attribute [local instance]
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.fusionFaceNetworkGraphEdgeSetDecidableEq
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.fusionFaceNetworkRetainedVertexFintype
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.fusionFaceNetworkRetainedVertexDecidableEq

/-- Rotation ordering forgets the initially supplied port enumeration: two
adjacent-pair data with the same oriented endpoints normalize to the same
four-port datum. -/
theorem rotationOrderedData_eq_of_endpoints_eq
    (graphData : Data G) (first second : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : GoertzelV24FaceDualConnectedness.VertexRotationCyclic
      graphData.toRotationSystem)
    (hfirst : first.firstVertex = second.firstVertex)
    (hsecond : first.secondVertex = second.secondVertex) :
    first.rotationOrderedData graphData hcubic hrotation =
      second.rotationOrderedData graphData hcubic hrotation := by
  rw [AdjacentPairData.mk.injEq]
  refine ⟨hfirst, hsecond, ?_⟩
  funext port
  have hcentral : first.rotationCentralDart =
      second.rotationCentralDart := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext hfirst hsecond
  fin_cases port <;>
    simp [rotationOrderedData, rotationPortVertex, rotationPortDart, hcentral]

end GoertzelV24AdjacentPairBoundary.AdjacentPairData

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}

/-- If a target Kempe package is followed by a source normal at the same
directed edge, their possibly different initial port enumerations have the
same rotation-ordered datum. -/
theorem HasRotationOrderedFusionKempeOrbitEscape.exists_normal_aligned_with_sourceBase
    {source : G.Dart} {sourceBase : AdjacentPairData G}
    (escape : HasRotationOrderedFusionKempeOrbitEscape graphData minimal
      source.fst source.snd)
    (hsource : centralDart
        (RecoveredRotationOrderedData graphData minimal
          sourceBase).centralAdjacent = source) :
    ∃ (targetBase : AdjacentPairData G)
        (targetNormal : RotationOrderedCyclicKempeFusionChainNormalForm
          graphData minimal targetBase),
      (targetNormal.TerminalFusionOutcome ∨
          targetNormal.CertifiedRebasePumpingLaunch) ∧
        Nonempty targetNormal.KempeOrbitAdjacentEscape ∧
        RecoveredRotationOrderedData graphData minimal targetBase =
          RecoveredRotationOrderedData graphData minimal sourceBase := by
  rcases escape with
    ⟨targetBase, htargetFirst, htargetSecond, targetNormal,
      htargetOutcome, htargetEscape⟩
  have hsourceFirst : sourceBase.firstVertex = source.fst := by
    have hfst := congrArg (fun dart : G.Dart => dart.fst) hsource
    simpa [centralDart, RecoveredRotationOrderedData, rotationOrderedData]
      using hfst
  have hsourceSecond : sourceBase.secondVertex = source.snd := by
    have hsnd := congrArg (fun dart : G.Dart => dart.snd) hsource
    simpa [centralDart, RecoveredRotationOrderedData, rotationOrderedData]
      using hsnd
  have haligned : RecoveredRotationOrderedData graphData minimal targetBase =
      RecoveredRotationOrderedData graphData minimal sourceBase :=
    rotationOrderedData_eq_of_endpoints_eq graphData targetBase sourceBase
      minimal.spherical.cubic minimal.vertexRotationCyclic
      (htargetFirst.trans hsourceFirst.symm)
      (htargetSecond.trans hsourceSecond.symm)
  exact ⟨targetBase, targetNormal, htargetOutcome, htargetEscape, haligned⟩

/-- A recursive all-face step retaining the exact source fusion normal and
its pumping launch, in addition to the target Kempe package and the
singleton-triangle or recovery geometry. -/
def RotationOrderedFusionNormalIntrinsicShortOrRecoveryDartReentry
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (source target : G.Dart) : Prop :=
  ∃ (baseData : AdjacentPairData G)
      (normal : RotationOrderedCyclicKempeFusionChainNormalForm graphData
        minimal baseData),
    normal.CertifiedRebasePumpingLaunch ∧
      ∃ targetEdge : G.edgeSet,
        centralDart
            (RecoveredRotationOrderedData graphData minimal
              baseData).centralAdjacent = source ∧
          centralEdge
              (RecoveredRotationOrderedData graphData minimal baseData) ≠
            targetEdge ∧
          targetEdge.1 = target.edge ∧
          HasRotationOrderedFusionKempeOrbitEscape
            graphData minimal target.fst target.snd ∧
          IntrinsicShortOrRecoveryGeometry graphData minimal baseData
            targetEdge

/-- A normal-retaining recursive step changes the directed ambient edge. -/
theorem RotationOrderedFusionNormalIntrinsicShortOrRecoveryDartReentry.ne
    {source target : G.Dart}
    (reentry : RotationOrderedFusionNormalIntrinsicShortOrRecoveryDartReentry
      graphData minimal source target) :
    source ≠ target := by
  rcases reentry with
    ⟨_baseData, _normal, _hlaunch, targetEdge, hsource, hne, hedge,
      _hkempe, _hgeometry⟩
  intro heq
  apply hne
  apply Subtype.ext
  have hdartEdge := congrArg SimpleGraph.Dart.edge (hsource.trans heq)
  exact hdartEdge.trans hedge.symm

/-- At every dart, the all-face alternative can retain the exact source
normal and its certified pumping launch through either recursive geometry.
The other two outcomes are the existing structural target and large exact
remote separator. -/
theorem rotationOrderedFusionStructuralTarget_or_largeRemotePrimalCut_or_exists_normalIntrinsicShortOrRecoveryDartReentry
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (source : G.Dart) :
    RotationOrderedFusionStructuralTargetAtDart graphData minimal source ∨
      RotationOrderedFusionLargeRemotePrimalCutAtDart graphData minimal
        source ∨
      ∃ target : G.Dart,
        RotationOrderedFusionNormalIntrinsicShortOrRecoveryDartReentry
          graphData minimal source target := by
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
  rcases normal.terminalFusion_or_certifiedRebasePumpingLaunch with
    hterminal | hlaunch
  · exact Or.inl ⟨baseData, normal, hcentral, Or.inl hterminal⟩
  · rcases
        hlaunch.exists_reachable_certifiedStopping_or_endpointPortPairingReductionObstruction_or_crossFaceAdjacentPairReentry
      with hstop | hloop
    · exact Or.inl ⟨baseData, normal, hcentral,
        Or.inr (Or.inl hstop)⟩
    · rcases hloop with hcell | ⟨targetEdge, htarget⟩
      · exact Or.inl ⟨baseData, normal, hcentral,
          Or.inr (Or.inr hcell)⟩
      · rcases htarget.geometry with hremote | hrecovery
        · rcases hremote with
            ⟨circuit, hminimal, cycle, _htargetCrossing⟩
          rcases cycle.exists_longPrimalCut_or_intrinsicShortFusionTarget with
            hlong | ⟨shortCycle, intrinsicEdge, hintrinsic⟩
          · exact Or.inr (Or.inl
              ⟨baseData, circuit, cycle, hcentral, hminimal, hlong⟩)
          · have hintrinsic' := hintrinsic
            rcases hintrinsic with
              ⟨first, second, _hne, hadj, hvalue, hintrinsicNe,
                _hboundary, hkempe, _hshortGeometry⟩
            let intrinsicTarget : G.Dart := centralDart hadj
            have hedgeIntrinsic :
                intrinsicEdge.1 = intrinsicTarget.edge := hvalue
            exact Or.inr (Or.inr
              ⟨intrinsicTarget, baseData, normal, hlaunch, intrinsicEdge,
                hcentral, hintrinsicNe, hedgeIntrinsic, hkempe,
                Or.inl
                  ⟨circuit, hminimal, shortCycle, hintrinsic'⟩⟩)
        · rcases htarget.target_fusion with
            ⟨first, second, _hne, hadj, htargetValue, htargetFusion⟩
          let target : G.Dart := centralDart hadj
          have hedge : targetEdge.1 = target.edge := htargetValue
          have hfusion :
              HasRotationOrderedFusionTerminalOrRebasePumping
                graphData minimal target.fst target.snd := by
            simpa [target, centralDart] using htargetFusion
          have hkempe : HasRotationOrderedFusionKempeOrbitEscape graphData
              minimal target.fst target.snd :=
            hasRotationOrderedFusionKempeOrbitEscape_of_terminalOrRebasePumping
              graphData minimal hfusion
          exact Or.inr (Or.inr
            ⟨target, baseData, normal, hlaunch, targetEdge, hcentral,
              htarget.target_ne_central, hedge, hkempe,
              Or.inr hrecovery⟩)

/-- Finite iteration of normal-retaining reentry reaches a structural
target, reaches a large exact separator, or contains a nonempty closed
normal-retaining orbit. -/
theorem exists_reachable_rotationOrderedFusionStructuralTarget_or_largeRemotePrimalCut_or_normalIntrinsicShortOrRecoveryDartReentryCycle
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (start : G.Dart) :
    (∃ finish : G.Dart,
        Relation.ReflTransGen
            (RotationOrderedFusionNormalIntrinsicShortOrRecoveryDartReentry
              graphData minimal) start finish ∧
          RotationOrderedFusionStructuralTargetAtDart graphData minimal
            finish) ∨
      (∃ finish : G.Dart,
        Relation.ReflTransGen
            (RotationOrderedFusionNormalIntrinsicShortOrRecoveryDartReentry
              graphData minimal) start finish ∧
          RotationOrderedFusionLargeRemotePrimalCutAtDart graphData minimal
            finish) ∨
      ∃ cycleDart : G.Dart,
        Relation.ReflTransGen
            (RotationOrderedFusionNormalIntrinsicShortOrRecoveryDartReentry
              graphData minimal) start cycleDart ∧
          Relation.TransGen
            (RotationOrderedFusionNormalIntrinsicShortOrRecoveryDartReentry
              graphData minimal) cycleDart cycleDart := by
  let transition :=
    RotationOrderedFusionNormalIntrinsicShortOrRecoveryDartReentry
      graphData minimal
  let terminal := fun dart : G.Dart =>
    RotationOrderedFusionStructuralTargetAtDart graphData minimal dart ∨
      RotationOrderedFusionLargeRemotePrimalCutAtDart graphData minimal dart
  have hterminalOrStep : ∀ dart : G.Dart,
      terminal dart ∨ ∃ target, transition dart target := by
    intro dart
    rcases
        rotationOrderedFusionStructuralTarget_or_largeRemotePrimalCut_or_exists_normalIntrinsicShortOrRecoveryDartReentry
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

/-- At a composable reentry join, the target Kempe package of the first
step and the retained source normal of the second step normalize to the
same rotation-ordered adjacent-pair datum. -/
theorem RotationOrderedFusionNormalIntrinsicShortOrRecoveryDartReentry.exists_shared_normal_alignment
    {source middle target : G.Dart}
    (firstStep :
      RotationOrderedFusionNormalIntrinsicShortOrRecoveryDartReentry
        graphData minimal source middle)
    (nextStep :
      RotationOrderedFusionNormalIntrinsicShortOrRecoveryDartReentry
        graphData minimal middle target) :
    ∃ (targetBase : AdjacentPairData G)
        (targetNormal : RotationOrderedCyclicKempeFusionChainNormalForm
          graphData minimal targetBase)
        (nextBase : AdjacentPairData G)
        (nextNormal : RotationOrderedCyclicKempeFusionChainNormalForm
          graphData minimal nextBase),
      (targetNormal.TerminalFusionOutcome ∨
          targetNormal.CertifiedRebasePumpingLaunch) ∧
        Nonempty targetNormal.KempeOrbitAdjacentEscape ∧
        nextNormal.CertifiedRebasePumpingLaunch ∧
        RecoveredRotationOrderedData graphData minimal targetBase =
          RecoveredRotationOrderedData graphData minimal nextBase := by
  rcases firstStep with
    ⟨_firstBase, _firstNormal, _hfirstLaunch, _firstEdge, _hfirstSource,
      _hfirstNe, _hfirstEdge, htargetKempe, _hfirstGeometry⟩
  rcases nextStep with
    ⟨nextBase, nextNormal, hnextLaunch, _nextEdge, hnextSource,
      _hnextNe, _hnextEdge, _hnextKempe, _hnextGeometry⟩
  rcases
      HasRotationOrderedFusionKempeOrbitEscape.exists_normal_aligned_with_sourceBase
        (graphData := graphData) (minimal := minimal) htargetKempe hnextSource with
    ⟨targetBase, targetNormal, htargetOutcome, htargetEscape, haligned⟩
  exact ⟨targetBase, targetNormal, nextBase, nextNormal, htargetOutcome,
    htargetEscape, hnextLaunch, haligned⟩

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
