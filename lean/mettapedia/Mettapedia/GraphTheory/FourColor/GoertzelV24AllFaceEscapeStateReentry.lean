import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicShortEscapeCollar

/-! Finite all-face reentry states retaining the actual Kempe escape
coloring, so that equality at recursive joins carries Kempe-orbit data rather
than only the underlying rotation-ordered ports. -/

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

/-- The finite raw data underlying an adjacent-pair presentation. -/
private def adjacentPairDataRaw (data : AdjacentPairData G) :
    V × V × (Fin 4 → V) :=
  (data.firstVertex, data.secondVertex, data.portVertex)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The endpoints and four ordered ports determine an adjacent-pair datum;
all remaining fields are propositions. -/
private theorem adjacentPairDataRaw_injective :
    Function.Injective (adjacentPairDataRaw (G := G)) := by
  intro first second heq
  have hfirst : first.firstVertex = second.firstVertex :=
    congrArg (fun data => data.1) heq
  have hsecond : first.secondVertex = second.secondVertex :=
    congrArg (fun data => data.2.1) heq
  have hports : first.portVertex = second.portVertex :=
    congrArg (fun data => data.2.2) heq
  cases first
  cases second
  simp only at hfirst hsecond hports
  subst hfirst
  subst hsecond
  subst hports
  rfl

/-- A finite state records an exact adjacent-pair presentation together with
an actual coloring of its deleted-pair graph. -/
abbrev RotationOrderedFusionEscapeColorState
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData) :=
  Σ baseData : AdjacentPairData G,
    (DeletedAdjacentPairGraph G
      (RecoveredRotationOrderedData graphData minimal baseData).firstVertex
      (RecoveredRotationOrderedData graphData minimal baseData).secondVertex).EdgeColoring
        Color

noncomputable instance rotationOrderedFusionEscapeColorStateFinite :
    Finite (RotationOrderedFusionEscapeColorState graphData minimal) := by
  letI : Finite (AdjacentPairData G) :=
    Finite.of_injective (adjacentPairDataRaw (G := G))
      adjacentPairDataRaw_injective
  infer_instance

namespace RotationOrderedFusionEscapeColorState

/-- The directed ambient edge represented by an escape-color state. -/
def dart (state : RotationOrderedFusionEscapeColorState graphData minimal) :
    G.Dart :=
  centralDart
    (RecoveredRotationOrderedData graphData minimal
      state.1).centralAdjacent

/-- A state is genuine when its coloring is the certified adjacent Kempe
escape of a complete normal form on its exact adjacent-pair datum. -/
def Admissible
    (state : RotationOrderedFusionEscapeColorState graphData minimal) : Prop :=
  ∃ normal : RotationOrderedCyclicKempeFusionChainNormalForm graphData
      minimal state.1,
    (normal.TerminalFusionOutcome ∨
        normal.CertifiedRebasePumpingLaunch) ∧
      ∃ escape : normal.KempeOrbitAdjacentEscape,
        state.2 = escape.coloring

/-- The finite carrier of genuine escape-color states. -/
abbrev AdmissibleState :=
  {state : RotationOrderedFusionEscapeColorState graphData minimal //
    state.Admissible}

noncomputable instance admissibleStateFinite :
    Finite (AdmissibleState (graphData := graphData) (minimal := minimal)) :=
  inferInstance

/-- Remembering the actual escape coloring makes independently selected
normal forms on one state Kempe-compatible: their all-equal recolorings have
exactly the same Kempe closure. -/
theorem kempeClosure_recoloring_eq_of_escapeColoring_eq
    {state : RotationOrderedFusionEscapeColorState graphData minimal}
    {firstNormal secondNormal :
      RotationOrderedCyclicKempeFusionChainNormalForm graphData minimal
        state.1}
    (firstEscape : firstNormal.KempeOrbitAdjacentEscape)
    (secondEscape : secondNormal.KempeOrbitAdjacentEscape)
    (hfirst : state.2 = firstEscape.coloring)
    (hsecond : state.2 = secondEscape.coloring) :
    (DeletedAdjacentPairGraph G
        (RecoveredRotationOrderedData graphData minimal state.1).firstVertex
        (RecoveredRotationOrderedData graphData minimal state.1).secondVertex).EdgeKempeClosure
          firstNormal.recoloring =
      (DeletedAdjacentPairGraph G
        (RecoveredRotationOrderedData graphData minimal state.1).firstVertex
        (RecoveredRotationOrderedData graphData minimal state.1).secondVertex).EdgeKempeClosure
          secondNormal.recoloring := by
  calc
    _ = (DeletedAdjacentPairGraph G
          (RecoveredRotationOrderedData graphData minimal state.1).firstVertex
          (RecoveredRotationOrderedData graphData minimal state.1).secondVertex).EdgeKempeClosure
            firstEscape.coloring :=
      firstEscape.same_kempeClosure_as_allEqual
    _ = (DeletedAdjacentPairGraph G
          (RecoveredRotationOrderedData graphData minimal state.1).firstVertex
          (RecoveredRotationOrderedData graphData minimal state.1).secondVertex).EdgeKempeClosure
            state.2 := by rw [hfirst]
    _ = (DeletedAdjacentPairGraph G
          (RecoveredRotationOrderedData graphData minimal state.1).firstVertex
          (RecoveredRotationOrderedData graphData minimal state.1).secondVertex).EdgeKempeClosure
            secondEscape.coloring := by rw [hsecond]
    _ = _ := secondEscape.same_kempeClosure_as_allEqual.symm

/-- Recursive geometry aligned with the literal target escape-color state.
In the intrinsic branch the retained singleton collar's target escape is
definitionally the coloring stored by the next state. -/
def EscapeAlignedGeometry
    (source target : RotationOrderedFusionEscapeColorState graphData minimal)
    (targetEdge : G.edgeSet) : Prop :=
  (∃ circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal
        source.1,
      circuit.IsLengthMinimal ∧
        ∃ cycle :
            CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
              circuit,
          cycle.IntrinsicShortFusionTarget targetEdge ∧
            ∃ collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge,
              target = ⟨collar.targetBase,
                collar.targetEscape.coloring⟩) ∨
    ∃ circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal
        source.1,
      circuit.IsLengthMinimal ∧
        ∃ rotated : CrossCentralExactFaceCertifiedRebaseCircuit graphData
            minimal source.1,
          rotated.arcLength = circuit.arcLength ∧
            ∃ transfer : ClosureRecoveryFaceTransfer rotated,
              targetEdge = transfer.recovery.edge

/-- Forgetting the exact target escape recovers the underlying geometric
intrinsic-short/recovery alternative. -/
theorem EscapeAlignedGeometry.toIntrinsicShortOrRecoveryGeometry
    {source target :
      RotationOrderedFusionEscapeColorState graphData minimal}
    {targetEdge : G.edgeSet}
    (geometry : source.EscapeAlignedGeometry target targetEdge) :
    IntrinsicShortOrRecoveryGeometry graphData minimal source.1 targetEdge := by
  rcases geometry with
    ⟨circuit, hminimal, cycle, intrinsic, _collar, _htarget⟩ |
      ⟨circuit, hminimal, rotated, hlength, transfer, htarget⟩
  · exact Or.inl ⟨circuit, hminimal, cycle, intrinsic⟩
  · exact Or.inr ⟨circuit, hminimal, rotated, hlength, transfer, htarget⟩

/-- A recursive step whose source and target both retain their actual Kempe
escape coloring.  The target is tied to the geometric successor edge by an
equality of ambient edge-set elements, not merely by endpoint names. -/
def Reentry
    (source target : RotationOrderedFusionEscapeColorState graphData minimal) :
    Prop :=
  ∃ sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm graphData
      minimal source.1,
    sourceNormal.CertifiedRebasePumpingLaunch ∧
      ∃ sourceEscape : sourceNormal.KempeOrbitAdjacentEscape,
        source.2 = sourceEscape.coloring ∧
          ∃ targetEdge : G.edgeSet,
            centralEdge
                (RecoveredRotationOrderedData graphData minimal source.1) ≠
              targetEdge ∧
              centralEdge
                  (RecoveredRotationOrderedData graphData minimal target.1) =
                targetEdge ∧
                source.EscapeAlignedGeometry target targetEdge ∧
                ∃ targetNormal :
                    RotationOrderedCyclicKempeFusionChainNormalForm graphData
                      minimal target.1,
                  (targetNormal.TerminalFusionOutcome ∨
                      targetNormal.CertifiedRebasePumpingLaunch) ∧
                    ∃ targetEscape : targetNormal.KempeOrbitAdjacentEscape,
                      target.2 = targetEscape.coloring

/-- Consecutive escape-color reentries have an honest same-base Kempe join:
the target normal selected by the first step and the source normal selected by
the next step have equal all-equal Kempe closures. -/
theorem Reentry.exists_join_kempeClosure_eq
    {source middle target :
      RotationOrderedFusionEscapeColorState graphData minimal}
    (firstStep : source.Reentry middle)
    (nextStep : middle.Reentry target) :
    ∃ (firstTargetNormal nextSourceNormal :
        RotationOrderedCyclicKempeFusionChainNormalForm graphData minimal
          middle.1),
      (DeletedAdjacentPairGraph G
          (RecoveredRotationOrderedData graphData minimal middle.1).firstVertex
          (RecoveredRotationOrderedData graphData minimal middle.1).secondVertex).EdgeKempeClosure
            firstTargetNormal.recoloring =
        (DeletedAdjacentPairGraph G
          (RecoveredRotationOrderedData graphData minimal middle.1).firstVertex
          (RecoveredRotationOrderedData graphData minimal middle.1).secondVertex).EdgeKempeClosure
            nextSourceNormal.recoloring := by
  rcases firstStep with
    ⟨_firstSourceNormal, _hfirstLaunch, _firstSourceEscape,
      _hfirstSourceColor, _firstTargetEdge, _hfirstNe, _hfirstTargetEdge,
      _hfirstGeometry, firstTargetNormal, _hfirstTargetOutcome,
      firstTargetEscape, hfirstTargetColor⟩
  rcases nextStep with
    ⟨nextSourceNormal, _hnextLaunch, nextSourceEscape,
      hnextSourceColor, _nextTargetEdge, _hnextNe, _hnextTargetEdge,
      _hnextGeometry, _nextTargetNormal, _hnextTargetOutcome,
      _nextTargetEscape, _hnextTargetColor⟩
  exact ⟨firstTargetNormal, nextSourceNormal,
    kempeClosure_recoloring_eq_of_escapeColoring_eq firstTargetEscape
      nextSourceEscape hfirstTargetColor hnextSourceColor⟩

/-- Every escape-color reentry changes the represented directed ambient
edge. -/
theorem Reentry.dart_ne
    {source target :
      RotationOrderedFusionEscapeColorState graphData minimal}
    (step : source.Reentry target) :
    source.dart ≠ target.dart := by
  rcases step with
    ⟨_sourceNormal, _hlaunch, _sourceEscape, _hsourceColor, targetEdge,
      hne, htarget, _hgeometry, _targetNormal, _htargetOutcome,
      _targetEscape, _htargetColor⟩
  intro hdart
  apply hne
  apply Subtype.ext
  calc
    (centralEdge
        (RecoveredRotationOrderedData graphData minimal source.1)).1 =
        source.dart.edge := by
      rfl
    _ = target.dart.edge := congrArg SimpleGraph.Dart.edge hdart
    _ = (centralEdge
        (RecoveredRotationOrderedData graphData minimal target.1)).1 := by
      rfl
    _ = targetEdge.1 := congrArg Subtype.val htarget

/-- The recursive relation lifted to the finite subtype of genuine escape
states. -/
def AdmissibleReentry
    (source target :
      AdmissibleState (graphData := graphData) (minimal := minimal)) : Prop :=
  source.1.Reentry target.1

/-- The two all-face stopping alternatives on a genuine escape state. -/
def AdmissibleTerminal
    (state :
      AdmissibleState (graphData := graphData) (minimal := minimal)) : Prop :=
  RotationOrderedFusionStructuralTargetAtDart graphData minimal
      state.1.dart ∨
    RotationOrderedFusionLargeRemotePrimalCutAtDart graphData minimal
      state.1.dart

/-- Every genuine escape state either realizes a structural target, realizes
a large exact remote separator, or takes a successor step retaining the
actual source and target escape colorings. -/
theorem admissibleTerminal_or_exists_admissibleReentry
    (state :
      AdmissibleState (graphData := graphData) (minimal := minimal)) :
    AdmissibleTerminal state ∨
      ∃ target :
          AdmissibleState (graphData := graphData) (minimal := minimal),
        AdmissibleReentry state target := by
  rcases state.2 with
    ⟨sourceNormal, hsourceOutcome, sourceEscape, hsourceColor⟩
  rcases hsourceOutcome with hterminal | hlaunch
  · exact Or.inl (Or.inl
      ⟨state.1.1, sourceNormal, rfl, Or.inl hterminal⟩)
  · rcases
        hlaunch.exists_reachable_certifiedStopping_or_endpointPortPairingReductionObstruction_or_crossFaceAdjacentPairReentry
      with hstop | hloop
    · exact Or.inl (Or.inl
        ⟨state.1.1, sourceNormal, rfl,
          Or.inr (Or.inl hstop)⟩)
    · rcases hloop with hcell | ⟨targetEdge, htarget⟩
      · exact Or.inl (Or.inl
          ⟨state.1.1, sourceNormal, rfl,
            Or.inr (Or.inr hcell)⟩)
      · rcases htarget.geometry with hremote | hrecovery
        · rcases hremote with
            ⟨circuit, hminimal, cycle, _htargetCrossing⟩
          rcases cycle.exists_longPrimalCut_or_intrinsicShortFusionTarget with
            hlong | ⟨shortCycle, intrinsicEdge, hintrinsic⟩
          · exact Or.inl (Or.inr
              ⟨state.1.1, circuit, cycle, rfl, hminimal, hlong⟩)
          · have hintrinsic' := hintrinsic
            rcases hintrinsic with
              ⟨_first, _second, _hne, _hadj, _hvalue, hintrinsicNe,
                _hboundary, _hkempe, _hshortGeometry⟩
            rcases hintrinsic'.nonempty_targetEscapeCollar with
              ⟨targetCollar⟩
            let targetRaw :
                RotationOrderedFusionEscapeColorState graphData minimal :=
              ⟨targetCollar.targetBase,
                targetCollar.targetEscape.coloring⟩
            have htargetAdmissible : targetRaw.Admissible := by
              exact ⟨targetCollar.targetNormal,
                targetCollar.targetOutcome, targetCollar.targetEscape, rfl⟩
            let target :
                AdmissibleState (graphData := graphData)
                  (minimal := minimal) :=
              ⟨targetRaw, htargetAdmissible⟩
            exact Or.inr ⟨target, sourceNormal, hlaunch, sourceEscape,
              hsourceColor, intrinsicEdge, hintrinsicNe,
              targetCollar.targetCentral_eq,
              Or.inl ⟨circuit, hminimal, shortCycle, hintrinsic',
                targetCollar, rfl⟩,
              targetCollar.targetNormal, targetCollar.targetOutcome,
              targetCollar.targetEscape, rfl⟩
        · rcases htarget.target_fusion with
            ⟨first, second, _hne, hadj, htargetValue, htargetFusion⟩
          let targetDart : G.Dart := centralDart hadj
          have hfusion :
              HasRotationOrderedFusionTerminalOrRebasePumping
                graphData minimal targetDart.fst targetDart.snd := by
            simpa [targetDart, centralDart] using htargetFusion
          have hkempe : HasRotationOrderedFusionKempeOrbitEscape graphData
              minimal targetDart.fst targetDart.snd :=
            hasRotationOrderedFusionKempeOrbitEscape_of_terminalOrRebasePumping
              graphData minimal hfusion
          rcases hkempe with
            ⟨targetBase, htargetFirst, htargetSecond, targetNormal,
              htargetOutcome, ⟨targetEscape⟩⟩
          let targetRaw :
              RotationOrderedFusionEscapeColorState graphData minimal :=
            ⟨targetBase, targetEscape.coloring⟩
          have htargetAdmissible : targetRaw.Admissible := by
            exact ⟨targetNormal, htargetOutcome, targetEscape, rfl⟩
          let target :
              AdmissibleState (graphData := graphData) (minimal := minimal) :=
            ⟨targetRaw, htargetAdmissible⟩
          have htargetCentral :
              centralEdge
                  (RecoveredRotationOrderedData graphData minimal
                    targetBase) = targetEdge := by
            apply Subtype.ext
            rw [centralEdge_val, centralEdgeValue]
            change s(targetBase.firstVertex, targetBase.secondVertex) =
              targetEdge.1
            rw [htargetFirst, htargetSecond]
            simpa [targetDart, centralDart] using htargetValue.symm
          exact Or.inr ⟨target, sourceNormal, hlaunch, sourceEscape,
            hsourceColor, targetEdge, htarget.target_ne_central,
            htargetCentral, Or.inr hrecovery, targetNormal,
            htargetOutcome, targetEscape, rfl⟩

/-- Lifted reentries have no self-loop. -/
theorem AdmissibleReentry.ne
    {source target :
      AdmissibleState (graphData := graphData) (minimal := minimal)}
    (step : AdmissibleReentry source target) :
    source ≠ target := by
  intro heq
  exact step.dart_ne (congrArg (fun state => state.1.dart) heq)

/-- The same-base Kempe-closure equality is available at every composable
join of lifted finite-state transitions. -/
theorem AdmissibleReentry.exists_join_kempeClosure_eq
    {source middle target :
      AdmissibleState (graphData := graphData) (minimal := minimal)}
    (firstStep : AdmissibleReentry source middle)
    (nextStep : AdmissibleReentry middle target) :
    ∃ (firstTargetNormal nextSourceNormal :
        RotationOrderedCyclicKempeFusionChainNormalForm graphData minimal
          middle.1.1),
      (DeletedAdjacentPairGraph G
          (RecoveredRotationOrderedData graphData minimal
            middle.1.1).firstVertex
          (RecoveredRotationOrderedData graphData minimal
            middle.1.1).secondVertex).EdgeKempeClosure
            firstTargetNormal.recoloring =
        (DeletedAdjacentPairGraph G
          (RecoveredRotationOrderedData graphData minimal
            middle.1.1).firstVertex
          (RecoveredRotationOrderedData graphData minimal
            middle.1.1).secondVertex).EdgeKempeClosure
            nextSourceNormal.recoloring :=
  RotationOrderedFusionEscapeColorState.Reentry.exists_join_kempeClosure_eq
    firstStep nextStep

/-- Finite iteration on actual escape-color states reaches one of the two
all-face stopping alternatives or produces a reachable nonempty closed
escape-color orbit. -/
theorem exists_reachable_admissibleTerminal_or_admissibleReentryCycle
    (start :
      AdmissibleState (graphData := graphData) (minimal := minimal)) :
    (∃ finish,
        Relation.ReflTransGen
            (AdmissibleReentry (graphData := graphData) (minimal := minimal))
            start finish ∧
          AdmissibleTerminal finish) ∨
      ∃ cycleState,
        Relation.ReflTransGen
            (AdmissibleReentry (graphData := graphData) (minimal := minimal))
            start cycleState ∧
          Relation.TransGen
            (AdmissibleReentry (graphData := graphData) (minimal := minimal))
            cycleState cycleState := by
  exact finite_reflTransGen_terminal_or_transGen_cycle
    (AdmissibleReentry (graphData := graphData) (minimal := minimal))
    (AdmissibleTerminal (graphData := graphData) (minimal := minimal))
    admissibleTerminal_or_exists_admissibleReentry start

/-- Every directed ambient edge has a genuine finite state whose datum has
that exact central orientation and whose coloring is an actual Kempe escape. -/
theorem exists_admissibleState_with_dart
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (start : G.Dart) :
    ∃ state :
        AdmissibleState (graphData := graphData) (minimal := minimal),
      state.1.dart = start := by
  rcases
      exists_rotationOrderedCyclicKempeFusionChainNormalForm_of_vertexMinimalTaitCounterexample
        graphData minimal start.2 with
    ⟨baseData, hfirst, hsecond, ⟨normal⟩⟩
  rcases normal.nonempty_kempeOrbitAdjacentEscape with ⟨escape⟩
  let raw : RotationOrderedFusionEscapeColorState graphData minimal :=
    ⟨baseData, escape.coloring⟩
  have hadmissible : raw.Admissible := by
    exact ⟨normal, normal.terminalFusion_or_certifiedRebasePumpingLaunch,
      escape, rfl⟩
  refine ⟨⟨raw, hadmissible⟩, ?_⟩
  apply SimpleGraph.Dart.ext
  exact Prod.ext hfirst hsecond

/-- Starting at any directed edge, the color-retaining all-face machine
reaches a structural target, reaches a large exact remote separator, or
contains a nonempty closed orbit of genuine escape-color states. -/
theorem exists_escapeState_reachable_structural_or_largeRemotePrimalCut_or_reentryCycle
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (start : G.Dart) :
    ∃ initial :
        AdmissibleState (graphData := graphData) (minimal := minimal),
      initial.1.dart = start ∧
        ((∃ finish,
            Relation.ReflTransGen
                (AdmissibleReentry (graphData := graphData)
                  (minimal := minimal)) initial finish ∧
              RotationOrderedFusionStructuralTargetAtDart graphData minimal
                finish.1.dart) ∨
          (∃ finish,
            Relation.ReflTransGen
                (AdmissibleReentry (graphData := graphData)
                  (minimal := minimal)) initial finish ∧
              RotationOrderedFusionLargeRemotePrimalCutAtDart graphData
                minimal finish.1.dart) ∨
          ∃ cycleState,
            Relation.ReflTransGen
                (AdmissibleReentry (graphData := graphData)
                  (minimal := minimal)) initial cycleState ∧
              Relation.TransGen
                (AdmissibleReentry (graphData := graphData)
                  (minimal := minimal)) cycleState cycleState) := by
  rcases exists_admissibleState_with_dart graphData minimal start with
    ⟨initial, hinitial⟩
  refine ⟨initial, hinitial, ?_⟩
  rcases exists_reachable_admissibleTerminal_or_admissibleReentryCycle initial
      with hfinish | hcycle
  · rcases hfinish with ⟨finish, hreach, hstructural | hlarge⟩
    · exact Or.inl ⟨finish, hreach, hstructural⟩
    · exact Or.inr (Or.inl ⟨finish, hreach, hlarge⟩)
  · exact Or.inr (Or.inr hcycle)

end RotationOrderedFusionEscapeColorState

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
