import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionChargedKempeAction
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionLens

/-! Canonical same-base reentry after a charged-terminal Kempe action. -/

namespace Mettapedia.GraphTheory.FourColor

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open GoertzelV24CorridorPumping
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24FourDefectBoundary
open GoertzelV24FourEdgeCutKempeEscape
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- In an uncolorable cubic ambient graph, every Tait coloring of an
adjacent-pair deletion lies either in the all-equal boundary sector or in
the canonical `01|23` adjacent sector. -/
theorem boundaryWord_allEqual_or_adjacent01_23_of_not_taitColorable
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C) :
    SquareBoundaryWord.AllEqual
        (data.degreeTwoBoundaryData.colorWord C) ∨
      SquareBoundaryWord.Adjacent01_23
        (data.degreeTwoBoundaryData.colorWord C) := by
  have hsame :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.sameSidePairs_of_not_taitColorable
      data hcubic hnotColorable C hC
  by_cases hsides : data.degreeTwoBoundaryData.colorWord C 0 =
      data.degreeTwoBoundaryData.colorWord C 2
  · exact Or.inl
      ⟨hsame.1, hsame.1.symm.trans hsides, hsame.2⟩
  · exact Or.inr ⟨hsame.1, hsame.2, hsides⟩

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

namespace GoertzelV24RecoveredAdjacentPairFusionChainNormalForm

namespace RotationOrderedCyclicKempeFusionChainNormalForm

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- An all-equal coloring reached in the normal form's Kempe orbit,
together with the two actual even fusion lenses carried by that coloring. -/
structure AllEqualFusionSuccessor
    (normal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData) where
  coloring : (DeletedAdjacentPairGraph G
    (RecoveredRotationOrderedData graphData minimal baseData).firstVertex
    (RecoveredRotationOrderedData graphData minimal baseData).secondVertex
      ).EdgeColoring Color
  isTait : IsTaitEdgeColoring
    (DeletedAdjacentPairGraph G
      (RecoveredRotationOrderedData graphData minimal baseData).firstVertex
      (RecoveredRotationOrderedData graphData minimal baseData).secondVertex)
    coloring
  boundary_allEqual : SquareBoundaryWord.AllEqual
    ((RecoveredRotationOrderedData graphData minimal baseData
      ).degreeTwoBoundaryData.colorWord coloring)
  reachable_from_allEqual : coloring ∈
    (DeletedAdjacentPairGraph G
      (RecoveredRotationOrderedData graphData minimal baseData).firstVertex
      (RecoveredRotationOrderedData graphData minimal baseData).secondVertex
      ).EdgeKempeClosure normal.recoloring
  reachable_from_profile : coloring ∈
    (DeletedAdjacentPairGraph G
      (RecoveredRotationOrderedData graphData minimal baseData).firstVertex
      (RecoveredRotationOrderedData graphData minimal baseData).secondVertex
      ).EdgeKempeClosure normal.profile.coloring
  constant : Color
  other : Color
  validPair : ValidColorPair constant other
  boundary_constant : ∀ port : Fin 4,
    (RecoveredRotationOrderedData graphData minimal baseData
      ).degreeTwoBoundaryData.colorWord coloring port = constant
  lens01 : Nonempty
    ((RecoveredRotationOrderedData graphData minimal baseData
      ).degreeTwoBoundaryData.EvenKempeFusionLens
        coloring constant other (constant + other) 0 1)
  lens23 : Nonempty
    ((RecoveredRotationOrderedData graphData minimal baseData
      ).degreeTwoBoundaryData.EvenKempeFusionLens
        coloring constant other (constant + other) 2 3)

/-- The canonical outcomes of a same-base Kempe step from an adjacent
escape: either an all-equal state carrying both fusion lenses, or another
adjacent escape in the same normal-form orbit. -/
inductive SameBaseKempeReentry
    (normal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData)
    (escape : normal.KempeOrbitAdjacentEscape) : Prop
  | allEqual (successor : normal.AllEqualFusionSuccessor)
      (oneStep : (DeletedAdjacentPairGraph G
        (RecoveredRotationOrderedData graphData minimal baseData).firstVertex
        (RecoveredRotationOrderedData graphData minimal baseData).secondVertex
        ).EdgeKempeStep escape.coloring successor.coloring)
  | adjacent (successor : normal.KempeOrbitAdjacentEscape)
      (oneStep : (DeletedAdjacentPairGraph G
        (RecoveredRotationOrderedData graphData minimal baseData).firstVertex
        (RecoveredRotationOrderedData graphData minimal baseData).secondVertex
        ).EdgeKempeStep escape.coloring successor.coloring)

/-- Every actual Tait-preserving component switch from an adjacent escape
re-enters one of the two canonical sectors, retaining all reachability and
fusion data. -/
theorem KempeOrbitAdjacentEscape.sameBaseKempeReentry_of_step
    {normal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (escape : normal.KempeOrbitAdjacentEscape)
    (successorColoring : (DeletedAdjacentPairGraph G
      (RecoveredRotationOrderedData graphData minimal baseData).firstVertex
      (RecoveredRotationOrderedData graphData minimal baseData).secondVertex
      ).EdgeColoring Color)
    (hTait : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G
        (RecoveredRotationOrderedData graphData minimal baseData).firstVertex
        (RecoveredRotationOrderedData graphData minimal baseData).secondVertex)
      successorColoring)
    (hstep : (DeletedAdjacentPairGraph G
      (RecoveredRotationOrderedData graphData minimal baseData).firstVertex
      (RecoveredRotationOrderedData graphData minimal baseData).secondVertex
      ).EdgeKempeStep escape.coloring successorColoring) :
    normal.SameBaseKempeReentry escape := by
  let data := RecoveredRotationOrderedData graphData minimal baseData
  let deleted := DeletedAdjacentPairGraph G data.firstVertex data.secondVertex
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring :=
    graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
      graphData minimal
  have hreachable : successorColoring ∈
      deleted.EdgeKempeClosure escape.coloring :=
    deleted.mem_edgeKempeClosure_of_step
      (deleted.mem_edgeKempeClosure_self escape.coloring) hstep
  have hfromAllEqual : successorColoring ∈
      deleted.EdgeKempeClosure normal.recoloring :=
    deleted.edgeKempeClosure_subset_of_mem
      escape.reachable_from_allEqual hreachable
  have hfromProfile : successorColoring ∈
      deleted.EdgeKempeClosure normal.profile.coloring :=
    deleted.edgeKempeClosure_subset_of_mem
      escape.reachable_from_profile hreachable
  rcases GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryWord_allEqual_or_adjacent01_23_of_not_taitColorable
      data hcubic hnotColorable successorColoring hTait with
    hallEqual | hadjacent
  · let constant := data.degreeTwoBoundaryData.colorWord successorColoring 0
    have hwell := data.degreeTwoBoundaryData_wellFormed hcubic
    have hconstantNonzero : constant ≠ 0 :=
      data.degreeTwoBoundaryData.colorWord_ne_zero
        hwell successorColoring 0
    have hconstant : ∀ port : Fin 4,
        data.degreeTwoBoundaryData.colorWord successorColoring port =
          constant := by
      intro port
      fin_cases port
      · rfl
      · exact hallEqual.1.symm
      · exact (hallEqual.1.trans hallEqual.2.1).symm
      · exact (hallEqual.1.trans hallEqual.2.1 |>.trans
          hallEqual.2.2).symm
    rcases exists_validColorPair_with_first_of_ne_zero hconstantNonzero with
      ⟨other, hpair⟩
    rcases data.exists_two_evenKempeFusionLenses_of_constant_colorWord
        hcubic hnotColorable successorColoring hTait hpair hconstant with
      ⟨hlens01, hlens23⟩
    exact SameBaseKempeReentry.allEqual {
      coloring := successorColoring
      isTait := hTait
      boundary_allEqual := hallEqual
      reachable_from_allEqual := hfromAllEqual
      reachable_from_profile := hfromProfile
      constant := constant
      other := other
      validPair := hpair
      boundary_constant := hconstant
      lens01 := hlens01
      lens23 := hlens23 } hstep
  · let successor : normal.KempeOrbitAdjacentEscape := {
      coloring := successorColoring
      isTait := hTait
      boundary_adjacent01_23 := hadjacent
      reachable_from_allEqual := hfromAllEqual
      same_kempeClosure_as_allEqual :=
        SimpleGraph.Coloring.kempeClosure_eq_of_mem hfromAllEqual
      reachable_from_profile := hfromProfile }
    exact SameBaseKempeReentry.adjacent successor hstep

end RotationOrderedCyclicKempeFusionChainNormalForm
end GoertzelV24RecoveredAdjacentPairFusionChainNormalForm

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

namespace CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

namespace IntrinsicShortTargetEscapeCollar

variable {cycle :
    CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle rebaseCircuit}
  {targetEdge : G.edgeSet}
  {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
    graphData minimal baseData}
  {collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge}
  {sourceEscape : sourceNormal.KempeOrbitAdjacentEscape}
  {coordinate : Bool}
  {representative : IntrinsicCollarTerminalRepresentative
    collar.intrinsicCollarPortOverlapProfile}

/-- A constructed charged-terminal action canonically re-enters the source
or target normal form: the unmatched-target case is target-based, while the
other two cases are source-based. -/
theorem ChargedTerminalKempeAction.sameBaseReentry
    (action : ChargedTerminalKempeAction collar sourceEscape coordinate
      representative) :
    sourceNormal.SameBaseKempeReentry sourceEscape ∨
      collar.targetNormal.SameBaseKempeReentry collar.targetEscape := by
  cases action with
  | unmatchedSource sourcePort noOverlap mismatch actionData =>
      rcases actionData with ⟨retarget⟩
      exact Or.inl
        (sourceEscape.sameBaseKempeReentry_of_step retarget.coloring
          (retarget.isTait sourceEscape.isTait) retarget.oneStep)
  | matchedStem sourcePort targetPort overlap stem incident mismatch actionData =>
      rcases actionData with ⟨retarget⟩
      exact Or.inl
        (sourceEscape.sameBaseKempeReentry_of_step retarget.coloring
          (retarget.isTait sourceEscape.isTait) retarget.oneStep)
  | unmatchedTarget targetPort noOverlap mismatch actionData =>
      rcases actionData with ⟨retarget⟩
      exact Or.inr
        (collar.targetEscape.sameBaseKempeReentry_of_step retarget.coloring
          (retarget.isTait collar.targetEscape.isTait) retarget.oneStep)

namespace FirstHitSingletonCompanionTransferPath

variable {firstHit : FirstHitSingletonCompanionTransferPath
  (collar := collar) (sourceEscape := sourceEscape)}

namespace TransverseCompanionChange

variable {change : firstHit.TransverseCompanionChange}

namespace ComplementarySupportCorner.ChargedSupportRoute

variable {corner : change.ComplementarySupportCorner}

/-- The charged-route branch now retains both its exact endpoint action and
the ensuing canonical same-base reentry, including fusion lenses in the
all-equal sector. -/
theorem finishKempeAction_and_sameBaseReentry
    (route : corner.ChargedSupportRoute) :
    ChargedTerminalKempeAction collar sourceEscape
        (!firstHit.transfer.coordinate) route.finishRepresentative ∧
      (sourceNormal.SameBaseKempeReentry sourceEscape ∨
        collar.targetNormal.SameBaseKempeReentry collar.targetEscape) := by
  let action := route.nonempty_finishKempeAction
  exact ⟨action, action.sameBaseReentry⟩

end ComplementarySupportCorner.ChargedSupportRoute

namespace ComplementarySupportCorner

variable {corner : change.ComplementarySupportCorner}

namespace ClosedSupportRoute

/-- Either closed-route constructor carries a genuine return of positive
period in the same four-state discrepancy transfer system. -/
theorem exists_positive_exactReturn
    (route : corner.ClosedSupportRoute) :
    ∃ period : Nat,
      ∃ state : ScalarDiscrepancyColorState
          (!firstHit.transfer.coordinate),
        0 < period ∧
          ExactRelationalTransfer ScalarDiscrepancyColorTransition
            period state state := by
  cases route with
  | direct strand =>
      exact ⟨strand.cycle.length,
        strand.stateWord.head strand.stateWord_ne_nil,
        lt_of_lt_of_le (by omega) strand.cycle_isCycle.three_le_length,
        strand.exactReturn⟩
  | continued strand continuation routeData =>
      exact ⟨routeData.supportCycle.length,
        routeData.stateWord.head routeData.stateWord_ne_nil,
        lt_of_lt_of_le (by omega)
          routeData.supportCycle_isCycle.three_le_length,
        routeData.exactReturn⟩

end ClosedSupportRoute

/-- Complete complementary-support resolution.  A transverse companion
change now yields either a constructed endpoint Kempe action followed by
canonical same-base reentry, or a positive-period exact monodromy return. -/
theorem canonicalKempeReentry_or_positiveExactReturn
    (corner : change.ComplementarySupportCorner) :
    (∃ route : corner.ChargedSupportRoute,
      ChargedTerminalKempeAction collar sourceEscape
          (!firstHit.transfer.coordinate) route.finishRepresentative ∧
        (sourceNormal.SameBaseKempeReentry sourceEscape ∨
          collar.targetNormal.SameBaseKempeReentry collar.targetEscape)) ∨
    ∃ period : Nat,
      ∃ state : ScalarDiscrepancyColorState
          (!firstHit.transfer.coordinate),
        0 < period ∧
          ExactRelationalTransfer ScalarDiscrepancyColorTransition
            period state state := by
  rcases corner.chargedSupportRoute_or_closedSupportRoute with
    hcharged | hclosed
  · rcases hcharged with ⟨route⟩
    exact Or.inl ⟨route, route.finishKempeAction_and_sameBaseReentry⟩
  · rcases hclosed with ⟨route⟩
    exact Or.inr route.exists_positive_exactReturn

end ComplementarySupportCorner
end TransverseCompanionChange
end FirstHitSingletonCompanionTransferPath
end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
