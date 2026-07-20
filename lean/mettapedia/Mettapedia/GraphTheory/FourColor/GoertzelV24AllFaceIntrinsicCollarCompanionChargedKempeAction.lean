import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionChargedTerminal
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedTrail

/-! Genuine same-base Kempe actions supplied by charged collar terminals. -/

namespace Mettapedia.GraphTheory.FourColor

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open GoertzelV24CorridorPumping
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24FourDefectBoundary
open GoertzelV24FramedTrail
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A Kempe component selected by the present color of one edge and a
distinct target color.  Switching it retargets that edge exactly. -/
structure EdgeKempeRetarget
    (C : G.EdgeColoring Color) (edge : G.edgeSet) (target : Color) where
  validPair : ValidColorPair (C edge) target
  component :
    (C.bicoloredSubgraph (C edge) target).ConnectedComponent
  edge_mem_component :
    edge ∈ C.kempeComponentSet (C edge) target component

namespace EdgeKempeRetarget

variable {C : G.EdgeColoring Color} {edge : G.edgeSet} {target : Color}

/-- The coloring after performing the selected component switch. -/
def coloring (retarget : EdgeKempeRetarget C edge target) :
    G.EdgeColoring Color :=
  C.swapOnKempeComponent (C edge) target retarget.component

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The selected component switch gives the requested edge color. -/
@[simp]
theorem coloring_apply_edge
    (retarget : EdgeKempeRetarget C edge target) :
    retarget.coloring edge = target := by
  rw [coloring, C.swapOnKempeComponent_apply_of_mem
    retarget.edge_mem_component]
  exact Equiv.swap_apply_left _ _

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Retargeting one edge by its selected component is one genuine Kempe
step. -/
theorem oneStep (retarget : EdgeKempeRetarget C edge target) :
    G.EdgeKempeStep C retarget.coloring := by
  exact G.edgeKempeStep_swapOnKempeComponent
    C (C edge) target retarget.component

/-- A Tait coloring remains Tait after the edge-retargeting switch. -/
theorem isTait (retarget : EdgeKempeRetarget C edge target)
    (hC : IsTaitEdgeColoring G C) :
    IsTaitEdgeColoring G retarget.coloring := by
  exact GoertzelV24FramedTrail.isTaitEdgeColoring_swapOnKempeComponent hC
    retarget.validPair retarget.component

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The retargeted coloring lies in the same Kempe closure. -/
theorem reachable (retarget : EdgeKempeRetarget C edge target) :
    retarget.coloring ∈ G.EdgeKempeClosure C := by
  exact G.mem_edgeKempeClosure_of_step
    (G.mem_edgeKempeClosure_self C) retarget.oneStep

/-- Distinct nonzero present and target colors canonically select an
edge-retargeting component. -/
def ofValidPair (C : G.EdgeColoring Color) (edge : G.edgeSet)
    (target : Color) (hab : ValidColorPair (C edge) target) :
    EdgeKempeRetarget C edge target := by
  let component :=
    (C.bicoloredSubgraph (C edge) target).connectedComponentMk
      ⟨edge, Or.inl rfl⟩
  exact {
    validPair := hab
    component := component
    edge_mem_component := C.mem_kempeComponentSet_self (Or.inl rfl) }

end EdgeKempeRetarget

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {portCount : Nat}

/-- A component switch selected to change one degree-two boundary request
to a prescribed distinct nonzero color. -/
structure PortColorKempeRetarget
    (data : DegreeTwoBoundaryData G portCount)
    (C : G.EdgeColoring Color) (port : Fin portCount) (target : Color) where
  validPair : ValidColorPair (data.colorWord C port) target
  component :
    (C.bicoloredSubgraph (data.colorWord C port) target).ConnectedComponent
  meetsPort : data.KempeComponentMeetsPort C
    (data.colorWord C port) target component port

namespace PortColorKempeRetarget

variable {data : DegreeTwoBoundaryData G portCount}
  {C : G.EdgeColoring Color} {port : Fin portCount} {target : Color}

/-- The coloring after the selected boundary-component switch. -/
def coloring (retarget : data.PortColorKempeRetarget C port target) :
    G.EdgeColoring Color :=
  C.swapOnKempeComponent (data.colorWord C port) target
    retarget.component

/-- The switch changes the selected boundary request to the target color. -/
@[simp]
theorem colorWord_coloring
    (retarget : data.PortColorKempeRetarget C port target) :
    data.colorWord retarget.coloring port = target := by
  rw [coloring,
    data.colorWord_swapOnKempeComponent_of_meetsPort
      C retarget.validPair retarget.component port retarget.meetsPort]
  exact Equiv.swap_apply_left _ _

/-- Boundary retargeting is one genuine Kempe step. -/
theorem oneStep (retarget : data.PortColorKempeRetarget C port target) :
    G.EdgeKempeStep C retarget.coloring := by
  exact G.edgeKempeStep_swapOnKempeComponent C
    (data.colorWord C port) target retarget.component

/-- Boundary retargeting preserves the Tait condition. -/
theorem isTait (retarget : data.PortColorKempeRetarget C port target)
    (hC : IsTaitEdgeColoring G C) :
    IsTaitEdgeColoring G retarget.coloring := by
  exact GoertzelV24FramedTrail.isTaitEdgeColoring_swapOnKempeComponent hC
    retarget.validPair retarget.component

/-- Boundary retargeting stays in the original Kempe closure. -/
theorem reachable (retarget : data.PortColorKempeRetarget C port target) :
    retarget.coloring ∈ G.EdgeKempeClosure C := by
  exact G.mem_edgeKempeClosure_of_step
    (G.mem_edgeKempeClosure_self C) retarget.oneStep

end PortColorKempeRetarget

/-- Any distinct nonzero target can be reached at one degree-two port by a
single actual component switch. -/
theorem nonempty_portColorKempeRetarget
    (data : DegreeTwoBoundaryData G portCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color)
    (port : Fin portCount) (target : Color) (htarget : target ≠ 0)
    (hne : data.colorWord C port ≠ target) :
    Nonempty (data.PortColorKempeRetarget C port target) := by
  have hcurrent : data.colorWord C port ≠ 0 :=
    data.colorWord_ne_zero hdata C port
  have hab : ValidColorPair (data.colorWord C port) target :=
    ⟨hcurrent, htarget, hne⟩
  rcases data.exists_kempeComponentMeetsPort_of_colorWord_selected
      hdata C hab port (Or.inl rfl) with ⟨component, hmeets⟩
  exact ⟨{
    validPair := hab
    component := component
    meetsPort := hmeets }⟩

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

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

/-- The concrete same-base Kempe action attached to a charged terminal.
Unmatched ports retarget their missing color to the color seen across the
collar; a matched port retargets its unique common stem. -/
inductive ChargedTerminalKempeAction
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (coordinate : Bool) :
    IntrinsicCollarTerminalRepresentative
      collar.intrinsicCollarPortOverlapProfile → Prop
  | unmatchedSource
      (sourcePort : Fin 4)
      (noOverlap : ∀ targetPort : Fin 4,
        ¬ collar.PortOverlap sourcePort targetPort)
      (mismatch :
        (collar.sourceData.degreeTwoBoundaryData.colorWord
              sourceEscape.coloring sourcePort =
                crossFaceZeroColor coordinate ∧
            collar.sourceBoundaryWord sourcePort ≠
                crossFaceZeroColor coordinate) ∨
          (collar.sourceData.degreeTwoBoundaryData.colorWord
              sourceEscape.coloring sourcePort ≠
                crossFaceZeroColor coordinate ∧
            collar.sourceBoundaryWord sourcePort =
                crossFaceZeroColor coordinate))
      (action : Nonempty
        (collar.sourceData.degreeTwoBoundaryData.PortColorKempeRetarget
          sourceEscape.coloring sourcePort
            (collar.sourceBoundaryWord sourcePort))) :
      ChargedTerminalKempeAction collar sourceEscape coordinate
        (Sum.inl sourcePort)
  | matchedStem
      (sourcePort targetPort : Fin 4)
      (overlap : collar.PortOverlap sourcePort targetPort)
      (stem : collar.commonCore.edgeSet)
      (incident_eq : incidentEdgeFinset collar.commonCore
        (collar.sourcePortInCommonCore sourcePort) = {stem})
      (mismatch :
        (collar.sourceCommonColoring sourceEscape stem =
              crossFaceZeroColor coordinate ∧
            collar.targetCommonColoring stem ≠
              crossFaceZeroColor coordinate) ∨
          (collar.sourceCommonColoring sourceEscape stem ≠
              crossFaceZeroColor coordinate ∧
            collar.targetCommonColoring stem =
              crossFaceZeroColor coordinate))
      (action : Nonempty
        (EdgeKempeRetarget sourceEscape.coloring
          (collar.commonEdgeInSource stem)
          (collar.targetCommonColoring stem))) :
      ChargedTerminalKempeAction collar sourceEscape coordinate
        (Sum.inl sourcePort)
  | unmatchedTarget
      (targetPort : ↑(intrinsicCollarUnmatchedTargetPorts
        collar.intrinsicCollarPortOverlapProfile))
      (noOverlap : ∀ sourcePort : Fin 4,
        ¬ collar.PortOverlap sourcePort targetPort.1)
      (mismatch :
        (collar.targetData.degreeTwoBoundaryData.colorWord
              collar.targetEscape.coloring targetPort.1 =
                crossFaceZeroColor coordinate ∧
            collar.targetBoundaryWordInSource sourceEscape targetPort.1 ≠
                crossFaceZeroColor coordinate) ∨
          (collar.targetData.degreeTwoBoundaryData.colorWord
              collar.targetEscape.coloring targetPort.1 ≠
                crossFaceZeroColor coordinate ∧
            collar.targetBoundaryWordInSource sourceEscape targetPort.1 =
                crossFaceZeroColor coordinate))
      (action : Nonempty
        (collar.targetData.degreeTwoBoundaryData.PortColorKempeRetarget
          collar.targetEscape.coloring targetPort.1
            (collar.targetBoundaryWordInSource sourceEscape targetPort.1))) :
      ChargedTerminalKempeAction collar sourceEscape coordinate
        (Sum.inr targetPort)

/-- Every charged terminal color witness constructs its corresponding
actual component switch; no additional escape hypothesis is required. -/
theorem ChargedTerminalColorWitness.nonempty_kempeAction
    {coordinate : Bool}
    {representative : IntrinsicCollarTerminalRepresentative
      collar.intrinsicCollarPortOverlapProfile}
    (witness : ChargedTerminalColorWitness collar sourceEscape coordinate
      representative) :
    ChargedTerminalKempeAction collar sourceEscape coordinate
      representative := by
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  cases witness with
  | unmatchedSource sourcePort noOverlap mismatch =>
      have hne : collar.sourceData.degreeTwoBoundaryData.colorWord
          sourceEscape.coloring sourcePort ≠
            collar.sourceBoundaryWord sourcePort := by
        rcases mismatch with hsource | htarget
        · intro heq
          exact hsource.2 (heq.symm.trans hsource.1)
        · intro heq
          exact htarget.1 (heq.trans htarget.2)
      apply ChargedTerminalKempeAction.unmatchedSource
        sourcePort noOverlap mismatch
      exact collar.sourceData.degreeTwoBoundaryData.nonempty_portColorKempeRetarget
          (collar.sourceData.degreeTwoBoundaryData_wellFormed hcubic)
          sourceEscape.coloring sourcePort
          (collar.sourceBoundaryWord sourcePort)
          (collar.sourceBoundaryWord_apply_ne_zero sourcePort) hne
  | matchedStem sourcePort targetPort overlap stem incident mismatch =>
      have hne : sourceEscape.coloring (collar.commonEdgeInSource stem) ≠
          collar.targetCommonColoring stem := by
        rw [← collar.sourceCommonColoring_apply_commonEdgeInSource]
        rcases mismatch with hsource | htarget
        · intro heq
          exact hsource.2 (heq.symm.trans hsource.1)
        · intro heq
          exact htarget.1 (heq.trans htarget.2)
      have hab : ValidColorPair
          (sourceEscape.coloring (collar.commonEdgeInSource stem))
          (collar.targetCommonColoring stem) :=
        ⟨sourceEscape.isTait _, collar.targetCommonColoring_isTait stem, hne⟩
      apply ChargedTerminalKempeAction.matchedStem
        sourcePort targetPort overlap stem incident mismatch
      exact ⟨EdgeKempeRetarget.ofValidPair sourceEscape.coloring
          (collar.commonEdgeInSource stem)
          (collar.targetCommonColoring stem) hab⟩
  | unmatchedTarget targetPort noOverlap mismatch =>
      have hne : collar.targetData.degreeTwoBoundaryData.colorWord
          collar.targetEscape.coloring targetPort.1 ≠
            collar.targetBoundaryWordInSource sourceEscape targetPort.1 := by
        rcases mismatch with htarget | hsource
        · intro heq
          exact htarget.2 (heq.symm.trans htarget.1)
        · intro heq
          exact hsource.1 (heq.trans hsource.2)
      apply ChargedTerminalKempeAction.unmatchedTarget
        targetPort noOverlap mismatch
      exact collar.targetData.degreeTwoBoundaryData.nonempty_portColorKempeRetarget
          (collar.targetData.degreeTwoBoundaryData_wellFormed hcubic)
          collar.targetEscape.coloring targetPort.1
          (collar.targetBoundaryWordInSource sourceEscape targetPort.1)
          (collar.targetBoundaryWordInSource_apply_ne_zero
            sourceEscape targetPort.1) hne

namespace FirstHitSingletonCompanionTransferPath

variable {firstHit : FirstHitSingletonCompanionTransferPath
  (collar := collar) (sourceEscape := sourceEscape)}

namespace TransverseCompanionChange

variable {change : firstHit.TransverseCompanionChange}

namespace ComplementarySupportCorner.ChargedSupportRoute

variable {corner : change.ComplementarySupportCorner}

/-- Every charged complementary-support route ends in a constructed
same-base Kempe action on the source deletion, target deletion, or unique
matched stem. -/
theorem nonempty_finishKempeAction
    (route : corner.ChargedSupportRoute) :
    ChargedTerminalKempeAction collar sourceEscape
      (!firstHit.transfer.coordinate) route.finishRepresentative :=
  route.finishColorWitness.nonempty_kempeAction

end ComplementarySupportCorner.ChargedSupportRoute
end TransverseCompanionChange
end FirstHitSingletonCompanionTransferPath
end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
