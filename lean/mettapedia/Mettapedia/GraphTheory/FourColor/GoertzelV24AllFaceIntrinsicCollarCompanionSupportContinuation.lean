import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionSupportTerminal

/-! Degree-two terminal passages in complementary scalar-support strands. -/

namespace Mettapedia.GraphTheory.FourColor

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open GoertzelV24CorridorPumping
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24FourDefectBoundary
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {graphData : Data G}
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

namespace FirstHitSingletonCompanionTransferPath

variable {firstHit : FirstHitSingletonCompanionTransferPath
  (collar := collar) (sourceEscape := sourceEscape)}

namespace TransverseCompanionChange

variable {change : firstHit.TransverseCompanionChange}

namespace ComplementarySupportCorner

namespace FirstTerminalSupportStrand

variable {corner : change.ComplementarySupportCorner}
  {strand : corner.FirstTerminalSupportStrand}

/-- Following a degree-two named terminal in the outgoing direction reaches
a distinct charged named terminal. -/
structure ChargedContinuationStrand
    (continuation : strand.TerminalContinuation) where
  finish : collar.commonPortVertexFinset
  finish_ne_start : finish.1 ≠ strand.finish.1
  path : corner.complementarySupportGraph.Walk strand.finish.1 finish.1
  path_isPath : path.IsPath
  path_positive : 0 < path.length
  terminal_edge_avoided : strand.terminalSupportEdge.1 ∉ path.edges
  continuation_edge_mem : continuation.edge.1 ∈ path.edges
  finish_boundary_ne_zero :
    crossFaceCoordinate (!firstHit.transfer.coordinate)
      ((collar.commonDiscrepancyBoundaryState sourceEscape).1 finish) ≠ 0

/-- Following a degree-two named terminal can instead close its support
component into a simple cycle through both the arrival and outgoing edges. -/
structure ClosedContinuationCycle
    (continuation : strand.TerminalContinuation) where
  supportCycle : corner.complementarySupportGraph.Walk
    strand.finish.1 strand.finish.1
  supportCycle_isCycle : supportCycle.IsCycle
  terminal_edge_mem : strand.terminalSupportEdge.1 ∈ supportCycle.edges
  continuation_edge_mem : continuation.edge.1 ∈ supportCycle.edges

/-- A degree-two terminal passage is exhaustive: its uniquely directed
support component either reaches a charged collar terminal or closes into a
simple support cycle. -/
theorem chargedContinuationStrand_or_closedContinuationCycle
    (continuation : strand.TerminalContinuation) :
    Nonempty (strand.ChargedContinuationStrand continuation) ∨
      Nonempty (strand.ClosedContinuationCycle continuation) := by
  classical
  let supportGraph := corner.complementarySupportGraph
  let scalarChain : collar.commonCore.edgeSet → F2 :=
    fun edge => crossFaceCoordinate (!firstHit.transfer.coordinate)
      (collar.commonDiscrepancy sourceEscape edge)
  have hstartDegree : supportGraph.degree strand.finish.1 = 2 := by
    rw [← incidentEdgeFinset_card_eq_degree]
    exact (strand.nonempty_terminalContinuation_iff_supportDegree_eq_two).1
      <| Nonempty.intro continuation
  have hterminalIncident : strand.finish.1 ∈
      strand.terminalSupportEdge.1 := by
    simpa only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and] using strand.terminalSupportEdge_mem_incident
  have hcontinuationIncident : strand.finish.1 ∈ continuation.edge.1 := by
    simpa only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and] using continuation.edge_mem
  rcases exists_directed_odd_path_or_cycle_of_incident_pair
      (H := supportGraph) strand.finish.1 strand.terminalSupportEdge
        continuation.edge continuation.edge_ne_terminal.symm
        hterminalIncident hcontinuationIncident hstartDegree with
    hcharged | hclosed
  · left
    rcases hcharged with
      ⟨finish, hfinishNe, hfinishOdd, path, hpath, hterminalAvoided,
        hcontinuationMem⟩
    have hfinishTerminal : finish ∈ collar.commonPortVertexFinset := by
      have hscalarBoundary : scalarVertexKirchhoffSum collar.commonCore
          scalarChain finish ≠ 0 := by
        exact (scalarSupportGraph_degree_odd_iff scalarChain finish).1
          hfinishOdd
      by_contra hnotTerminal
      apply hscalarBoundary
      rw [scalarVertexKirchhoffSum_crossFaceCoordinate,
        collar.vertexKirchhoffSum_commonDiscrepancy_eq_zero_of_not_mem_commonPortVertexFinset
          sourceEscape finish hnotTerminal]
      cases (!firstHit.transfer.coordinate) <;> rfl
    let finishTerminal : collar.commonPortVertexFinset :=
      ⟨finish, hfinishTerminal⟩
    have hfinishBoundary :
        crossFaceCoordinate (!firstHit.transfer.coordinate)
          ((collar.commonDiscrepancyBoundaryState sourceEscape).1
            finishTerminal) ≠ 0 := by
      rw [commonDiscrepancyBoundaryState_apply,
        ← scalarVertexKirchhoffSum_crossFaceCoordinate]
      exact (scalarSupportGraph_degree_odd_iff scalarChain finish).1
        hfinishOdd
    have hpositive : 0 < path.length := by
      by_contra hnotPositive
      have hzero : path.length = 0 := Nat.eq_zero_of_not_pos hnotPositive
      exact hfinishNe (path.eq_of_length_eq_zero hzero).symm
    exact ⟨{
      finish := finishTerminal
      finish_ne_start := hfinishNe
      path := path
      path_isPath := hpath
      path_positive := hpositive
      terminal_edge_avoided := hterminalAvoided
      continuation_edge_mem := hcontinuationMem
      finish_boundary_ne_zero := hfinishBoundary }⟩
  · right
    rcases hclosed with
      ⟨supportCycle, hsupportCycle, hterminalMem, hcontinuationMem⟩
    exact ⟨{
      supportCycle := supportCycle
      supportCycle_isCycle := hsupportCycle
      terminal_edge_mem := hterminalMem
      continuation_edge_mem := hcontinuationMem }⟩

namespace ChargedContinuationStrand

variable {continuation : strand.TerminalContinuation}
  (continued : strand.ChargedContinuationStrand continuation)

/-- The canonical fixed-collar representative of the charged endpoint. -/
noncomputable def finishRepresentative :
    IntrinsicCollarTerminalRepresentative
      collar.intrinsicCollarPortOverlapProfile :=
  collar.intrinsicCollarTerminalRepresentativeEquiv.symm continued.finish

@[simp]
theorem finishRepresentative_apply :
    collar.intrinsicCollarTerminalRepresentativeEquiv
        continued.finishRepresentative = continued.finish :=
  Equiv.apply_symm_apply _ _

/-- The charged endpoint is read exactly from the fixed collar word. -/
theorem finishBoundaryWord_eq :
    intrinsicCollarTerminalBoundaryWord
        collar.intrinsicCollarPortOverlapProfile
        (collar.intrinsicCollarCorrectionWord sourceEscape)
        (intrinsicCollarTerminalCoordinateOfRepresentative
          continued.finishRepresentative) =
      (collar.commonDiscrepancyBoundaryState sourceEscape).1
        continued.finish := by
  simpa only [continued.finishRepresentative_apply] using
    (collar.intrinsicCollarTerminalBoundaryWord_representative_eq_boundaryState
      sourceEscape continued.finishRepresentative)

/-- Hence the complementary coordinate of the fixed endpoint word is
genuinely charged. -/
theorem finishBoundaryWord_coordinate_ne_zero :
    crossFaceCoordinate (!firstHit.transfer.coordinate)
      (intrinsicCollarTerminalBoundaryWord
        collar.intrinsicCollarPortOverlapProfile
        (collar.intrinsicCollarCorrectionWord sourceEscape)
        (intrinsicCollarTerminalCoordinateOfRepresentative
          continued.finishRepresentative)) ≠ 0 := by
  rw [continued.finishBoundaryWord_eq]
  exact continued.finish_boundary_ne_zero

/-- The first scalar-support edge of the directed continuation path. -/
def initialSupportEdge : corner.complementarySupportGraph.edgeSet :=
  continued.path.edgeSubtypeSupport.head
    (edgeSubtypeSupport_ne_nil_of_length_pos
      continued.path continued.path_positive)

theorem initialSupportEdge_mem_path :
    continued.initialSupportEdge.1 ∈ continued.path.edges := by
  have hhead : continued.initialSupportEdge ∈
      continued.path.edgeSubtypeSupport := by
    exact List.head_mem
      (edgeSubtypeSupport_ne_nil_of_length_pos
        continued.path continued.path_positive)
  rw [← continued.path.edgeSubtypeSupport_map_val]
  exact List.mem_map.mpr ⟨continued.initialSupportEdge, hhead, rfl⟩

theorem initialSupportEdge_mem_incident :
    continued.initialSupportEdge ∈
      incidentEdgeFinset corner.complementarySupportGraph strand.finish.1 := by
  have hedges : continued.path.edges ≠ [] :=
    SimpleGraph.Walk.edges_eq_nil.not.mpr
      (SimpleGraph.Walk.not_nil_iff_lt_length.mpr
        continued.path_positive)
  have hvalue : continued.initialSupportEdge.1 =
      s(strand.finish.1, continued.path.snd) := by
    calc
      continued.initialSupportEdge.1 =
          continued.path.edges[0]'(by simpa using continued.path_positive) :=
        continued.path.edgeSubtypeSupport_head_val continued.path_positive
      _ = continued.path.edges.head hedges :=
        (List.head_eq_getElem_zero hedges).symm
      _ = s(strand.finish.1, continued.path.snd) :=
        continued.path.head_edges_eq_mk_start_snd hedges
  rw [incidentEdgeFinset]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hvalue]
  exact Sym2.mem_mk_left _ _

/-- Direction at the degree-two passage is literal: the first edge of the
continued path is the selected outgoing edge. -/
theorem initialSupportEdge_eq_continuation :
    continued.initialSupportEdge = continuation.edge := by
  let incident := incidentEdgeFinset corner.complementarySupportGraph
    strand.finish.1
  have hcard : incident.card = 2 :=
    (strand.nonempty_terminalContinuation_iff_supportDegree_eq_two).1
      ⟨continuation⟩
  have hpairCard :
      ({strand.terminalSupportEdge, continuation.edge} :
          Finset corner.complementarySupportGraph.edgeSet).card = 2 :=
    Finset.card_pair_eq_two_iff.mpr continuation.edge_ne_terminal.symm
  have hpairSubset :
      ({strand.terminalSupportEdge, continuation.edge} :
          Finset corner.complementarySupportGraph.edgeSet) ⊆ incident := by
    intro edge hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl
    · exact strand.terminalSupportEdge_mem_incident
    · exact continuation.edge_mem
  have hpairEq :
      ({strand.terminalSupportEdge, continuation.edge} :
          Finset corner.complementarySupportGraph.edgeSet) = incident := by
    apply Finset.eq_of_subset_of_card_le hpairSubset
    rw [hpairCard, hcard]
  have hinitial : continued.initialSupportEdge ∈ incident :=
    continued.initialSupportEdge_mem_incident
  rw [← hpairEq] at hinitial
  simp only [Finset.mem_insert, Finset.mem_singleton] at hinitial
  rcases hinitial with hincoming | houtgoing
  · exact False.elim (continued.terminal_edge_avoided
      (hincoming ▸ continued.initialSupportEdge_mem_path))
  · exact houtgoing

/-- The continuation path after forgetting the scalar-support subgraph. -/
def ambientPath : collar.commonCore.Walk strand.finish.1 continued.finish.1 :=
  continued.path.mapLe (scalarSupportGraph_le (fun edge =>
    crossFaceCoordinate (!firstHit.transfer.coordinate)
      (collar.commonDiscrepancy sourceEscape edge)))

@[simp]
theorem ambientPath_length :
    continued.ambientPath.length = continued.path.length := by
  calc
    continued.ambientPath.length = continued.ambientPath.edges.length :=
      continued.ambientPath.length_edges.symm
    _ = continued.path.edges.length := by
      exact congrArg List.length
        (SimpleGraph.Walk.edges_mapLe_eq_edges _ _)
    _ = continued.path.length := continued.path.length_edges

theorem ambientPath_isPath : continued.ambientPath.IsPath :=
  continued.path_isPath.mapLe (scalarSupportGraph_le (fun edge =>
    crossFaceCoordinate (!firstHit.transfer.coordinate)
      (collar.commonDiscrepancy sourceEscape edge)))

theorem ambientPath_positive : 0 < continued.ambientPath.length := by
  rw [continued.ambientPath_length]
  exact continued.path_positive

theorem support : ∀ edge ∈ continued.ambientPath.edgeSubtypeSupport,
    crossFaceCoordinate (!firstHit.transfer.coordinate)
      (collar.sourceCommonColoring sourceEscape edge +
        collar.targetCommonColoring edge) ≠ 0 := by
  simpa only [ambientPath, commonDiscrepancy_apply] using
    (scalarSupportWalk_support (fun edge =>
      crossFaceCoordinate (!firstHit.transfer.coordinate)
        (collar.commonDiscrepancy sourceEscape edge)) continued.path)

/-- The first common-core edge of the continued path. -/
def initialAmbientEdge : collar.commonCore.edgeSet :=
  continued.ambientPath.edgeSubtypeSupport.head
    (edgeSubtypeSupport_ne_nil_of_length_pos
      continued.ambientPath continued.ambientPath_positive)

theorem initialAmbientEdge_val_eq_initialSupportEdge_val :
    continued.initialAmbientEdge.1 = continued.initialSupportEdge.1 := by
  calc
    continued.initialAmbientEdge.1 =
        continued.ambientPath.edges[0]'(by
          simpa using continued.ambientPath_positive) :=
      continued.ambientPath.edgeSubtypeSupport_head_val
        continued.ambientPath_positive
    _ = continued.path.edges[0]'(by
          simpa using continued.path_positive) := by
      simp only [ambientPath, SimpleGraph.Walk.edges_mapLe_eq_edges]
    _ = continued.initialSupportEdge.1 :=
      (continued.path.edgeSubtypeSupport_head_val
        continued.path_positive).symm

theorem initialAmbientEdge_eq_continuation_ambientEdge :
    continued.initialAmbientEdge = continuation.ambientEdge := by
  apply Subtype.ext
  calc
    continued.initialAmbientEdge.1 = continued.initialSupportEdge.1 :=
      continued.initialAmbientEdge_val_eq_initialSupportEdge_val
    _ = continuation.edge.1 :=
      congrArg Subtype.val continued.initialSupportEdge_eq_continuation
    _ = continuation.ambientEdge.1 := rfl

theorem initialAmbientEdge_support :
    crossFaceCoordinate (!firstHit.transfer.coordinate)
      (collar.sourceCommonColoring sourceEscape continued.initialAmbientEdge +
        collar.targetCommonColoring continued.initialAmbientEdge) ≠ 0 := by
  apply continued.support continued.initialAmbientEdge
  exact List.head_mem
    (edgeSubtypeSupport_ne_nil_of_length_pos
      continued.ambientPath continued.ambientPath_positive)

/-- The exact finite-state word carried from the passage terminal to the
charged terminal. -/
noncomputable def stateWord :
    List (ScalarDiscrepancyColorState
      (!firstHit.transfer.coordinate)) :=
  scalarDiscrepancyColorStateWord
    (collar.sourceCommonColoring sourceEscape)
    collar.targetCommonColoring
    (collar.sourceCommonColoring_isTait sourceEscape)
    collar.targetCommonColoring_isTait
    (!firstHit.transfer.coordinate) continued.ambientPath continued.support

@[simp]
theorem stateWord_length :
    continued.stateWord.length = continued.path.length := by
  rw [stateWord, scalarDiscrepancyColorStateWord_length,
    continued.ambientPath_length]

theorem stateWord_ne_nil : continued.stateWord ≠ [] := by
  apply List.length_pos_iff.mp
  rw [continued.stateWord_length]
  exact continued.path_positive

/-- The actual first finite state on the continued path. -/
noncomputable def initialState :
    ScalarDiscrepancyColorState (!firstHit.transfer.coordinate) :=
  continued.stateWord.head continued.stateWord_ne_nil

theorem initialState_eq_stateOf :
    continued.initialState =
      scalarDiscrepancyColorStateOf
        (collar.sourceCommonColoring sourceEscape)
        collar.targetCommonColoring
        (collar.sourceCommonColoring_isTait sourceEscape)
        collar.targetCommonColoring_isTait
        (!firstHit.transfer.coordinate)
        continued.initialAmbientEdge continued.initialAmbientEdge_support := by
  unfold initialState stateWord initialAmbientEdge
  unfold scalarDiscrepancyColorStateWord
  rw [List.head_pmap]

/-- The graph-extracted initial state is exactly the state already attached
to the selected terminal continuation. -/
theorem initialState_eq_continuation_state :
    continued.initialState = continuation.state := by
  rw [continued.initialState_eq_stateOf]
  apply Subtype.ext
  apply Prod.ext
  · change collar.sourceCommonColoring sourceEscape
        continued.initialAmbientEdge =
      collar.sourceCommonColoring sourceEscape continuation.ambientEdge
    rw [continued.initialAmbientEdge_eq_continuation_ambientEdge]
  · change collar.targetCommonColoring continued.initialAmbientEdge =
      collar.targetCommonColoring continuation.ambientEdge
    rw [continued.initialAmbientEdge_eq_continuation_ambientEdge]

/-- A degree-two passage followed to its charged endpoint is one exact
finite-state transfer. -/
theorem exactTransfer :
    ExactRelationalTransfer ScalarDiscrepancyColorTransition
      (continued.path.length - 1)
      (continued.stateWord.head continued.stateWord_ne_nil)
      (continued.stateWord.getLast continued.stateWord_ne_nil) := by
  simpa only [stateWord, continued.ambientPath_length] using
    (scalarDiscrepancyColorStateWord_exactTransfer
      (collar.sourceCommonColoring sourceEscape)
      collar.targetCommonColoring
      (collar.sourceCommonColoring_isTait sourceEscape)
      collar.targetCommonColoring_isTait
      (!firstHit.transfer.coordinate)
      continued.ambientPath_isPath.isTrail continued.ambientPath_positive
      continued.support)

/-- Concatenating the incoming strand, the one terminal transition, and the
directed continuation gives one exact transfer from the complementary turn
to the charged endpoint. -/
theorem exactTransfer_from_corner :
    ExactRelationalTransfer ScalarDiscrepancyColorTransition
      (strand.path.length + continued.path.length - 1)
      (strand.stateWord.head strand.stateWord_ne_nil)
      (continued.stateWord.getLast continued.stateWord_ne_nil) := by
  have hfirst :
      ExactRelationalTransfer ScalarDiscrepancyColorTransition
        (strand.path.length - 1)
        (strand.stateWord.head strand.stateWord_ne_nil)
        strand.terminalState := by
    simpa only [FirstTerminalSupportStrand.terminalState] using
      strand.exactTransfer
  have htransition : ScalarDiscrepancyColorTransition
      strand.terminalState continued.initialState := by
    rw [continued.initialState_eq_continuation_state]
    exact continuation.terminalState_transition
  have hbridge :
      ExactRelationalTransfer ScalarDiscrepancyColorTransition 1
        strand.terminalState continued.initialState := by
    simpa using ExactRelationalTransfer.succ htransition
      (ExactRelationalTransfer.zero
        (oneStep := ScalarDiscrepancyColorTransition)
        continued.initialState)
  have hsecond :
      ExactRelationalTransfer ScalarDiscrepancyColorTransition
        (continued.path.length - 1) continued.initialState
        (continued.stateWord.getLast continued.stateWord_ne_nil) := by
    simpa only [initialState] using continued.exactTransfer
  have hcombined := hfirst.comp (hbridge.comp hsecond)
  have hfirstPositive := strand.path_positive
  have hsecondPositive := continued.path_positive
  have hlength :
      strand.path.length - 1 + (1 + (continued.path.length - 1)) =
        strand.path.length + continued.path.length - 1 := by
    omega
  rw [hlength] at hcombined
  exact hcombined

end ChargedContinuationStrand

namespace ClosedContinuationCycle

variable {continuation : strand.TerminalContinuation}
  (closed : strand.ClosedContinuationCycle continuation)

/-- The closed continuation after forgetting the scalar-support subgraph. -/
def ambientCycle : collar.commonCore.Walk strand.finish.1 strand.finish.1 :=
  closed.supportCycle.mapLe (scalarSupportGraph_le (fun edge =>
    crossFaceCoordinate (!firstHit.transfer.coordinate)
      (collar.commonDiscrepancy sourceEscape edge)))

@[simp]
theorem ambientCycle_length :
    closed.ambientCycle.length = closed.supportCycle.length := by
  calc
    closed.ambientCycle.length = closed.ambientCycle.edges.length :=
      closed.ambientCycle.length_edges.symm
    _ = closed.supportCycle.edges.length := by
      exact congrArg List.length
        (SimpleGraph.Walk.edges_mapLe_eq_edges _ _)
    _ = closed.supportCycle.length := closed.supportCycle.length_edges

theorem ambientCycle_isCycle : closed.ambientCycle.IsCycle :=
  closed.supportCycle_isCycle.mapLe (scalarSupportGraph_le (fun edge =>
    crossFaceCoordinate (!firstHit.transfer.coordinate)
      (collar.commonDiscrepancy sourceEscape edge)))

theorem ambientCycle_positive : 0 < closed.ambientCycle.length :=
  lt_of_lt_of_le (by omega) closed.ambientCycle_isCycle.three_le_length

theorem support : ∀ edge ∈ closed.ambientCycle.edgeSubtypeSupport,
    crossFaceCoordinate (!firstHit.transfer.coordinate)
      (collar.sourceCommonColoring sourceEscape edge +
        collar.targetCommonColoring edge) ≠ 0 := by
  simpa only [ambientCycle, commonDiscrepancy_apply] using
    (scalarSupportWalk_support (fun edge =>
      crossFaceCoordinate (!firstHit.transfer.coordinate)
        (collar.commonDiscrepancy sourceEscape edge)) closed.supportCycle)

noncomputable def stateWord :
    List (ScalarDiscrepancyColorState
      (!firstHit.transfer.coordinate)) :=
  scalarDiscrepancyColorStateWord
    (collar.sourceCommonColoring sourceEscape)
    collar.targetCommonColoring
    (collar.sourceCommonColoring_isTait sourceEscape)
    collar.targetCommonColoring_isTait
    (!firstHit.transfer.coordinate) closed.ambientCycle closed.support

@[simp]
theorem stateWord_length :
    closed.stateWord.length = closed.supportCycle.length := by
  rw [stateWord, scalarDiscrepancyColorStateWord_length,
    closed.ambientCycle_length]

theorem stateWord_ne_nil : closed.stateWord ≠ [] := by
  apply List.length_pos_iff.mp
  rw [closed.stateWord_length]
  exact lt_of_lt_of_le (by omega)
    closed.supportCycle_isCycle.three_le_length

theorem linearizedExactTransfer :
    ExactRelationalTransfer ScalarDiscrepancyColorTransition
      (closed.supportCycle.length - 1)
      (closed.stateWord.head closed.stateWord_ne_nil)
      (closed.stateWord.getLast closed.stateWord_ne_nil) := by
  simpa only [stateWord, closed.ambientCycle_length] using
    (scalarDiscrepancyColorStateWord_exactTransfer
      (collar.sourceCommonColoring sourceEscape)
      collar.targetCommonColoring
      (collar.sourceCommonColoring_isTait sourceEscape)
      collar.targetCommonColoring_isTait
      (!firstHit.transfer.coordinate)
      closed.ambientCycle_isCycle.isTrail closed.ambientCycle_positive
      closed.support)

theorem closingTransition :
    ScalarDiscrepancyColorTransition
      (closed.stateWord.getLast closed.stateWord_ne_nil)
      (closed.stateWord.head closed.stateWord_ne_nil) := by
  simpa only [stateWord] using
    (scalarDiscrepancyColorStateWord_closingTransition
      (collar.sourceCommonColoring sourceEscape)
      collar.targetCommonColoring
      (collar.sourceCommonColoring_isTait sourceEscape)
      collar.targetCommonColoring_isTait
      (!firstHit.transfer.coordinate)
      closed.ambientCycle_isCycle closed.support)

/-- A closed continuation is an exact positive-period return. -/
theorem exactReturn :
    ExactRelationalTransfer ScalarDiscrepancyColorTransition
      closed.supportCycle.length
      (closed.stateWord.head closed.stateWord_ne_nil)
      (closed.stateWord.head closed.stateWord_ne_nil) := by
  have hclosingStep :
      ExactRelationalTransfer ScalarDiscrepancyColorTransition 1
        (closed.stateWord.getLast closed.stateWord_ne_nil)
        (closed.stateWord.head closed.stateWord_ne_nil) := by
    simpa using ExactRelationalTransfer.succ closed.closingTransition
      (ExactRelationalTransfer.zero
        (oneStep := ScalarDiscrepancyColorTransition)
        (closed.stateWord.head closed.stateWord_ne_nil))
  have hreturn := closed.linearizedExactTransfer.comp hclosingStep
  have hpositive : 0 < closed.supportCycle.length :=
    lt_of_lt_of_le (by omega)
      closed.supportCycle_isCycle.three_le_length
  have hlength : closed.supportCycle.length - 1 + 1 =
      closed.supportCycle.length := by omega
  rw [hlength] at hreturn
  exact hreturn

end ClosedContinuationCycle

end FirstTerminalSupportStrand

/-- A complementary turn reaches a charged collar terminal either on its
first directed strand or after passing through one degree-two named port. -/
inductive ChargedSupportRoute
    (corner : change.ComplementarySupportCorner) where
  | direct (strand : corner.FirstTerminalSupportStrand)
      (charged : strand.terminalBoundaryCoordinate ≠ 0)
  | continued (strand : corner.FirstTerminalSupportStrand)
      (continuation : strand.TerminalContinuation)
      (route : strand.ChargedContinuationStrand continuation)

/-- The closed alternative is either the initial complementary component or
the component obtained after directing a degree-two terminal passage. -/
inductive ClosedSupportRoute
    (corner : change.ComplementarySupportCorner) where
  | direct (strand : corner.ClosedSupportStrand)
  | continued (strand : corner.FirstTerminalSupportStrand)
      (continuation : strand.TerminalContinuation)
      (route : strand.ClosedContinuationCycle continuation)

/-- No degree-two terminal remains as an obligation: every complementary
turn reaches an explicitly charged collar endpoint or an explicitly closed
support route. -/
theorem chargedSupportRoute_or_closedSupportRoute
    (corner : change.ComplementarySupportCorner) :
    Nonempty corner.ChargedSupportRoute ∨
      Nonempty corner.ClosedSupportRoute := by
  rcases corner.firstTerminalSupportStrand_or_closedSupportStrand with
    hterminal | hclosed
  · rcases hterminal with ⟨strand⟩
    rcases strand.terminalBoundary_or_continuation with
      hcharged | hcontinuation
    · exact Or.inl ⟨ChargedSupportRoute.direct strand hcharged⟩
    · rcases hcontinuation with ⟨continuation⟩
      rcases strand.chargedContinuationStrand_or_closedContinuationCycle
          continuation with hcharged | hclosed
      · rcases hcharged with ⟨route⟩
        exact Or.inl
          ⟨ChargedSupportRoute.continued strand continuation route⟩
      · rcases hclosed with ⟨route⟩
        exact Or.inr
          ⟨ClosedSupportRoute.continued strand continuation route⟩
  · rcases hclosed with ⟨strand⟩
    exact Or.inr ⟨ClosedSupportRoute.direct strand⟩

end ComplementarySupportCorner
end TransverseCompanionChange
end FirstHitSingletonCompanionTransferPath
end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
