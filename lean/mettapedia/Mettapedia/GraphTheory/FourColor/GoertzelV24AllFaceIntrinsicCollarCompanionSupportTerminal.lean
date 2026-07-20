import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionSupportTransfer

/-! Canonical terminal data for complementary scalar-support strands. -/

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

variable {W : Type*} {H : SimpleGraph W}

/-- A positive walk has a nonempty word of edge-set members. -/
theorem edgeSubtypeSupport_ne_nil_of_length_pos
    {start finish : W} (path : H.Walk start finish)
    (hpositive : 0 < path.length) :
    path.edgeSubtypeSupport ≠ [] := by
  intro hnil
  have hlength := congrArg List.length hnil
  rw [path.edgeSubtypeSupport_length] at hlength
  exact (Nat.ne_of_gt hpositive) hlength

/-- The last member of the edge word is the edge-set form of the last dart. -/
theorem edgeSubtypeSupport_getLast_eq_lastEdgeSet
    {start finish : W} (path : H.Walk start finish)
    (hpositive : 0 < path.length) :
    path.edgeSubtypeSupport.getLast
        (edgeSubtypeSupport_ne_nil_of_length_pos path hpositive) =
      path.lastEdgeSet
        (SimpleGraph.Walk.not_nil_iff_lt_length.mpr hpositive) := by
  let hword := edgeSubtypeSupport_ne_nil_of_length_pos path hpositive
  let hnil := SimpleGraph.Walk.not_nil_iff_lt_length.mpr hpositive
  have hedges : path.edges ≠ [] :=
    SimpleGraph.Walk.edges_eq_nil.not.mpr hnil
  have hmapped : path.edgeSubtypeSupport.map Subtype.val ≠ [] := by
    intro hmap
    exact hword (List.map_eq_nil_iff.mp hmap)
  apply Subtype.ext
  calc
    (path.edgeSubtypeSupport.getLast hword).1 =
        (path.edgeSubtypeSupport.map Subtype.val).getLast hmapped := by
      exact (List.getLast_map hmapped).symm
    _ = path.edges.getLast hedges := by
      simp only [path.edgeSubtypeSupport_map_val]
    _ = s(path.penultimate, finish) :=
      path.getLast_edges_eq_mk_penultimate_end hedges
    _ = (path.lastEdgeSet hnil).1 := by rfl

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
  (strand : corner.FirstTerminalSupportStrand)

/-- The unique source occurrence or unmatched target occurrence naming the
first terminal reached by the complementary strand. -/
noncomputable def terminalRepresentative :
    IntrinsicCollarTerminalRepresentative
      collar.intrinsicCollarPortOverlapProfile :=
  collar.intrinsicCollarTerminalRepresentativeEquiv.symm strand.finish

@[simp]
theorem terminalRepresentative_apply :
    collar.intrinsicCollarTerminalRepresentativeEquiv
        strand.terminalRepresentative = strand.finish :=
  Equiv.apply_symm_apply _ _

/-- Canonical terminal representatives eliminate duplicated target ports:
the strand ends either at a source port or at a target port with no source
overlap. -/
theorem exists_sourcePort_or_unmatchedTargetPort :
    (∃ sourcePort : Fin 4,
      strand.finish = collar.sourcePortCommonTerminal sourcePort) ∨
    ∃ targetPort : ↑(intrinsicCollarUnmatchedTargetPorts
        collar.intrinsicCollarPortOverlapProfile),
      strand.finish = collar.targetPortCommonTerminal targetPort.1 := by
  have hfinish := strand.terminalRepresentative_apply
  generalize hrepresentative : strand.terminalRepresentative =
      representative at hfinish
  rcases representative with sourcePort | targetPort
  · left
    refine ⟨sourcePort, ?_⟩
    change collar.sourcePortCommonTerminal sourcePort = strand.finish
      at hfinish
    exact hfinish.symm
  · right
    refine ⟨targetPort, ?_⟩
    change collar.targetPortCommonTerminal targetPort.1 = strand.finish
      at hfinish
    exact hfinish.symm

/-- The complementary scalar coordinate of the exact Kirchhoff boundary at
the first terminal. -/
def terminalBoundaryCoordinate : F2 :=
  crossFaceCoordinate (!firstHit.transfer.coordinate)
    ((collar.commonDiscrepancyBoundaryState sourceEscape).1 strand.finish)

/-- The variable common-core boundary value at the first terminal is exactly
the fixed collar word at its canonical representative. -/
theorem terminalBoundaryWord_eq :
    intrinsicCollarTerminalBoundaryWord
        collar.intrinsicCollarPortOverlapProfile
        (collar.intrinsicCollarCorrectionWord sourceEscape)
        (intrinsicCollarTerminalCoordinateOfRepresentative
          strand.terminalRepresentative) =
      (collar.commonDiscrepancyBoundaryState sourceEscape).1
        strand.finish := by
  simpa only [strand.terminalRepresentative_apply] using
    (collar.intrinsicCollarTerminalBoundaryWord_representative_eq_boundaryState
      sourceEscape strand.terminalRepresentative)

/-- Consequently the selected scalar boundary is read directly from the
fixed ten-edge collar word. -/
theorem terminalBoundaryCoordinate_eq_word :
    strand.terminalBoundaryCoordinate =
      crossFaceCoordinate (!firstHit.transfer.coordinate)
        (intrinsicCollarTerminalBoundaryWord
          collar.intrinsicCollarPortOverlapProfile
          (collar.intrinsicCollarCorrectionWord sourceEscape)
          (intrinsicCollarTerminalCoordinateOfRepresentative
            strand.terminalRepresentative)) := by
  exact congrArg (crossFaceCoordinate (!firstHit.transfer.coordinate))
    strand.terminalBoundaryWord_eq.symm

/-- The support edge on which the strand arrives at its first terminal. -/
def terminalSupportEdge : corner.complementarySupportGraph.edgeSet :=
  strand.path.edgeSubtypeSupport.getLast
    (edgeSubtypeSupport_ne_nil_of_length_pos
      strand.path strand.path_positive)

theorem terminalSupportEdge_mem_incident :
    strand.terminalSupportEdge ∈
      incidentEdgeFinset corner.complementarySupportGraph strand.finish.1 := by
  rw [terminalSupportEdge,
    edgeSubtypeSupport_getLast_eq_lastEdgeSet strand.path
      strand.path_positive]
  exact strand.path.lastEdgeSet_mem_incidentEdgeFinset
    (SimpleGraph.Walk.not_nil_iff_lt_length.mpr strand.path_positive)

/-- Subcubic Tait parity bounds the complementary support degree at the
terminal by two. -/
theorem terminalSupportDegree_le_two :
    (incidentEdgeFinset corner.complementarySupportGraph
      strand.finish.1).card ≤ 2 := by
  apply taitDiscrepancySupport_incidentCard_le_two
    (collar.sourceCommonColoring sourceEscape)
    collar.targetCommonColoring
    (collar.sourceCommonColoring_isTait sourceEscape)
    collar.targetCommonColoring_isTait
    (!firstHit.transfer.coordinate) strand.finish.1
  exact collar.commonCore_incidentEdgeFinset_card_le_three strand.finish.1

/-- Arrival along the strand makes the terminal support degree positive. -/
theorem terminalSupportDegree_pos :
    0 < (incidentEdgeFinset corner.complementarySupportGraph
      strand.finish.1).card := by
  exact Finset.card_pos.mpr
    ⟨strand.terminalSupportEdge, strand.terminalSupportEdge_mem_incident⟩

/-- Thus the first named terminal is either a support endpoint or a
degree-two passage. -/
theorem terminalSupportDegree_eq_one_or_two :
    (incidentEdgeFinset corner.complementarySupportGraph
        strand.finish.1).card = 1 ∨
      (incidentEdgeFinset corner.complementarySupportGraph
        strand.finish.1).card = 2 := by
  have hpositive := strand.terminalSupportDegree_pos
  have hupper := strand.terminalSupportDegree_le_two
  omega

/-- Degree one is equivalent to a nonzero complementary coordinate of the
canonical terminal boundary. -/
theorem terminalBoundaryCoordinate_ne_zero_iff_supportDegree_eq_one :
    strand.terminalBoundaryCoordinate ≠ 0 ↔
      (incidentEdgeFinset corner.complementarySupportGraph
        strand.finish.1).card = 1 := by
  unfold terminalBoundaryCoordinate
  change crossFaceCoordinate (!firstHit.transfer.coordinate)
      (vertexKirchhoffSum collar.commonCore
        (collar.commonDiscrepancy sourceEscape) strand.finish.1) ≠ 0 ↔ _
  rw [← scalarVertexKirchhoffSum_crossFaceCoordinate]
  rw [← scalarSupportGraph_degree_odd_iff]
  rw [← incidentEdgeFinset_card_eq_degree]
  change Odd ((incidentEdgeFinset corner.complementarySupportGraph
      strand.finish.1).card) ↔ _
  rcases strand.terminalSupportDegree_eq_one_or_two with hone | htwo
  · constructor
    · intro _hodd
      exact hone
    · intro _hone
      rw [hone]
      exact ⟨0, rfl⟩
  · constructor
    · rintro ⟨multiple, hmultiple⟩
      omega
    · intro hone
      omega

/-- Degree two is equivalently vanishing of that scalar boundary coordinate. -/
theorem terminalBoundaryCoordinate_eq_zero_iff_supportDegree_eq_two :
    strand.terminalBoundaryCoordinate = 0 ↔
      (incidentEdgeFinset corner.complementarySupportGraph
        strand.finish.1).card = 2 := by
  constructor
  · intro hzero
    rcases strand.terminalSupportDegree_eq_one_or_two with hone | htwo
    · exact False.elim
        ((strand.terminalBoundaryCoordinate_ne_zero_iff_supportDegree_eq_one
          ).2 hone hzero)
    · exact htwo
  · intro htwo
    by_contra hnonzero
    have hone :=
      (strand.terminalBoundaryCoordinate_ne_zero_iff_supportDegree_eq_one).1
        hnonzero
    omega

/-- In the degree-two case, a second supported edge continues through the
named terminal. -/
structure TerminalContinuation where
  edge : corner.complementarySupportGraph.edgeSet
  edge_mem : edge ∈ incidentEdgeFinset corner.complementarySupportGraph
    strand.finish.1
  edge_ne_terminal : edge ≠ strand.terminalSupportEdge

namespace TerminalContinuation

variable {strand : corner.FirstTerminalSupportStrand}
  (continuation : strand.TerminalContinuation)

/-- The arrival and continuation edges meet at the named terminal. -/
theorem adjacent :
    corner.complementarySupportGraph.lineGraph.Adj
      strand.terminalSupportEdge continuation.edge := by
  apply SimpleGraph.lineGraph_adj_iff_exists.mpr
  refine ⟨continuation.edge_ne_terminal.symm, strand.finish.1, ?_, ?_⟩
  · simpa only [incidentEdgeFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] using
      strand.terminalSupportEdge_mem_incident
  · simpa only [incidentEdgeFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] using continuation.edge_mem

end TerminalContinuation

/-- A continuation exists exactly in the degree-two terminal case. -/
theorem nonempty_terminalContinuation_iff_supportDegree_eq_two :
    Nonempty strand.TerminalContinuation ↔
      (incidentEdgeFinset corner.complementarySupportGraph
        strand.finish.1).card = 2 := by
  let incident := incidentEdgeFinset corner.complementarySupportGraph
    strand.finish.1
  constructor
  · rintro ⟨continuation⟩
    have hone : 1 < incident.card := by
      apply Finset.one_lt_card.mpr
      exact ⟨strand.terminalSupportEdge,
        strand.terminalSupportEdge_mem_incident,
        continuation.edge, continuation.edge_mem,
        continuation.edge_ne_terminal.symm⟩
    have hupper := strand.terminalSupportDegree_le_two
    change incident.card ≤ 2 at hupper
    change incident.card = 2
    omega
  · intro htwo
    have hone : 1 < incident.card := by
      change incident.card = 2 at htwo
      omega
    rcases Finset.one_lt_card.mp hone with
      ⟨first, hfirst, second, hsecond, hne⟩
    by_cases hfirstTerminal : first = strand.terminalSupportEdge
    · refine ⟨{
        edge := second
        edge_mem := hsecond
        edge_ne_terminal := ?_ }⟩
      intro hsecondTerminal
      exact hne (hfirstTerminal.trans hsecondTerminal.symm)
    · exact ⟨{
        edge := first
        edge_mem := hfirst
        edge_ne_terminal := hfirstTerminal }⟩

/-- Vanishing of the fixed collar boundary coordinate is exactly the
existence of a supported continuation through the terminal. -/
theorem terminalBoundaryCoordinate_eq_zero_iff_nonempty_terminalContinuation :
    strand.terminalBoundaryCoordinate = 0 ↔
      Nonempty strand.TerminalContinuation :=
  strand.terminalBoundaryCoordinate_eq_zero_iff_supportDegree_eq_two.trans
    strand.nonempty_terminalContinuation_iff_supportDegree_eq_two.symm

/-- The honest first-terminal alternative: either the fixed collar word has
a nonzero terminal boundary coordinate, or the support continues through a
second edge at that terminal. -/
theorem terminalBoundary_or_continuation :
    strand.terminalBoundaryCoordinate ≠ 0 ∨
      Nonempty strand.TerminalContinuation := by
  rcases strand.terminalSupportDegree_eq_one_or_two with hone | htwo
  · exact Or.inl
      ((strand.terminalBoundaryCoordinate_ne_zero_iff_supportDegree_eq_one
        ).2 hone)
  · exact Or.inr
      ((strand.nonempty_terminalContinuation_iff_supportDegree_eq_two).2
        htwo)

/-- The ambient common-core edge carrying the last state of the strand. -/
def terminalAmbientEdge : collar.commonCore.edgeSet :=
  strand.ambientPath.edgeSubtypeSupport.getLast
    (edgeSubtypeSupport_ne_nil_of_length_pos
      strand.ambientPath strand.ambientPath_positive)

theorem terminalAmbientEdge_mem_word :
    strand.terminalAmbientEdge ∈
      strand.ambientPath.edgeSubtypeSupport := by
  exact List.getLast_mem _

theorem terminalAmbientEdge_support :
    crossFaceCoordinate (!firstHit.transfer.coordinate)
      (collar.sourceCommonColoring sourceEscape strand.terminalAmbientEdge +
        collar.targetCommonColoring strand.terminalAmbientEdge) ≠ 0 :=
  strand.support strand.terminalAmbientEdge
    strand.terminalAmbientEdge_mem_word

theorem terminalAmbientEdge_mem_incident :
    strand.terminalAmbientEdge ∈
      incidentEdgeFinset collar.commonCore strand.finish.1 := by
  rw [terminalAmbientEdge,
    edgeSubtypeSupport_getLast_eq_lastEdgeSet strand.ambientPath
      strand.ambientPath_positive]
  exact strand.ambientPath.lastEdgeSet_mem_incidentEdgeFinset
    (SimpleGraph.Walk.not_nil_iff_lt_length.mpr
      strand.ambientPath_positive)

/-- The terminal ambient edge is precisely the image of the terminal edge
selected in the scalar-support subgraph. -/
theorem terminalAmbientEdge_val_eq_terminalSupportEdge_val :
    strand.terminalAmbientEdge.1 = strand.terminalSupportEdge.1 := by
  rw [terminalAmbientEdge, terminalSupportEdge,
    edgeSubtypeSupport_getLast_eq_lastEdgeSet strand.ambientPath
      strand.ambientPath_positive,
    edgeSubtypeSupport_getLast_eq_lastEdgeSet strand.path
      strand.path_positive]
  let hambientNil := SimpleGraph.Walk.not_nil_iff_lt_length.mpr
    strand.ambientPath_positive
  let hpathNil := SimpleGraph.Walk.not_nil_iff_lt_length.mpr
    strand.path_positive
  have hambientEdges : strand.ambientPath.edges ≠ [] :=
    SimpleGraph.Walk.edges_eq_nil.not.mpr hambientNil
  have hpathEdges : strand.path.edges ≠ [] :=
    SimpleGraph.Walk.edges_eq_nil.not.mpr hpathNil
  calc
    (strand.ambientPath.lastEdgeSet hambientNil).1 =
        strand.ambientPath.edges.getLast hambientEdges := by
      exact strand.ambientPath.mk_penultimate_end_eq_getLast_edges hambientNil
    _ = strand.path.edges.getLast hpathEdges := by
      simp only [ambientPath, SimpleGraph.Walk.edges_mapLe_eq_edges]
    _ = (strand.path.lastEdgeSet hpathNil).1 := by
      exact strand.path.mk_penultimate_end_eq_getLast_edges hpathNil |>.symm

/-- The actual terminal state, rather than only its abstract reachability
class in the transfer relation. -/
noncomputable def terminalState :
    ScalarDiscrepancyColorState (!firstHit.transfer.coordinate) :=
  strand.stateWord.getLast strand.stateWord_ne_nil

theorem terminalState_eq_stateOf :
    strand.terminalState =
      scalarDiscrepancyColorStateOf
        (collar.sourceCommonColoring sourceEscape)
        collar.targetCommonColoring
        (collar.sourceCommonColoring_isTait sourceEscape)
        collar.targetCommonColoring_isTait
        (!firstHit.transfer.coordinate)
        strand.terminalAmbientEdge
        strand.terminalAmbientEdge_support := by
  unfold terminalState stateWord terminalAmbientEdge
  unfold scalarDiscrepancyColorStateWord
  rw [List.getLast_pmap]

@[simp]
theorem terminalState_sourceColor :
    strand.terminalState.sourceColor =
      collar.sourceCommonColoring sourceEscape
        strand.terminalAmbientEdge := by
  rw [strand.terminalState_eq_stateOf]
  rfl

@[simp]
theorem terminalState_targetColor :
    strand.terminalState.targetColor =
      collar.targetCommonColoring strand.terminalAmbientEdge := by
  rw [strand.terminalState_eq_stateOf]
  rfl

namespace TerminalContinuation

variable {strand : corner.FirstTerminalSupportStrand}
  (continuation : strand.TerminalContinuation)

/-- Forgetting the scalar-support predicate gives the continuing edge in the
ambient common core. -/
def ambientEdge : collar.commonCore.edgeSet :=
  ⟨continuation.edge.1,
    (SimpleGraph.edgeSet_subset_edgeSet.mpr
      (scalarSupportGraph_le (fun edge =>
        crossFaceCoordinate (!firstHit.transfer.coordinate)
          (collar.commonDiscrepancy sourceEscape edge))))
      continuation.edge.2⟩

theorem ambientEdge_support :
    crossFaceCoordinate (!firstHit.transfer.coordinate)
      (collar.sourceCommonColoring sourceEscape continuation.ambientEdge +
        collar.targetCommonColoring continuation.ambientEdge) ≠ 0 := by
  change crossFaceCoordinate (!firstHit.transfer.coordinate)
    (collar.commonDiscrepancy sourceEscape continuation.ambientEdge) ≠ 0
  apply (ambientEdge_mem_scalarSupportGraph_edgeSet_iff
    (fun edge => crossFaceCoordinate (!firstHit.transfer.coordinate)
      (collar.commonDiscrepancy sourceEscape edge))
    continuation.ambientEdge).1
  exact continuation.edge.2

/-- The ambient terminal edge and ambient continuation edge are adjacent at
the same canonical terminal. -/
theorem ambient_adjacent :
    collar.commonCore.lineGraph.Adj
      strand.terminalAmbientEdge continuation.ambientEdge := by
  apply SimpleGraph.lineGraph_adj_iff_exists.mpr
  refine ⟨?_, strand.finish.1, ?_, ?_⟩
  · intro heq
    apply continuation.edge_ne_terminal
    apply Subtype.ext
    calc
      continuation.edge.1 = continuation.ambientEdge.1 := rfl
      _ = strand.terminalAmbientEdge.1 :=
        (congrArg Subtype.val heq).symm
      _ = strand.terminalSupportEdge.1 :=
        strand.terminalAmbientEdge_val_eq_terminalSupportEdge_val
  · simpa only [incidentEdgeFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] using
      strand.terminalAmbientEdge_mem_incident
  · simpa only [ambientEdge, incidentEdgeFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] using continuation.edge_mem

/-- The actual finite color state carried by the continuation edge. -/
noncomputable def state :
    ScalarDiscrepancyColorState (!firstHit.transfer.coordinate) :=
  scalarDiscrepancyColorStateOf
    (collar.sourceCommonColoring sourceEscape)
    collar.targetCommonColoring
    (collar.sourceCommonColoring_isTait sourceEscape)
    collar.targetCommonColoring_isTait
    (!firstHit.transfer.coordinate)
    continuation.ambientEdge continuation.ambientEdge_support

/-- A degree-two passage is a genuine next step of the same four-state
transfer system, not merely a graph-theoretic continuation. -/
theorem terminalState_transition :
    ScalarDiscrepancyColorTransition
      strand.terminalState continuation.state := by
  rw [strand.terminalState_eq_stateOf]
  simpa only [state] using
    (scalarDiscrepancyColorTransition_of_adjacent
      (collar.sourceCommonColoring sourceEscape)
      collar.targetCommonColoring
      (collar.sourceCommonColoring_isTait sourceEscape)
      collar.targetCommonColoring_isTait
      (!firstHit.transfer.coordinate)
      continuation.ambient_adjacent
      strand.terminalAmbientEdge_support
      continuation.ambientEdge_support)

@[simp]
theorem state_sourceColor :
    continuation.state.sourceColor =
      collar.sourceCommonColoring sourceEscape continuation.ambientEdge := rfl

@[simp]
theorem state_targetColor :
    continuation.state.targetColor =
      collar.targetCommonColoring continuation.ambientEdge := rfl

end TerminalContinuation

end FirstTerminalSupportStrand

end ComplementarySupportCorner
end TransverseCompanionChange
end FirstHitSingletonCompanionTransferPath
end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
