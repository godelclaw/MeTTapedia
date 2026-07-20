import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionSupportComponent

/-! Finite color transfer on complementary scalar-support strands. -/

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

/-- A walk in a scalar support maps to an ambient walk whose every edge
retains nonzero scalar weight. -/
theorem scalarSupportWalk_support
    [Fintype W] [DecidableRel H.Adj]
    (chain : H.edgeSet → F2) {start finish : W}
    (path : (scalarSupportGraph chain).Walk start finish) :
    ∀ edge ∈ (path.mapLe
      (scalarSupportGraph_le chain)).edgeSubtypeSupport,
      chain edge ≠ 0 := by
  classical
  intro edge hedge
  have hedgeAmbient : (edge : Sym2 W) ∈
      (path.mapLe (scalarSupportGraph_le chain)).edges := by
    rw [← SimpleGraph.Walk.edgeSubtypeSupport_map_val]
    exact List.mem_map.mpr ⟨edge, hedge, rfl⟩
  have hedgePath : (edge : Sym2 W) ∈ path.edges := by
    simpa only [SimpleGraph.Walk.edges_mapLe_eq_edges] using hedgeAmbient
  have hedgeSupport : (edge : Sym2 W) ∈
      (scalarSupportGraph chain).edgeSet :=
    path.edges_subset_edgeSet hedgePath
  exact (ambientEdge_mem_scalarSupportGraph_edgeSet_iff chain edge).1
    hedgeSupport

/-- In the edge word of a simple closed walk, the last and first edges are
adjacent vertices of the line graph. -/
theorem isCycle_edgeSubtypeSupport_closingAdj
    {start : W} {cycle : H.Walk start start} (hcycle : cycle.IsCycle) :
    H.lineGraph.Adj
      (cycle.edgeSubtypeSupport.getLast (by
        apply List.length_pos_iff.mp
        rw [cycle.edgeSubtypeSupport_length]
        exact lt_of_lt_of_le (by omega) hcycle.three_le_length))
      (cycle.edgeSubtypeSupport.head (by
        apply List.length_pos_iff.mp
        rw [cycle.edgeSubtypeSupport_length]
        exact lt_of_lt_of_le (by omega) hcycle.three_le_length)) := by
  let hpositive : 0 < cycle.length :=
    lt_of_lt_of_le (by omega) hcycle.three_le_length
  let hword : cycle.edgeSubtypeSupport ≠ [] := by
    intro hnil
    have hlength := congrArg List.length hnil
    rw [cycle.edgeSubtypeSupport_length] at hlength
    exact (Nat.ne_of_gt hpositive) hlength
  let firstEdge := cycle.edgeSubtypeSupport.head hword
  let lastEdge := cycle.edgeSubtypeSupport.getLast hword
  have hedges : cycle.edges ≠ [] := by
    exact SimpleGraph.Walk.edges_eq_nil.not.mpr hcycle.not_nil
  have hfirstValue : firstEdge.1 = s(start, cycle.snd) := by
    calc
      firstEdge.1 = cycle.edges[0]'(by simpa using hpositive) :=
        cycle.edgeSubtypeSupport_head_val hpositive
      _ = cycle.edges.head hedges :=
        (List.head_eq_getElem_zero hedges).symm
      _ = s(start, cycle.snd) :=
        cycle.head_edges_eq_mk_start_snd hedges
  have hlastValue : lastEdge.1 = s(cycle.penultimate, start) := by
    have hmapped :
        cycle.edgeSubtypeSupport.map Subtype.val ≠ [] := by
      intro hnil
      exact hword (List.map_eq_nil_iff.mp hnil)
    calc
      lastEdge.1 =
          (cycle.edgeSubtypeSupport.map Subtype.val).getLast hmapped := by
        exact (List.getLast_map hmapped).symm
      _ = cycle.edges.getLast hedges := by
        simp only [cycle.edgeSubtypeSupport_map_val]
      _ = s(cycle.penultimate, start) :=
        cycle.getLast_edges_eq_mk_penultimate_end hedges
  have hne : lastEdge ≠ firstEdge := by
    intro heq
    apply hcycle.snd_ne_penultimate
    apply (Sym2.mkEmbedding start).injective
    calc
      s(start, cycle.snd) = firstEdge.1 := hfirstValue.symm
      _ = lastEdge.1 := (congrArg Subtype.val heq).symm
      _ = s(cycle.penultimate, start) := hlastValue
      _ = s(start, cycle.penultimate) := Sym2.eq_swap
  apply SimpleGraph.lineGraph_adj_iff_exists.mpr
  refine ⟨hne, start, ?_, ?_⟩
  · rw [hlastValue]
    exact Sym2.mem_mk_right _ _
  · rw [hfirstValue]
    exact Sym2.mem_mk_left _ _

/-- The finite state word read around a scalar-support cycle includes the
closing transition from its last edge back to its first edge. -/
theorem scalarDiscrepancyColorStateWord_closingTransition
    (firstColoring secondColoring : H.EdgeColoring Color)
    (hfirstTait : IsTaitEdgeColoring H firstColoring)
    (hsecondTait : IsTaitEdgeColoring H secondColoring)
    (coordinate : Bool) {start : W} {cycle : H.Walk start start}
    (hcycle : cycle.IsCycle)
    (hsupport : ∀ edge ∈ cycle.edgeSubtypeSupport,
      crossFaceCoordinate coordinate
        (firstColoring edge + secondColoring edge) ≠ 0) :
    let word := scalarDiscrepancyColorStateWord
      firstColoring secondColoring hfirstTait hsecondTait
        coordinate cycle hsupport
    ScalarDiscrepancyColorTransition
      (word.getLast (by
        apply List.length_pos_iff.mp
        rw [scalarDiscrepancyColorStateWord_length]
        exact lt_of_lt_of_le (by omega) hcycle.three_le_length))
      (word.head (by
        apply List.length_pos_iff.mp
        rw [scalarDiscrepancyColorStateWord_length]
        exact lt_of_lt_of_le (by omega) hcycle.three_le_length)) := by
  dsimp only
  let hpositive : 0 < cycle.length :=
    lt_of_lt_of_le (by omega) hcycle.three_le_length
  let hedgeWord : cycle.edgeSubtypeSupport ≠ [] := by
    intro hnil
    have hlength := congrArg List.length hnil
    rw [cycle.edgeSubtypeSupport_length] at hlength
    exact (Nat.ne_of_gt hpositive) hlength
  let firstEdge := cycle.edgeSubtypeSupport.head hedgeWord
  let lastEdge := cycle.edgeSubtypeSupport.getLast hedgeWord
  have hfirstSupport : crossFaceCoordinate coordinate
      (firstColoring firstEdge + secondColoring firstEdge) ≠ 0 :=
    hsupport firstEdge (List.head_mem hedgeWord)
  have hlastSupport : crossFaceCoordinate coordinate
      (firstColoring lastEdge + secondColoring lastEdge) ≠ 0 :=
    hsupport lastEdge (List.getLast_mem hedgeWord)
  have htransition : ScalarDiscrepancyColorTransition
      (scalarDiscrepancyColorStateOf firstColoring secondColoring
        hfirstTait hsecondTait coordinate lastEdge hlastSupport)
      (scalarDiscrepancyColorStateOf firstColoring secondColoring
        hfirstTait hsecondTait coordinate firstEdge hfirstSupport) := by
    apply scalarDiscrepancyColorTransition_of_adjacent
      firstColoring secondColoring hfirstTait hsecondTait coordinate
    exact isCycle_edgeSubtypeSupport_closingAdj hcycle
  unfold scalarDiscrepancyColorStateWord
  rw [List.getLast_pmap, List.head_pmap]
  exact htransition

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

/-- The complementary-coordinate support graph selected at a transverse
companion change. -/
abbrev complementarySupportGraph
    (_corner : change.ComplementarySupportCorner) :
    SimpleGraph collar.commonCoreVertex :=
  collar.coordinateDiscrepancySupportGraph sourceEscape
    (!firstHit.transfer.coordinate)

/-- The common endpoint of the incoming and transverse support edges. -/
abbrev complementarySupportJunction
    (corner : change.ComplementarySupportCorner) :
    collar.commonCoreVertex :=
  SimpleGraph.lineGraphCommonVertex corner.incoming_transverse_adj

/-- A complementary support strand directed from its transverse launch to
the first later named source or target port. -/
structure FirstTerminalSupportStrand
    (corner : change.ComplementarySupportCorner) where
  finish : collar.commonPortVertexFinset
  finish_ne_junction : finish.1 ≠ corner.complementarySupportJunction
  path : corner.complementarySupportGraph.Walk
    corner.complementarySupportJunction finish.1
  path_isPath : path.IsPath
  path_positive : 0 < path.length
  internal_not_commonPort :
    ∀ position : Nat, 0 < position → position < path.length →
      path.getVert position ∉ collar.commonPortVertexFinset
  incoming_avoided : corner.incomingSupportEdge.1 ∉ path.edges
  transverse_mem : (transverseSupportEdge change).1 ∈ path.edges

/-- A complementary support strand that returns to its launch before
reaching a distinct named port. -/
structure ClosedSupportStrand
    (corner : change.ComplementarySupportCorner) where
  cycle : corner.complementarySupportGraph.Walk
    corner.complementarySupportJunction corner.complementarySupportJunction
  cycle_isCycle : cycle.IsCycle
  incoming_mem : corner.incomingSupportEdge.1 ∈ cycle.edges
  transverse_mem : (transverseSupportEdge change).1 ∈ cycle.edges

/-- The directional component theorem constructs either a first-terminal
strand or a closed strand, with no additional coloring hypothesis. -/
theorem firstTerminalSupportStrand_or_closedSupportStrand
    (corner : change.ComplementarySupportCorner) :
    Nonempty corner.FirstTerminalSupportStrand ∨
      Nonempty corner.ClosedSupportStrand := by
  rcases corner.exists_firstTerminalPath_or_supportCycle with
    hterminal | hcycle
  · rcases hterminal with
      ⟨finish, hfinishTerminal, hfinishNe, path, hpath,
        hpositive, hinternal, hincoming, htransverse⟩
    exact Or.inl ⟨{
      finish := ⟨finish, hfinishTerminal⟩
      finish_ne_junction := hfinishNe
      path := path
      path_isPath := hpath
      path_positive := hpositive
      internal_not_commonPort := hinternal
      incoming_avoided := hincoming
      transverse_mem := htransverse }⟩
  · rcases hcycle with
      ⟨supportCycle, hsupportCycle, hincoming, htransverse⟩
    exact Or.inr ⟨{
      cycle := supportCycle
      cycle_isCycle := hsupportCycle
      incoming_mem := hincoming
      transverse_mem := htransverse }⟩

namespace FirstTerminalSupportStrand

variable {corner : change.ComplementarySupportCorner}
  (strand : corner.FirstTerminalSupportStrand)

/-- The same strand after forgetting the scalar-support subgraph. -/
def ambientPath : collar.commonCore.Walk
    corner.complementarySupportJunction strand.finish.1 :=
  strand.path.mapLe (scalarSupportGraph_le (fun edge =>
    crossFaceCoordinate (!firstHit.transfer.coordinate)
      (collar.commonDiscrepancy sourceEscape edge)))

@[simp]
theorem ambientPath_length :
    strand.ambientPath.length = strand.path.length := by
  calc
    strand.ambientPath.length = strand.ambientPath.edges.length :=
      strand.ambientPath.length_edges.symm
    _ = strand.path.edges.length := by
      exact congrArg List.length
        (SimpleGraph.Walk.edges_mapLe_eq_edges _ _)
    _ = strand.path.length := strand.path.length_edges

theorem ambientPath_isPath : strand.ambientPath.IsPath := by
  exact strand.path_isPath.mapLe (scalarSupportGraph_le (fun edge =>
    crossFaceCoordinate (!firstHit.transfer.coordinate)
      (collar.commonDiscrepancy sourceEscape edge)))

theorem ambientPath_positive : 0 < strand.ambientPath.length := by
  rw [strand.ambientPath_length]
  exact strand.path_positive

/-- Every ambient edge of the strand retains nonzero discrepancy in the
complementary coordinate. -/
theorem support : ∀ edge ∈ strand.ambientPath.edgeSubtypeSupport,
    crossFaceCoordinate (!firstHit.transfer.coordinate)
      (collar.sourceCommonColoring sourceEscape edge +
        collar.targetCommonColoring edge) ≠ 0 := by
  simpa only [ambientPath, commonDiscrepancy_apply] using
    (scalarSupportWalk_support (fun edge =>
      crossFaceCoordinate (!firstHit.transfer.coordinate)
        (collar.commonDiscrepancy sourceEscape edge)) strand.path)

/-- The canonical four-state word read from the complementary strand. -/
noncomputable def stateWord :
    List (ScalarDiscrepancyColorState
      (!firstHit.transfer.coordinate)) :=
  scalarDiscrepancyColorStateWord
    (collar.sourceCommonColoring sourceEscape)
    collar.targetCommonColoring
    (collar.sourceCommonColoring_isTait sourceEscape)
    collar.targetCommonColoring_isTait
    (!firstHit.transfer.coordinate) strand.ambientPath strand.support

@[simp]
theorem stateWord_length :
    strand.stateWord.length = strand.path.length := by
  rw [stateWord,
    scalarDiscrepancyColorStateWord_length,
    strand.ambientPath_length]

theorem stateWord_ne_nil : strand.stateWord ≠ [] := by
  apply List.length_pos_iff.mp
  rw [strand.stateWord_length]
  exact strand.path_positive

/-- The first-terminal strand is an exact finite-state transfer between its
canonical endpoint edge states. -/
theorem exactTransfer :
    ExactRelationalTransfer ScalarDiscrepancyColorTransition
      (strand.path.length - 1)
      (strand.stateWord.head strand.stateWord_ne_nil)
      (strand.stateWord.getLast strand.stateWord_ne_nil) := by
  simpa only [stateWord, strand.ambientPath_length] using
    (scalarDiscrepancyColorStateWord_exactTransfer
      (collar.sourceCommonColoring sourceEscape)
      collar.targetCommonColoring
      (collar.sourceCommonColoring_isTait sourceEscape)
      collar.targetCommonColoring_isTait
      (!firstHit.transfer.coordinate)
      strand.ambientPath_isPath.isTrail strand.ambientPath_positive
      strand.support)

end FirstTerminalSupportStrand

namespace ClosedSupportStrand

variable {corner : change.ComplementarySupportCorner}
  (strand : corner.ClosedSupportStrand)

/-- The same closed strand after forgetting the scalar-support subgraph. -/
def ambientCycle : collar.commonCore.Walk
    corner.complementarySupportJunction corner.complementarySupportJunction :=
  strand.cycle.mapLe (scalarSupportGraph_le (fun edge =>
    crossFaceCoordinate (!firstHit.transfer.coordinate)
      (collar.commonDiscrepancy sourceEscape edge)))

@[simp]
theorem ambientCycle_length :
    strand.ambientCycle.length = strand.cycle.length := by
  calc
    strand.ambientCycle.length = strand.ambientCycle.edges.length :=
      strand.ambientCycle.length_edges.symm
    _ = strand.cycle.edges.length := by
      exact congrArg List.length
        (SimpleGraph.Walk.edges_mapLe_eq_edges _ _)
    _ = strand.cycle.length := strand.cycle.length_edges

theorem ambientCycle_isCycle : strand.ambientCycle.IsCycle := by
  exact strand.cycle_isCycle.mapLe (scalarSupportGraph_le (fun edge =>
    crossFaceCoordinate (!firstHit.transfer.coordinate)
      (collar.commonDiscrepancy sourceEscape edge)))

theorem ambientCycle_positive : 0 < strand.ambientCycle.length := by
  exact lt_of_lt_of_le (by omega) strand.ambientCycle_isCycle.three_le_length

/-- Every ambient edge of the closed strand retains nonzero discrepancy in
the complementary coordinate. -/
theorem support : ∀ edge ∈ strand.ambientCycle.edgeSubtypeSupport,
    crossFaceCoordinate (!firstHit.transfer.coordinate)
      (collar.sourceCommonColoring sourceEscape edge +
        collar.targetCommonColoring edge) ≠ 0 := by
  simpa only [ambientCycle, commonDiscrepancy_apply] using
    (scalarSupportWalk_support (fun edge =>
      crossFaceCoordinate (!firstHit.transfer.coordinate)
        (collar.commonDiscrepancy sourceEscape edge)) strand.cycle)

/-- The canonical four-state word obtained by cutting the closed strand at
its complementary-support junction. -/
noncomputable def stateWord :
    List (ScalarDiscrepancyColorState
      (!firstHit.transfer.coordinate)) :=
  scalarDiscrepancyColorStateWord
    (collar.sourceCommonColoring sourceEscape)
    collar.targetCommonColoring
    (collar.sourceCommonColoring_isTait sourceEscape)
    collar.targetCommonColoring_isTait
    (!firstHit.transfer.coordinate) strand.ambientCycle strand.support

@[simp]
theorem stateWord_length :
    strand.stateWord.length = strand.cycle.length := by
  rw [stateWord,
    scalarDiscrepancyColorStateWord_length,
    strand.ambientCycle_length]

theorem stateWord_ne_nil : strand.stateWord ≠ [] := by
  apply List.length_pos_iff.mp
  rw [strand.stateWord_length]
  exact lt_of_lt_of_le (by omega)
    strand.cycle_isCycle.three_le_length

/-- Cutting a closed strand at its root gives an exact transfer from its
first edge state to its last edge state. -/
theorem linearizedExactTransfer :
    ExactRelationalTransfer ScalarDiscrepancyColorTransition
      (strand.cycle.length - 1)
      (strand.stateWord.head strand.stateWord_ne_nil)
      (strand.stateWord.getLast strand.stateWord_ne_nil) := by
  simpa only [stateWord, strand.ambientCycle_length] using
    (scalarDiscrepancyColorStateWord_exactTransfer
      (collar.sourceCommonColoring sourceEscape)
      collar.targetCommonColoring
      (collar.sourceCommonColoring_isTait sourceEscape)
      collar.targetCommonColoring_isTait
      (!firstHit.transfer.coordinate)
      strand.ambientCycle_isCycle.isTrail strand.ambientCycle_positive
      strand.support)

/-- The last edge state of the cut cycle transitions back to its first edge
state at the common root. -/
theorem closingTransition :
    ScalarDiscrepancyColorTransition
      (strand.stateWord.getLast strand.stateWord_ne_nil)
      (strand.stateWord.head strand.stateWord_ne_nil) := by
  simpa only [stateWord] using
    (scalarDiscrepancyColorStateWord_closingTransition
      (collar.sourceCommonColoring sourceEscape)
      collar.targetCommonColoring
      (collar.sourceCommonColoring_isTait sourceEscape)
      collar.targetCommonColoring_isTait
      (!firstHit.transfer.coordinate)
      strand.ambientCycle_isCycle strand.support)

/-- A closed complementary strand is a genuine positive-period return in
the four-state transfer system.  Its exact period is its number of primal
support edges. -/
theorem exactReturn :
    ExactRelationalTransfer ScalarDiscrepancyColorTransition
      strand.cycle.length
      (strand.stateWord.head strand.stateWord_ne_nil)
      (strand.stateWord.head strand.stateWord_ne_nil) := by
  have hclosingStep :
      ExactRelationalTransfer ScalarDiscrepancyColorTransition 1
        (strand.stateWord.getLast strand.stateWord_ne_nil)
        (strand.stateWord.head strand.stateWord_ne_nil) := by
    simpa using ExactRelationalTransfer.succ strand.closingTransition
      (ExactRelationalTransfer.zero
        (oneStep := ScalarDiscrepancyColorTransition)
        (strand.stateWord.head strand.stateWord_ne_nil))
  have hreturn := strand.linearizedExactTransfer.comp hclosingStep
  have hpositive : 0 < strand.cycle.length :=
    lt_of_lt_of_le (by omega) strand.cycle_isCycle.three_le_length
  have hlength : strand.cycle.length - 1 + 1 =
      strand.cycle.length := by omega
  rw [hlength] at hreturn
  exact hreturn

end ClosedSupportStrand

end ComplementarySupportCorner

end TransverseCompanionChange

end FirstHitSingletonCompanionTransferPath

end IntrinsicShortTargetEscapeCollar

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
