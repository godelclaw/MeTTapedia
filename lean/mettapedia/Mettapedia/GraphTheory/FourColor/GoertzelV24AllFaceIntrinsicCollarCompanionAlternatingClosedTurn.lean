import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAlternatingContinuation

/-! Second signed turns on coordinate-generic closed support routes. -/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
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

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

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

namespace IntrinsicShortTargetEscapeCollar

variable {cycle :
    CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle rebaseCircuit}
  {targetEdge : G.edgeSet}
  {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
    graphData minimal baseData}
  {collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge}
  {sourceEscape : sourceNormal.KempeOrbitAdjacentEscape}
  {coordinate : Bool}
  {turn : collar.ScalarCompanionTurn sourceEscape coordinate}

namespace ScalarCompanionTurn.ComplementarySupportCorner

variable (corner : turn.ComplementarySupportCorner)

/-- Forget a scalar-support edge back to its common-core edge. -/
def supportEdgeAmbientEdge
    (edge : corner.complementarySupportGraph.edgeSet) :
    collar.commonCore.edgeSet :=
  ⟨edge.1,
    (SimpleGraph.edgeSet_subset_edgeSet.mpr
      (scalarSupportGraph_le (fun current =>
        crossFaceCoordinate (!coordinate)
          (collar.commonDiscrepancy sourceEscape current)))) edge.2⟩

@[simp]
theorem supportEdgeAmbientEdge_val
    (edge : corner.complementarySupportGraph.edgeSet) :
    (corner.supportEdgeAmbientEdge edge).1 = edge.1 := rfl

/-- Every forgotten support edge retains nonzero discrepancy. -/
theorem supportEdgeAmbientEdge_support
    (edge : corner.complementarySupportGraph.edgeSet) :
    crossFaceCoordinate (!coordinate)
      (collar.commonDiscrepancy sourceEscape
        (corner.supportEdgeAmbientEdge edge)) ≠ 0 := by
  apply (ambientEdge_mem_scalarSupportGraph_edgeSet_iff
    (fun current => crossFaceCoordinate (!coordinate)
      (collar.commonDiscrepancy sourceEscape current))
    (corner.supportEdgeAmbientEdge edge)).1
  exact edge.2

/-- Actual color state carried by a generic support-graph edge. -/
noncomputable def supportEdgeColorState
    (edge : corner.complementarySupportGraph.edgeSet) :
    ScalarDiscrepancyColorState (!coordinate) :=
  collar.discrepancyColorState sourceEscape (!coordinate)
    (corner.supportEdgeAmbientEdge edge)
    (corner.supportEdgeAmbientEdge_support edge)

@[simp]
theorem supportEdgeColorState_sourceColor
    (edge : corner.complementarySupportGraph.edgeSet) :
    (corner.supportEdgeColorState edge).sourceColor =
      collar.sourceCommonColoring sourceEscape
        (corner.supportEdgeAmbientEdge edge) := rfl

@[simp]
theorem supportEdgeColorState_targetColor
    (edge : corner.complementarySupportGraph.edgeSet) :
    (corner.supportEdgeColorState edge).targetColor =
      collar.targetCommonColoring
        (corner.supportEdgeAmbientEdge edge) := rfl

/-- State at the old launch edge is the recoordinated incoming state. -/
theorem supportEdgeColorState_incoming :
    corner.supportEdgeColorState corner.incomingSupportEdge =
      corner.incomingComplementState := by
  apply Subtype.ext
  rfl

/-- State at the transverse launch edge is its complementary state. -/
theorem supportEdgeColorState_transverse :
    corner.supportEdgeColorState corner.transverseSupportEdge =
      thirdComplementState (turn := turn) := by
  apply Subtype.ext
  rfl

/-- Support adjacency remains adjacency after forgetting the predicate. -/
theorem supportEdgeAmbientEdge_lineGraph_adj
    {first second : corner.complementarySupportGraph.edgeSet}
    (hadjacent : corner.complementarySupportGraph.lineGraph.Adj
      first second) :
    collar.commonCore.lineGraph.Adj
      (corner.supportEdgeAmbientEdge first)
      (corner.supportEdgeAmbientEdge second) := by
  rcases SimpleGraph.lineGraph_adj_iff_exists.mp hadjacent with
    ⟨hne, vertex, hfirst, hsecond⟩
  apply SimpleGraph.lineGraph_adj_iff_exists.mpr
  refine ⟨?_, vertex, ?_, ?_⟩
  · intro heq
    apply hne
    apply Subtype.ext
    have hval :
        (corner.supportEdgeAmbientEdge first).1 =
          (corner.supportEdgeAmbientEdge second).1 :=
      congrArg (fun edge : collar.commonCore.edgeSet => edge.1) heq
    simpa only [supportEdgeAmbientEdge_val] using hval
  · simpa only [supportEdgeAmbientEdge_val] using hfirst
  · simpa only [supportEdgeAmbientEdge_val] using hsecond

/-- Away from named ports, two adjacent support edges have a third
common-core edge at their cubic junction. -/
theorem exists_thirdEdge_of_supportEdge_adjacent_of_not_ports
    (first second : corner.complementarySupportGraph.edgeSet)
    (hadjacent : corner.complementarySupportGraph.lineGraph.Adj first second)
    (hsource : ∀ port : Fin 4,
      SimpleGraph.lineGraphCommonVertex
          (corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent) ≠
        collar.sourcePortInCommonCore port)
    (htarget : ∀ port : Fin 4,
      SimpleGraph.lineGraphCommonVertex
          (corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent) ≠
        collar.targetPortInCommonCore port) :
    ∃ thirdEdge : collar.commonCore.edgeSet,
      collar.commonCore.lineGraph.Adj
          (corner.supportEdgeAmbientEdge first) thirdEdge ∧
        collar.commonCore.lineGraph.Adj
          (corner.supportEdgeAmbientEdge second) thirdEdge := by
  let ambientAdj := corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent
  let vertex := SimpleGraph.lineGraphCommonVertex ambientAdj
  have hcard : (incidentEdgeFinset collar.commonCore vertex).card = 3 :=
    collar.card_incidentEdgeFinset_commonCore_eq_three_of_not_ports
      vertex hsource htarget
  have hfirstSecondNe : corner.supportEdgeAmbientEdge first ≠
      corner.supportEdgeAmbientEdge second := ambientAdj.ne
  have hnotSubset :
      ¬ incidentEdgeFinset collar.commonCore vertex ⊆
        ({corner.supportEdgeAmbientEdge first,
          corner.supportEdgeAmbientEdge second} :
          Finset collar.commonCore.edgeSet) := by
    intro hsubset
    have hcardLe := Finset.card_le_card hsubset
    have hpairCard :
        ({corner.supportEdgeAmbientEdge first,
          corner.supportEdgeAmbientEdge second} :
          Finset collar.commonCore.edgeSet).card = 2 :=
      Finset.card_pair hfirstSecondNe
    rw [hcard, hpairCard] at hcardLe
    omega
  rcases Finset.not_subset.mp hnotSubset with
    ⟨thirdEdge, hthirdIncident, hthirdNotPair⟩
  have hthirdVertex : vertex ∈ (thirdEdge.1 : Sym2 collar.commonCoreVertex) := by
    simpa only [incidentEdgeFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] using hthirdIncident
  have hthirdNeFirst : thirdEdge ≠ corner.supportEdgeAmbientEdge first := by
    intro heq
    apply hthirdNotPair
    rw [heq]
    exact Finset.mem_insert_self _ _
  have hthirdNeSecond : thirdEdge ≠ corner.supportEdgeAmbientEdge second := by
    intro heq
    apply hthirdNotPair
    rw [heq]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  exact ⟨thirdEdge,
    collar.commonCore.lineGraph_adj_of_edgeSet_common_vertex
      hthirdNeFirst.symm
      (SimpleGraph.lineGraphCommonVertex_mem_left ambientAdj)
      hthirdVertex,
    collar.commonCore.lineGraph_adj_of_edgeSet_common_vertex
      hthirdNeSecond.symm
      (SimpleGraph.lineGraphCommonVertex_mem_right ambientAdj)
      hthirdVertex⟩

/-- A companion change emits the active coordinate's distinguished color
on the third common-core edge. -/
theorem changedSupportEdges_emit_on_thirdEdge
    (first second : corner.complementarySupportGraph.edgeSet)
    (hadjacent : corner.complementarySupportGraph.lineGraph.Adj first second)
    (hcompanion :
      (corner.supportEdgeColorState first).companionColor ≠
        (corner.supportEdgeColorState second).companionColor)
    {thirdEdge : collar.commonCore.edgeSet}
    (hfirstThird : collar.commonCore.lineGraph.Adj
      (corner.supportEdgeAmbientEdge first) thirdEdge)
    (hsecondThird : collar.commonCore.lineGraph.Adj
      (corner.supportEdgeAmbientEdge second) thirdEdge) :
    collar.commonDiscrepancy sourceEscape thirdEdge =
      crossFaceZeroColor (!coordinate) := by
  apply thirdEdge_discrepancy_eq_zeroColor_of_companionColor_ne
    (collar.sourceCommonColoring sourceEscape)
    collar.targetCommonColoring
    (collar.sourceCommonColoring_isTait sourceEscape)
    collar.targetCommonColoring_isTait
    (!coordinate)
    (corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent)
    hfirstThird hsecondThird
    (corner.supportEdgeAmbientEdge_support first)
    (corner.supportEdgeAmbientEdge_support second)
  simpa only [supportEdgeColorState, discrepancyColorState] using hcompanion

/-- Every companion-changing adjacency is a named port or emits a
transverse edge supported in the opposite coordinate. -/
theorem changedSupportEdges_boundaryPort_or_transverseEmission
    (first second : corner.complementarySupportGraph.edgeSet)
    (hadjacent : corner.complementarySupportGraph.lineGraph.Adj first second)
    (hcompanion :
      (corner.supportEdgeColorState first).companionColor ≠
        (corner.supportEdgeColorState second).companionColor) :
    (∃ sourcePort : Fin 4,
        SimpleGraph.lineGraphCommonVertex
            (corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent) =
          collar.sourcePortInCommonCore sourcePort) ∨
      (∃ targetPort : Fin 4,
        SimpleGraph.lineGraphCommonVertex
            (corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent) =
          collar.targetPortInCommonCore targetPort) ∨
      ∃ thirdEdge : collar.commonCore.edgeSet,
        collar.commonCore.lineGraph.Adj
            (corner.supportEdgeAmbientEdge first) thirdEdge ∧
          collar.commonCore.lineGraph.Adj
            (corner.supportEdgeAmbientEdge second) thirdEdge ∧
          collar.commonDiscrepancy sourceEscape thirdEdge =
            crossFaceZeroColor (!coordinate) ∧
          crossFaceCoordinate coordinate
            (collar.commonDiscrepancy sourceEscape thirdEdge) ≠ 0 := by
  let ambientAdj := corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent
  by_cases hsource : ∃ sourcePort : Fin 4,
      SimpleGraph.lineGraphCommonVertex ambientAdj =
        collar.sourcePortInCommonCore sourcePort
  · exact Or.inl hsource
  · by_cases htarget : ∃ targetPort : Fin 4,
        SimpleGraph.lineGraphCommonVertex ambientAdj =
          collar.targetPortInCommonCore targetPort
    · exact Or.inr (Or.inl htarget)
    · have hsourceAvoid : ∀ sourcePort : Fin 4,
          SimpleGraph.lineGraphCommonVertex ambientAdj ≠
            collar.sourcePortInCommonCore sourcePort := by
        intro sourcePort heq
        exact hsource ⟨sourcePort, heq⟩
      have htargetAvoid : ∀ targetPort : Fin 4,
          SimpleGraph.lineGraphCommonVertex ambientAdj ≠
            collar.targetPortInCommonCore targetPort := by
        intro targetPort heq
        exact htarget ⟨targetPort, heq⟩
      rcases corner.exists_thirdEdge_of_supportEdge_adjacent_of_not_ports
          first second hadjacent hsourceAvoid htargetAvoid with
        ⟨thirdEdge, hfirstThird, hsecondThird⟩
      have hdiscrepancy := corner.changedSupportEdges_emit_on_thirdEdge
        first second hadjacent hcompanion hfirstThird hsecondThird
      refine Or.inr (Or.inr ⟨thirdEdge, hfirstThird, hsecondThird,
        hdiscrepancy, ?_⟩)
      rw [hdiscrepancy]
      simpa using
        crossFaceCoordinate_complement_zeroColor_ne_zero (!coordinate)

namespace ClosedSupportStrand

variable {corner : turn.ComplementarySupportCorner}
  (strand : corner.ClosedSupportStrand)

theorem cycleEdgeWord_ne_nil : strand.cycle.edgeSubtypeSupport ≠ [] :=
  edgeSubtypeSupport_ne_nil_of_length_pos strand.cycle
    (lt_of_lt_of_le (by omega) strand.cycle_isCycle.three_le_length)

/-- First edge at the rooted cut of the support cycle. -/
def rootFirstSupportEdge : corner.complementarySupportGraph.edgeSet :=
  strand.cycle.edgeSubtypeSupport.head strand.cycleEdgeWord_ne_nil

/-- Last edge at the rooted cut of the support cycle. -/
def rootLastSupportEdge : corner.complementarySupportGraph.edgeSet :=
  strand.cycle.edgeSubtypeSupport.getLast strand.cycleEdgeWord_ne_nil

theorem rootFirstSupportEdge_mem_incident :
    strand.rootFirstSupportEdge ∈
      incidentEdgeFinset corner.complementarySupportGraph
        corner.complementarySupportJunction := by
  have hpositive : 0 < strand.cycle.length :=
    lt_of_lt_of_le (by omega) strand.cycle_isCycle.three_le_length
  have hedges : strand.cycle.edges ≠ [] :=
    SimpleGraph.Walk.edges_eq_nil.not.mpr strand.cycle_isCycle.not_nil
  have hvalue : strand.rootFirstSupportEdge.1 =
      s(corner.complementarySupportJunction, strand.cycle.snd) := by
    calc
      strand.rootFirstSupportEdge.1 =
          strand.cycle.edges[0]'(by simpa using hpositive) :=
        strand.cycle.edgeSubtypeSupport_head_val hpositive
      _ = strand.cycle.edges.head hedges :=
        (List.head_eq_getElem_zero hedges).symm
      _ = s(corner.complementarySupportJunction, strand.cycle.snd) :=
        strand.cycle.head_edges_eq_mk_start_snd hedges
  rw [incidentEdgeFinset]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hvalue]
  exact Sym2.mem_mk_left _ _

theorem rootLastSupportEdge_mem_incident :
    strand.rootLastSupportEdge ∈
      incidentEdgeFinset corner.complementarySupportGraph
        corner.complementarySupportJunction := by
  rw [rootLastSupportEdge,
    edgeSubtypeSupport_getLast_eq_lastEdgeSet strand.cycle
      (lt_of_lt_of_le (by omega)
        strand.cycle_isCycle.three_le_length)]
  exact strand.cycle.lastEdgeSet_mem_incidentEdgeFinset
    strand.cycle_isCycle.not_nil

theorem rootFirstSupportEdge_ne_rootLastSupportEdge :
    strand.rootFirstSupportEdge ≠ strand.rootLastSupportEdge := by
  exact (isCycle_edgeSubtypeSupport_closingAdj
    strand.cycle_isCycle).ne.symm

/-- Root cycle edges are exactly the launch pair, up to order. -/
theorem rootEdges_pair_eq_launchEdges :
    ({strand.rootFirstSupportEdge, strand.rootLastSupportEdge} :
        Finset corner.complementarySupportGraph.edgeSet) =
      {corner.incomingSupportEdge, corner.transverseSupportEdge} := by
  let incident := incidentEdgeFinset corner.complementarySupportGraph
    corner.complementarySupportJunction
  have hdegree := corner.supportJunction_degree_eq_two
  change incident.card = 2 at hdegree
  have hrootSubset :
      ({strand.rootFirstSupportEdge, strand.rootLastSupportEdge} :
        Finset corner.complementarySupportGraph.edgeSet) ⊆ incident := by
    intro edge hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl
    · exact strand.rootFirstSupportEdge_mem_incident
    · exact strand.rootLastSupportEdge_mem_incident
  have hrootCard :
      ({strand.rootFirstSupportEdge, strand.rootLastSupportEdge} :
        Finset corner.complementarySupportGraph.edgeSet).card = 2 :=
    Finset.card_pair strand.rootFirstSupportEdge_ne_rootLastSupportEdge
  have hrootEq :
      ({strand.rootFirstSupportEdge, strand.rootLastSupportEdge} :
        Finset corner.complementarySupportGraph.edgeSet) = incident := by
    apply Finset.eq_of_subset_of_card_le hrootSubset
    rw [hrootCard, hdegree]
  have hlaunchSubset :
      ({corner.incomingSupportEdge, corner.transverseSupportEdge} :
        Finset corner.complementarySupportGraph.edgeSet) ⊆ incident := by
    intro edge hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl
    · simp only [incident, incidentEdgeFinset, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact SimpleGraph.lineGraphCommonVertex_mem_left
        corner.incoming_transverse_adj
    · simp only [incident, incidentEdgeFinset, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact SimpleGraph.lineGraphCommonVertex_mem_right
        corner.incoming_transverse_adj
  have hlaunchCard :
      ({corner.incomingSupportEdge, corner.transverseSupportEdge} :
        Finset corner.complementarySupportGraph.edgeSet).card = 2 :=
    Finset.card_pair corner.incoming_transverse_adj.ne
  have hlaunchEq :
      ({corner.incomingSupportEdge, corner.transverseSupportEdge} :
        Finset corner.complementarySupportGraph.edgeSet) = incident := by
    apply Finset.eq_of_subset_of_card_le hlaunchSubset
    rw [hlaunchCard, hdegree]
  exact hrootEq.trans hlaunchEq.symm

/-- The rooted cut retains the launch's nontrivial companion change. -/
theorem rootCompanionColor_ne :
    (corner.supportEdgeColorState strand.rootFirstSupportEdge
      ).companionColor ≠
    (corner.supportEdgeColorState strand.rootLastSupportEdge
      ).companionColor := by
  have hfirst : strand.rootFirstSupportEdge = corner.incomingSupportEdge ∨
      strand.rootFirstSupportEdge = corner.transverseSupportEdge := by
    have hmem : strand.rootFirstSupportEdge ∈
        ({corner.incomingSupportEdge, corner.transverseSupportEdge} :
          Finset corner.complementarySupportGraph.edgeSet) := by
      rw [← strand.rootEdges_pair_eq_launchEdges]
      exact Finset.mem_insert_self _ _
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  have hlast : strand.rootLastSupportEdge = corner.incomingSupportEdge ∨
      strand.rootLastSupportEdge = corner.transverseSupportEdge := by
    have hmem : strand.rootLastSupportEdge ∈
        ({corner.incomingSupportEdge, corner.transverseSupportEdge} :
          Finset corner.complementarySupportGraph.edgeSet) := by
      rw [← strand.rootEdges_pair_eq_launchEdges]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  rcases hfirst with hfirst | hfirst <;>
    rcases hlast with hlast | hlast
  · exact False.elim (strand.rootFirstSupportEdge_ne_rootLastSupportEdge
      (hfirst.trans hlast.symm))
  · rw [hfirst, hlast, corner.supportEdgeColorState_incoming,
      corner.supportEdgeColorState_transverse]
    exact corner.incoming_third_companionColor_ne
  · rw [hfirst, hlast, corner.supportEdgeColorState_transverse,
      corner.supportEdgeColorState_incoming]
    exact corner.incoming_third_companionColor_ne.symm
  · exact False.elim (strand.rootFirstSupportEdge_ne_rootLastSupportEdge
      (hfirst.trans hlast.symm))

/-- A closed support cycle contains another companion-changing adjacency
away from the rooted cut. -/
theorem exists_internal_companionChange :
    ∃ (before : List corner.complementarySupportGraph.edgeSet)
        (first second : corner.complementarySupportGraph.edgeSet)
        (after : List corner.complementarySupportGraph.edgeSet),
      strand.cycle.edgeSubtypeSupport =
          before ++ first :: second :: after ∧
        corner.complementarySupportGraph.lineGraph.Adj first second ∧
        (corner.supportEdgeColorState first).companionColor ≠
          (corner.supportEdgeColorState second).companionColor := by
  have hchain : strand.cycle.edgeSubtypeSupport.IsChain
      corner.complementarySupportGraph.lineGraph.Adj :=
    strand.cycle_isCycle.isTrail.edgeSubtypeSupport_isChain
  rcases isChain_or_exists_adjacent_not
      (preferred := fun first second =>
        (corner.supportEdgeColorState first).companionColor =
          (corner.supportEdgeColorState second).companionColor)
      hchain with hstraight |
      ⟨before, first, second, after, hword, hadjacent, hchanged⟩
  · have heq := map_eq_of_mem_of_isChain hstraight
      (List.head_mem strand.cycleEdgeWord_ne_nil)
      (List.getLast_mem strand.cycleEdgeWord_ne_nil)
    exact False.elim (strand.rootCompanionColor_ne heq)
  · exact ⟨before, first, second, after, hword, hadjacent, hchanged⟩

/-- The second signed turn is a named port or an interior transverse
emission in the original coordinate. -/
theorem exists_internal_boundaryPort_or_transverseEmission :
    ∃ (before : List corner.complementarySupportGraph.edgeSet)
        (first second : corner.complementarySupportGraph.edgeSet)
        (after : List corner.complementarySupportGraph.edgeSet)
        (hadjacent : corner.complementarySupportGraph.lineGraph.Adj
          first second),
      strand.cycle.edgeSubtypeSupport =
          before ++ first :: second :: after ∧
        (corner.supportEdgeColorState first).companionColor ≠
          (corner.supportEdgeColorState second).companionColor ∧
        ((∃ sourcePort : Fin 4,
            SimpleGraph.lineGraphCommonVertex
                (corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent) =
              collar.sourcePortInCommonCore sourcePort) ∨
          (∃ targetPort : Fin 4,
            SimpleGraph.lineGraphCommonVertex
                (corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent) =
              collar.targetPortInCommonCore targetPort) ∨
          ∃ thirdEdge : collar.commonCore.edgeSet,
            collar.commonCore.lineGraph.Adj
                (corner.supportEdgeAmbientEdge first) thirdEdge ∧
              collar.commonCore.lineGraph.Adj
                (corner.supportEdgeAmbientEdge second) thirdEdge ∧
              collar.commonDiscrepancy sourceEscape thirdEdge =
                crossFaceZeroColor (!coordinate) ∧
              crossFaceCoordinate coordinate
                (collar.commonDiscrepancy sourceEscape thirdEdge) ≠ 0) := by
  rcases strand.exists_internal_companionChange with
    ⟨before, first, second, after, hword, hadjacent, hcompanion⟩
  exact ⟨before, first, second, after, hadjacent, hword, hcompanion,
    corner.changedSupportEdges_boundaryPort_or_transverseEmission
      first second hadjacent hcompanion⟩

end ClosedSupportStrand

namespace FirstTerminalSupportStrand.ClosedContinuationCycle

variable {corner : turn.ComplementarySupportCorner}
  {strand : corner.FirstTerminalSupportStrand}
  {continuation : strand.TerminalContinuation}
  (closed : strand.ClosedContinuationCycle continuation)

/-- Reroot a continuation cycle at the original signed launch. -/
noncomputable def toClosedSupportStrand : corner.ClosedSupportStrand := by
  let supportGraph := corner.complementarySupportGraph
  have hdegree : ∀ vertex : collar.commonCoreVertex,
      supportGraph.degree vertex ≤ 2 :=
    corner.complementarySupportDegree_le_two
  have hcycleComponent : closed.supportCycle.toSubgraph.verts =
      (supportGraph.connectedComponentMk strand.finish.1).supp :=
    isCycle_toSubgraph_verts_eq_connectedComponentSupp_of_degree_le_two
      closed.supportCycle_isCycle hdegree
  have hjunctionComponent : corner.complementarySupportJunction ∈
      (supportGraph.connectedComponentMk strand.finish.1).supp := by
    rw [(supportGraph.connectedComponentMk strand.finish.1).mem_supp_iff]
    exact SimpleGraph.ConnectedComponent.sound strand.path.reachable
  have hjunctionVerts : corner.complementarySupportJunction ∈
      closed.supportCycle.toSubgraph.verts := by
    rw [hcycleComponent]
    exact hjunctionComponent
  have hjunctionSupport : corner.complementarySupportJunction ∈
      closed.supportCycle.support :=
    closed.supportCycle.mem_verts_toSubgraph.mp hjunctionVerts
  let launchCycle := closed.supportCycle.rotate
    corner.complementarySupportJunction hjunctionSupport
  have hlaunchCycle : launchCycle.IsCycle :=
    closed.supportCycle_isCycle.rotate hjunctionSupport
  have hjunctionDegree : supportGraph.degree
      corner.complementarySupportJunction = 2 := by
    rw [← incidentEdgeFinset_card_eq_degree]
    exact corner.supportJunction_degree_eq_two
  refine {
    cycle := launchCycle
    cycle_isCycle := hlaunchCycle
    incoming_mem := ?_
    transverse_mem := ?_ }
  · apply edge_mem_rooted_isCycle_of_degree_eq_two
      hlaunchCycle hjunctionDegree corner.incomingSupportEdge
    exact SimpleGraph.lineGraphCommonVertex_mem_left
      corner.incoming_transverse_adj
  · apply edge_mem_rooted_isCycle_of_degree_eq_two
      hlaunchCycle hjunctionDegree corner.transverseSupportEdge
    exact SimpleGraph.lineGraphCommonVertex_mem_right
      corner.incoming_transverse_adj

end FirstTerminalSupportStrand.ClosedContinuationCycle

namespace ClosedSupportRoute

variable {corner : turn.ComplementarySupportCorner}

/-- Canonically root either closed-route constructor at the signed launch. -/
noncomputable def rootedAtLaunch
    (route : corner.ClosedSupportRoute) : corner.ClosedSupportStrand :=
  match route with
  | .direct strand => strand
  | .continued _strand _continuation closed => closed.toClosedSupportStrand

/-- Every generic closed route exposes a second turn as a boundary event or
an interior transverse emission. -/
theorem exists_internal_boundaryPort_or_transverseEmission
    (route : corner.ClosedSupportRoute) :
    ∃ (before : List corner.complementarySupportGraph.edgeSet)
        (first second : corner.complementarySupportGraph.edgeSet)
        (after : List corner.complementarySupportGraph.edgeSet)
        (hadjacent : corner.complementarySupportGraph.lineGraph.Adj
          first second),
      route.rootedAtLaunch.cycle.edgeSubtypeSupport =
          before ++ first :: second :: after ∧
        (corner.supportEdgeColorState first).companionColor ≠
          (corner.supportEdgeColorState second).companionColor ∧
        ((∃ sourcePort : Fin 4,
            SimpleGraph.lineGraphCommonVertex
                (corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent) =
              collar.sourcePortInCommonCore sourcePort) ∨
          (∃ targetPort : Fin 4,
            SimpleGraph.lineGraphCommonVertex
                (corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent) =
              collar.targetPortInCommonCore targetPort) ∨
          ∃ thirdEdge : collar.commonCore.edgeSet,
            collar.commonCore.lineGraph.Adj
                (corner.supportEdgeAmbientEdge first) thirdEdge ∧
              collar.commonCore.lineGraph.Adj
                (corner.supportEdgeAmbientEdge second) thirdEdge ∧
              collar.commonDiscrepancy sourceEscape thirdEdge =
                crossFaceZeroColor (!coordinate) ∧
              crossFaceCoordinate coordinate
                (collar.commonDiscrepancy sourceEscape thirdEdge) ≠ 0) := by
  exact route.rootedAtLaunch.exists_internal_boundaryPort_or_transverseEmission

end ClosedSupportRoute
end ScalarCompanionTurn.ComplementarySupportCorner
end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
