import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAlternatingSupport

/-! Degree-two passages for coordinate-generic companion turns. -/

namespace Mettapedia.GraphTheory.FourColor

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

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

variable {corner : turn.ComplementarySupportCorner}

namespace FirstTerminalSupportStrand

variable (strand : corner.FirstTerminalSupportStrand)

/-- Degree two is exactly vanishing of the scalar boundary coordinate. -/
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

/-- The second supported edge through a degree-two named terminal. -/
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

/-- A continuation exists exactly at a degree-two terminal. -/
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

/-- The exact terminal dichotomy is charged boundary or continuation. -/
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

/-- Directing the second edge reaches a distinct charged named terminal. -/
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
    crossFaceCoordinate (!coordinate)
      ((collar.commonDiscrepancyBoundaryState sourceEscape).1 finish) ≠ 0

/-- Directing the second edge can instead close the support component. -/
structure ClosedContinuationCycle
    (continuation : strand.TerminalContinuation) where
  supportCycle : corner.complementarySupportGraph.Walk
    strand.finish.1 strand.finish.1
  supportCycle_isCycle : supportCycle.IsCycle
  terminal_edge_mem : strand.terminalSupportEdge.1 ∈ supportCycle.edges
  continuation_edge_mem : continuation.edge.1 ∈ supportCycle.edges

/-- A degree-two passage reaches a charged collar terminal or closes into a
simple support cycle. -/
theorem chargedContinuationStrand_or_closedContinuationCycle
    (continuation : strand.TerminalContinuation) :
    Nonempty (strand.ChargedContinuationStrand continuation) ∨
      Nonempty (strand.ClosedContinuationCycle continuation) := by
  classical
  let supportGraph := corner.complementarySupportGraph
  let scalarChain : collar.commonCore.edgeSet → F2 :=
    fun edge => crossFaceCoordinate (!coordinate)
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
          scalarChain finish ≠ 0 :=
        (scalarSupportGraph_degree_odd_iff scalarChain finish).1 hfinishOdd
      by_contra hnotTerminal
      apply hscalarBoundary
      rw [scalarVertexKirchhoffSum_crossFaceCoordinate,
        collar.vertexKirchhoffSum_commonDiscrepancy_eq_zero_of_not_mem_commonPortVertexFinset
          sourceEscape finish hnotTerminal]
      cases (!coordinate) <;> rfl
    let finishTerminal : collar.commonPortVertexFinset :=
      ⟨finish, hfinishTerminal⟩
    have hfinishBoundary :
        crossFaceCoordinate (!coordinate)
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

variable {strand : corner.FirstTerminalSupportStrand}
  {continuation : strand.TerminalContinuation}
  (continued : strand.ChargedContinuationStrand continuation)

/-- Canonical representative of the charged continuation endpoint. -/
noncomputable def finishRepresentative :
    IntrinsicCollarTerminalRepresentative
      collar.intrinsicCollarPortOverlapProfile :=
  collar.intrinsicCollarTerminalRepresentativeEquiv.symm continued.finish

@[simp]
theorem finishRepresentative_apply :
    collar.intrinsicCollarTerminalRepresentativeEquiv
        continued.finishRepresentative = continued.finish :=
  Equiv.apply_symm_apply _ _

/-- The endpoint boundary is exactly its fixed collar word. -/
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

/-- The fixed endpoint word is charged in the active support coordinate. -/
theorem finishBoundaryWord_coordinate_ne_zero :
    crossFaceCoordinate (!coordinate)
      (intrinsicCollarTerminalBoundaryWord
        collar.intrinsicCollarPortOverlapProfile
        (collar.intrinsicCollarCorrectionWord sourceEscape)
        (intrinsicCollarTerminalCoordinateOfRepresentative
          continued.finishRepresentative)) ≠ 0 := by
  rw [continued.finishBoundaryWord_eq]
  exact continued.finish_boundary_ne_zero

/-- A charged continuation endpoint produces an actual Kempe action and
canonical same-base reentry. -/
theorem kempeAction_and_sameBaseReentry :
    ChargedTerminalKempeAction collar sourceEscape (!coordinate)
        continued.finishRepresentative ∧
      (sourceNormal.SameBaseKempeReentry sourceEscape ∨
        collar.targetNormal.SameBaseKempeReentry collar.targetEscape) := by
  let witness :=
    collar.chargedTerminalColorWitness_of_coordinate_ne_zero
      sourceEscape (!coordinate) continued.finishRepresentative
        continued.finishBoundaryWord_coordinate_ne_zero
  let action := witness.nonempty_kempeAction
  exact ⟨action, action.sameBaseReentry⟩

end ChargedContinuationStrand

end FirstTerminalSupportStrand

/-- A generic companion turn reaches a charged endpoint directly or after
one degree-two named-terminal passage. -/
inductive ChargedSupportRoute
    (corner : turn.ComplementarySupportCorner) where
  | direct (strand : corner.FirstTerminalSupportStrand)
      (charged : strand.terminalBoundaryCoordinate ≠ 0)
  | continued (strand : corner.FirstTerminalSupportStrand)
      (continuation : strand.TerminalContinuation)
      (route : strand.ChargedContinuationStrand continuation)

/-- The closed alternative occurs at the launch component or after the
degree-two passage. -/
inductive ClosedSupportRoute
    (corner : turn.ComplementarySupportCorner) where
  | direct (strand : corner.ClosedSupportStrand)
  | continued (strand : corner.FirstTerminalSupportStrand)
      (continuation : strand.TerminalContinuation)
      (route : strand.ClosedContinuationCycle continuation)

namespace ChargedSupportRoute

variable {corner : turn.ComplementarySupportCorner}

/-- Every charged route carries an actual one-component Kempe action and
canonical reentry at its endpoint. -/
theorem exists_kempeAction_and_sameBaseReentry
    (route : corner.ChargedSupportRoute) :
    ∃ representative : IntrinsicCollarTerminalRepresentative
        collar.intrinsicCollarPortOverlapProfile,
      ChargedTerminalKempeAction collar sourceEscape (!coordinate)
          representative ∧
        (sourceNormal.SameBaseKempeReentry sourceEscape ∨
          collar.targetNormal.SameBaseKempeReentry collar.targetEscape) := by
  cases route with
  | direct strand charged =>
      have hdegree :=
        strand.terminalBoundaryCoordinate_ne_zero_iff_supportDegree_eq_one.1
          charged
      exact ⟨strand.terminalRepresentative,
        strand.kempeAction_and_sameBaseReentry_of_supportDegree_eq_one
          hdegree⟩
  | continued strand continuation continued =>
      exact ⟨continued.finishRepresentative,
        continued.kempeAction_and_sameBaseReentry⟩

end ChargedSupportRoute

/-- No degree-two terminal remains: every generic turn yields an actual
charged route or an explicitly closed support route. -/
theorem chargedSupportRoute_or_closedSupportRoute
    (corner : turn.ComplementarySupportCorner) :
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

/-- Endpoint resolution in its strongest useful form: an actual Kempe
action with reentry, or a closed scalar-support route. -/
theorem exists_kempeAction_and_sameBaseReentry_or_closedSupportRoute
    (corner : turn.ComplementarySupportCorner) :
    (∃ representative : IntrinsicCollarTerminalRepresentative
        collar.intrinsicCollarPortOverlapProfile,
      ChargedTerminalKempeAction collar sourceEscape (!coordinate)
          representative ∧
        (sourceNormal.SameBaseKempeReentry sourceEscape ∨
          collar.targetNormal.SameBaseKempeReentry collar.targetEscape)) ∨
      Nonempty corner.ClosedSupportRoute := by
  rcases corner.chargedSupportRoute_or_closedSupportRoute with
    hcharged | hclosed
  · rcases hcharged with ⟨route⟩
    exact Or.inl route.exists_kempeAction_and_sameBaseReentry
  · exact Or.inr hclosed

end ScalarCompanionTurn.ComplementarySupportCorner
end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
