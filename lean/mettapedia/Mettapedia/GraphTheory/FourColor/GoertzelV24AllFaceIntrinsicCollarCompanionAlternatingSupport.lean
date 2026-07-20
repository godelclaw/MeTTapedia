import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAlternatingTurn

/-! Generic support components entered by coordinate-generic signed turns. -/

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

/-- Common endpoint of the incoming and transverse support edges. -/
abbrev complementarySupportJunction : collar.commonCoreVertex :=
  SimpleGraph.lineGraphCommonVertex corner.incoming_transverse_adj

/-- Every vertex of the entered scalar-support graph has degree at most
two. -/
theorem complementarySupportDegree_le_two
    (vertex : collar.commonCoreVertex) :
    corner.complementarySupportGraph.degree vertex ≤ 2 := by
  rw [← incidentEdgeFinset_card_eq_degree]
  exact taitDiscrepancySupport_incidentCard_le_two
    (collar.sourceCommonColoring sourceEscape)
    collar.targetCommonColoring
    (collar.sourceCommonColoring_isTait sourceEscape)
    collar.targetCommonColoring_isTait
    (!coordinate) vertex
    (collar.commonCore_incidentEdgeFinset_card_le_three vertex)

/-- The directed component entered along the transverse edge reaches its
first later named collar terminal or closes into a simple support cycle. -/
theorem exists_firstTerminalPath_or_supportCycle :
    (∃ finish : collar.commonCoreVertex,
        finish ∈ collar.commonPortVertexFinset ∧
        finish ≠ corner.complementarySupportJunction ∧
        ∃ path : corner.complementarySupportGraph.Walk
            corner.complementarySupportJunction finish,
          path.IsPath ∧ 0 < path.length ∧
          (∀ position : Nat, 0 < position → position < path.length →
            path.getVert position ∉ collar.commonPortVertexFinset) ∧
          corner.incomingSupportEdge.1 ∉ path.edges ∧
          corner.transverseSupportEdge.1 ∈ path.edges) ∨
      ∃ supportCycle : corner.complementarySupportGraph.Walk
          corner.complementarySupportJunction
          corner.complementarySupportJunction,
        supportCycle.IsCycle ∧
        corner.incomingSupportEdge.1 ∈ supportCycle.edges ∧
        corner.transverseSupportEdge.1 ∈ supportCycle.edges := by
  classical
  let scalarChain : collar.commonCore.edgeSet → F2 :=
    fun edge => crossFaceCoordinate (!coordinate)
      (collar.commonDiscrepancy sourceEscape edge)
  let supportGraph : SimpleGraph collar.commonCoreVertex :=
    scalarSupportGraph scalarChain
  let junction := corner.complementarySupportJunction
  change (∃ finish : collar.commonCoreVertex,
      finish ∈ collar.commonPortVertexFinset ∧ finish ≠ junction ∧
      ∃ path : supportGraph.Walk junction finish,
        path.IsPath ∧ 0 < path.length ∧
        (∀ position : Nat, 0 < position → position < path.length →
          path.getVert position ∉ collar.commonPortVertexFinset) ∧
        corner.incomingSupportEdge.1 ∉ path.edges ∧
        corner.transverseSupportEdge.1 ∈ path.edges) ∨
    ∃ supportCycle : supportGraph.Walk junction junction,
      supportCycle.IsCycle ∧
      corner.incomingSupportEdge.1 ∈ supportCycle.edges ∧
      corner.transverseSupportEdge.1 ∈ supportCycle.edges
  have hjunctionDegree : supportGraph.degree junction = 2 := by
    rw [← incidentEdgeFinset_card_eq_degree]
    exact corner.supportJunction_degree_eq_two
  have hincomingIncident : junction ∈ corner.incomingSupportEdge.1 :=
    SimpleGraph.lineGraphCommonVertex_mem_left
      corner.incoming_transverse_adj
  have htransverseIncident : junction ∈ corner.transverseSupportEdge.1 :=
    SimpleGraph.lineGraphCommonVertex_mem_right
      corner.incoming_transverse_adj
  have hoddTerminal : ∀ vertex : collar.commonCoreVertex,
      Odd (supportGraph.degree vertex) →
        vertex ∈ collar.commonPortVertexFinset := by
    intro vertex hodd
    have hscalarBoundary :
        scalarVertexKirchhoffSum collar.commonCore scalarChain vertex ≠ 0 :=
      (scalarSupportGraph_degree_odd_iff scalarChain vertex).1 hodd
    by_contra hterminal
    apply hscalarBoundary
    rw [scalarVertexKirchhoffSum_crossFaceCoordinate,
      collar.vertexKirchhoffSum_commonDiscrepancy_eq_zero_of_not_mem_commonPortVertexFinset
        sourceEscape vertex hterminal]
    cases (!coordinate) <;> rfl
  rcases exists_directed_odd_path_or_cycle_of_incident_pair
      (H := supportGraph) junction corner.incomingSupportEdge
        corner.transverseSupportEdge
        corner.incoming_transverse_adj.ne
        hincomingIncident htransverseIncident hjunctionDegree with
    hterminal | hcycle
  · rcases hterminal with
      ⟨finish, hfinishNe, hfinishOdd, path,
        hpath, hincomingAvoided, _htransversePath⟩
    have hfinishTerminal := hoddTerminal finish hfinishOdd
    rcases exists_firstTerminalPrefix collar.commonPortVertexFinset
        path hfinishTerminal hfinishNe hpath with
      ⟨firstTerminal, initialPath, hfirstTerminal, hfirstNe,
        hinitialPath, hinitialPositive, hinternal, hinitialSubwalk⟩
    have hincomingInitial : corner.incomingSupportEdge.1 ∉
        initialPath.edges := by
      intro hincoming
      exact hincomingAvoided (hinitialSubwalk.edges_subset hincoming)
    have htransverseInitial : corner.transverseSupportEdge.1 ∈
        initialPath.edges := by
      apply second_mem_edges_of_isPath_of_degree_eq_two_of_first_not_mem
        hinitialPath hfirstNe corner.incomingSupportEdge
          corner.transverseSupportEdge corner.incoming_transverse_adj.ne
      · exact hincomingIncident
      · exact htransverseIncident
      · exact hjunctionDegree
      · exact hincomingInitial
    exact Or.inl ⟨firstTerminal, hfirstTerminal, hfirstNe,
      initialPath, hinitialPath, hinitialPositive, hinternal,
      hincomingInitial, htransverseInitial⟩
  · exact Or.inr hcycle

/-- A support strand from a generic signed turn to its first later named
collar terminal. -/
structure FirstTerminalSupportStrand
    (corner : turn.ComplementarySupportCorner) where
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
  transverse_mem : corner.transverseSupportEdge.1 ∈ path.edges

/-- A generic signed turn whose entered support component closes before a
distinct named terminal. -/
structure ClosedSupportStrand
    (corner : turn.ComplementarySupportCorner) where
  cycle : corner.complementarySupportGraph.Walk
    corner.complementarySupportJunction
    corner.complementarySupportJunction
  cycle_isCycle : cycle.IsCycle
  incoming_mem : corner.incomingSupportEdge.1 ∈ cycle.edges
  transverse_mem : corner.transverseSupportEdge.1 ∈ cycle.edges

/-- Every generic support launch constructs one of the two strand forms. -/
theorem firstTerminalSupportStrand_or_closedSupportStrand :
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

variable {corner : turn.ComplementarySupportCorner}
  (strand : corner.FirstTerminalSupportStrand)

/-- Canonical representative of the first terminal. -/
noncomputable def terminalRepresentative :
    IntrinsicCollarTerminalRepresentative
      collar.intrinsicCollarPortOverlapProfile :=
  collar.intrinsicCollarTerminalRepresentativeEquiv.symm strand.finish

@[simp]
theorem terminalRepresentative_apply :
    collar.intrinsicCollarTerminalRepresentativeEquiv
        strand.terminalRepresentative = strand.finish :=
  Equiv.apply_symm_apply _ _

/-- Selected scalar coordinate of the exact boundary at the first
terminal. -/
def terminalBoundaryCoordinate : F2 :=
  crossFaceCoordinate (!coordinate)
    ((collar.commonDiscrepancyBoundaryState sourceEscape).1 strand.finish)

/-- The terminal boundary is exactly the fixed collar word at its canonical
representative. -/
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

/-- Scalar form of the exact terminal-word identification. -/
theorem terminalBoundaryCoordinate_eq_word :
    strand.terminalBoundaryCoordinate =
      crossFaceCoordinate (!coordinate)
        (intrinsicCollarTerminalBoundaryWord
          collar.intrinsicCollarPortOverlapProfile
          (collar.intrinsicCollarCorrectionWord sourceEscape)
          (intrinsicCollarTerminalCoordinateOfRepresentative
            strand.terminalRepresentative)) := by
  exact congrArg (crossFaceCoordinate (!coordinate))
    strand.terminalBoundaryWord_eq.symm

/-- Last support edge of the positive terminal strand. -/
def terminalSupportEdge : corner.complementarySupportGraph.edgeSet :=
  strand.path.edgeSubtypeSupport.getLast
    (edgeSubtypeSupport_ne_nil_of_length_pos
      strand.path strand.path_positive)

theorem terminalSupportEdge_mem_incident :
    strand.terminalSupportEdge ∈
      incidentEdgeFinset corner.complementarySupportGraph
        strand.finish.1 := by
  rw [terminalSupportEdge,
    edgeSubtypeSupport_getLast_eq_lastEdgeSet strand.path
      strand.path_positive]
  exact strand.path.lastEdgeSet_mem_incidentEdgeFinset
    (SimpleGraph.Walk.not_nil_iff_lt_length.mpr strand.path_positive)

theorem terminalSupportDegree_le_two :
    (incidentEdgeFinset corner.complementarySupportGraph
      strand.finish.1).card ≤ 2 := by
  rw [incidentEdgeFinset_card_eq_degree]
  exact corner.complementarySupportDegree_le_two strand.finish.1

theorem terminalSupportDegree_pos :
    0 < (incidentEdgeFinset corner.complementarySupportGraph
      strand.finish.1).card :=
  Finset.card_pos.mpr
    ⟨strand.terminalSupportEdge, strand.terminalSupportEdge_mem_incident⟩

/-- The first named terminal is a support endpoint or a degree-two
passage. -/
theorem terminalSupportDegree_eq_one_or_two :
    (incidentEdgeFinset corner.complementarySupportGraph
        strand.finish.1).card = 1 ∨
      (incidentEdgeFinset corner.complementarySupportGraph
        strand.finish.1).card = 2 := by
  have hpositive := strand.terminalSupportDegree_pos
  have hupper := strand.terminalSupportDegree_le_two
  omega

/-- Degree one is exactly nonzero boundary in the entered scalar
coordinate. -/
theorem terminalBoundaryCoordinate_ne_zero_iff_supportDegree_eq_one :
    strand.terminalBoundaryCoordinate ≠ 0 ↔
      (incidentEdgeFinset corner.complementarySupportGraph
        strand.finish.1).card = 1 := by
  unfold terminalBoundaryCoordinate
  change crossFaceCoordinate (!coordinate)
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

/-- A degree-one generic terminal is consumed immediately by an actual
Kempe action and canonical same-base reentry. -/
theorem kempeAction_and_sameBaseReentry_of_supportDegree_eq_one
    (hdegree : (incidentEdgeFinset corner.complementarySupportGraph
      strand.finish.1).card = 1) :
    ChargedTerminalKempeAction collar sourceEscape (!coordinate)
        strand.terminalRepresentative ∧
      (sourceNormal.SameBaseKempeReentry sourceEscape ∨
        collar.targetNormal.SameBaseKempeReentry collar.targetEscape) := by
  have hterminal : strand.terminalBoundaryCoordinate ≠ 0 :=
    strand.terminalBoundaryCoordinate_ne_zero_iff_supportDegree_eq_one.2
      hdegree
  have hcharged : crossFaceCoordinate (!coordinate)
      (intrinsicCollarTerminalBoundaryWord
        collar.intrinsicCollarPortOverlapProfile
        (collar.intrinsicCollarCorrectionWord sourceEscape)
        (intrinsicCollarTerminalCoordinateOfRepresentative
          strand.terminalRepresentative)) ≠ 0 := by
    rw [← strand.terminalBoundaryCoordinate_eq_word]
    exact hterminal
  let witness :=
    collar.chargedTerminalColorWitness_of_coordinate_ne_zero
      sourceEscape (!coordinate) strand.terminalRepresentative hcharged
  let action := witness.nonempty_kempeAction
  exact ⟨action, action.sameBaseReentry⟩

end FirstTerminalSupportStrand
end ScalarCompanionTurn.ComplementarySupportCorner
end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
