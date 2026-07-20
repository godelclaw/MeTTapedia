import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionTransfer

/-! The global straight-or-transverse split on a singleton companion trail. -/

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

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

/-- A chain for `primary` is either also a chain for `preferred`, or it has
an explicitly located adjacent primary step that fails `preferred`. -/
theorem isChain_or_exists_adjacent_not
    {State : Type*} {primary preferred : State → State → Prop}
    {states : List State} (hprimary : states.IsChain primary) :
    states.IsChain preferred ∨
      ∃ (before : List State) (first second : State) (after : List State),
        states = before ++ first :: second :: after ∧
          primary first second ∧ ¬ preferred first second := by
  classical
  induction hprimary with
  | nil => exact Or.inl .nil
  | singleton state => exact Or.inl (.singleton state)
  | @cons_cons first second rest hstep htail ih =>
      by_cases hpreferred : preferred first second
      · rcases ih with htailPreferred |
          ⟨before, changedFirst, changedSecond, after,
            htailEq, hchangedStep, hchangedPreferred⟩
        · exact Or.inl (.cons_cons hpreferred htailPreferred)
        · exact Or.inr
            ⟨first :: before, changedFirst, changedSecond, after,
              by simp [htailEq], hchangedStep, hchangedPreferred⟩
      · exact Or.inr
          ⟨[], first, second, rest, rfl, hstep, hpreferred⟩

/-- Equality along adjacent entries of a list propagates between arbitrary
entries of that list. -/
theorem map_eq_of_mem_of_isChain
    {State Value : Type*} {value : State → Value} {states : List State}
    (hchain : states.IsChain (fun first second =>
      value first = value second))
    {first second : State} (hfirst : first ∈ states)
    (hsecond : second ∈ states) :
    value first = value second := by
  have hmapped : (states.map value).IsChain (· = ·) :=
    (List.isChain_map value).2 hchain
  have hpairwise : (states.map value).Pairwise (· = ·) :=
    hmapped.pairwise
  have hfirstMapped : value first ∈ states.map value :=
    List.mem_map.mpr ⟨first, hfirst, rfl⟩
  have hsecondMapped : value second ∈ states.map value :=
    List.mem_map.mpr ⟨second, hsecond, rfl⟩
  exact (hpairwise.rel_head hfirstMapped).symm.trans
    (hpairwise.rel_head hsecondMapped)

/-- Every scalar discrepancy state is exactly an ordered occurrence of the
distinguished color and its companion. -/
theorem ScalarDiscrepancyColorState.source_target_zero_companion_cases
    {coordinate : Bool} (state : ScalarDiscrepancyColorState coordinate) :
    (state.sourceColor = crossFaceZeroColor coordinate ∧
        state.targetColor = state.companionColor) ∨
      (state.sourceColor = state.companionColor ∧
        state.targetColor = crossFaceZeroColor coordinate) := by
  rcases state.exactlyOne_zeroColor with hsource | htarget
  · exact Or.inl ⟨hsource.1,
      (state.companionColor_of_sourceColor_eq hsource.1).symm⟩
  · exact Or.inr ⟨
      (state.companionColor_of_sourceColor_ne htarget.1).symm,
      htarget.2⟩

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {graphData : Data G}
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

namespace SingletonCompanionTransferPath

variable (transfer : SingletonCompanionTransferPath collar sourceEscape)

/-- An edge of the singleton trail together with its actual support proof. -/
abbrev SupportEdge :=
  {edge : collar.commonCore.edgeSet //
    edge ∈ transfer.path.edgeSubtypeSupport}

/-- The support edges in their trail order, retaining edge identity. -/
noncomputable def supportEdgeWord : List transfer.SupportEdge :=
  transfer.path.edgeSubtypeSupport.attach

@[simp]
theorem supportEdgeWord_length :
    transfer.supportEdgeWord.length = transfer.path.length := by
  rw [supportEdgeWord, List.length_attach,
    transfer.path.edgeSubtypeSupport_length]

theorem supportEdgeWord_ne_nil : transfer.supportEdgeWord ≠ [] := by
  intro hnil
  have hlength := congrArg List.length hnil
  rw [transfer.supportEdgeWord_length] at hlength
  exact (Nat.ne_of_gt transfer.path_positive) hlength

/-- The color state attached to a support edge while retaining its graph
identity. -/
noncomputable def supportEdgeState (edge : transfer.SupportEdge) :
    ScalarDiscrepancyColorState transfer.coordinate :=
  transfer.stateOfEdge edge.1 edge.2

@[simp]
theorem supportEdgeState_sourceColor (edge : transfer.SupportEdge) :
    (transfer.supportEdgeState edge).sourceColor =
      collar.sourceCommonColoring sourceEscape edge.1 := rfl

@[simp]
theorem supportEdgeState_targetColor (edge : transfer.SupportEdge) :
    (transfer.supportEdgeState edge).targetColor =
      collar.targetCommonColoring edge.1 := rfl

/-- The exact graph-and-color transition between consecutive support edges. -/
def SupportEdgeTransition
    (first second : transfer.SupportEdge) : Prop :=
  collar.commonCore.lineGraph.Adj first.1 second.1 ∧
    ScalarDiscrepancyColorTransition
      (transfer.supportEdgeState first) (transfer.supportEdgeState second)

/-- A straight support transition keeps its companion color. -/
def SupportEdgeStraight
    (first second : transfer.SupportEdge) : Prop :=
  (transfer.supportEdgeState first).companionColor =
    (transfer.supportEdgeState second).companionColor

/-- The edge-retaining singleton word follows the exact graph-and-color
transition relation. -/
theorem supportEdgeWord_isChain_transition :
    transfer.supportEdgeWord.IsChain transfer.SupportEdgeTransition := by
  rw [supportEdgeWord, List.isChain_attach]
  apply transfer.path_isPath.isTrail.edgeSubtypeSupport_isChain.imp_of_mem_imp
  intro first second hfirstMem hsecondMem hadjacent
  exact ⟨hfirstMem, hsecondMem, hadjacent,
    scalarDiscrepancyColorTransition_of_adjacent
      (collar.sourceCommonColoring sourceEscape)
      collar.targetCommonColoring
      (collar.sourceCommonColoring_isTait sourceEscape)
      collar.targetCommonColoring_isTait
      transfer.coordinate hadjacent
      (transfer.support first hfirstMem)
      (transfer.support second hsecondMem)⟩

/-- The global edge-retaining transfer is either straight throughout or has
an explicitly located adjacent companion change. -/
theorem straightChain_or_exists_changedAdjacent :
    transfer.supportEdgeWord.IsChain transfer.SupportEdgeStraight ∨
      ∃ (before : List transfer.SupportEdge)
          (first second : transfer.SupportEdge)
          (after : List transfer.SupportEdge),
        transfer.supportEdgeWord =
            before ++ first :: second :: after ∧
          collar.commonCore.lineGraph.Adj first.1 second.1 ∧
          (transfer.supportEdgeState first).companionColor ≠
            (transfer.supportEdgeState second).companionColor := by
  rcases isChain_or_exists_adjacent_not
      transfer.supportEdgeWord_isChain_transition with hstraight |
      ⟨before, first, second, after, hword, htransition, hnotStraight⟩
  · exact Or.inl hstraight
  · exact Or.inr ⟨before, first, second, after, hword,
      htransition.1, hnotStraight⟩

/-- If the whole singleton trail is straight, one fixed companion color is
used on every support edge, oppositely ordered in the two colorings. -/
theorem exists_fixedTwoColorPattern_of_straight
    (hstraight :
      transfer.supportEdgeWord.IsChain transfer.SupportEdgeStraight) :
    ∃ companion : Color,
      companion ≠ 0 ∧
      companion ≠ crossFaceZeroColor transfer.coordinate ∧
      ∀ edge ∈ transfer.supportEdgeWord,
        (collar.sourceCommonColoring sourceEscape edge.1 =
              crossFaceZeroColor transfer.coordinate ∧
            collar.targetCommonColoring edge.1 = companion) ∨
          (collar.sourceCommonColoring sourceEscape edge.1 = companion ∧
            collar.targetCommonColoring edge.1 =
              crossFaceZeroColor transfer.coordinate) := by
  let first := transfer.supportEdgeWord.head transfer.supportEdgeWord_ne_nil
  let companion := (transfer.supportEdgeState first).companionColor
  refine ⟨companion,
    (transfer.supportEdgeState first).companionColor_ne_zero,
    (transfer.supportEdgeState first).companionColor_ne_zeroColor, ?_⟩
  intro edge hedge
  have hfirstMem : first ∈ transfer.supportEdgeWord :=
    List.head_mem transfer.supportEdgeWord_ne_nil
  have hcompanion :
      (transfer.supportEdgeState edge).companionColor = companion := by
    exact (map_eq_of_mem_of_isChain hstraight hfirstMem hedge).symm
  have hcases :=
    (transfer.supportEdgeState edge).source_target_zero_companion_cases
  rw [hcompanion] at hcases
  simpa only [supportEdgeState_sourceColor,
    supportEdgeState_targetColor] using hcases

/-- The graph-level global dichotomy: either the discrepancy trail is one
fixed two-color pattern, or a consecutive pair changes companion and is ready
to emit a transverse cross-channel at any cubic third edge. -/
theorem fixedTwoColorPattern_or_exists_changedAdjacent :
    (∃ companion : Color,
      companion ≠ 0 ∧
      companion ≠ crossFaceZeroColor transfer.coordinate ∧
      ∀ edge ∈ transfer.supportEdgeWord,
        (collar.sourceCommonColoring sourceEscape edge.1 =
              crossFaceZeroColor transfer.coordinate ∧
            collar.targetCommonColoring edge.1 = companion) ∨
          (collar.sourceCommonColoring sourceEscape edge.1 = companion ∧
            collar.targetCommonColoring edge.1 =
              crossFaceZeroColor transfer.coordinate)) ∨
      ∃ (before : List transfer.SupportEdge)
          (first second : transfer.SupportEdge)
          (after : List transfer.SupportEdge),
        transfer.supportEdgeWord =
            before ++ first :: second :: after ∧
          collar.commonCore.lineGraph.Adj first.1 second.1 ∧
          (transfer.supportEdgeState first).companionColor ≠
            (transfer.supportEdgeState second).companionColor := by
  rcases transfer.straightChain_or_exists_changedAdjacent with
    hstraight | hchanged
  · exact Or.inl (transfer.exists_fixedTwoColorPattern_of_straight hstraight)
  · exact Or.inr hchanged

/-- Away from all common-core ports, the common vertex of two consecutive
trail edges retains ambient cubic degree and therefore has a third edge. -/
theorem exists_thirdEdge_of_adjacent_of_commonVertex_not_ports
    (first second : transfer.SupportEdge)
    (hfirstSecond : collar.commonCore.lineGraph.Adj first.1 second.1)
    (hsource : ∀ port : Fin 4,
      SimpleGraph.lineGraphCommonVertex hfirstSecond ≠
        collar.sourcePortInCommonCore port)
    (htarget : ∀ port : Fin 4,
      SimpleGraph.lineGraphCommonVertex hfirstSecond ≠
        collar.targetPortInCommonCore port) :
    ∃ thirdEdge : collar.commonCore.edgeSet,
      collar.commonCore.lineGraph.Adj first.1 thirdEdge ∧
        collar.commonCore.lineGraph.Adj second.1 thirdEdge := by
  let vertex := SimpleGraph.lineGraphCommonVertex hfirstSecond
  have hcard :
      (incidentEdgeFinset collar.commonCore vertex).card = 3 :=
    collar.card_incidentEdgeFinset_commonCore_eq_three_of_not_ports
      vertex hsource htarget
  have hfirstSecondNe : first.1 ≠ second.1 := hfirstSecond.ne
  have hnotSubset :
      ¬incidentEdgeFinset collar.commonCore vertex ⊆
        ({first.1, second.1} : Finset collar.commonCore.edgeSet) := by
    intro hsubset
    have hcardLe := Finset.card_le_card hsubset
    have hpairCard :
        ({first.1, second.1} : Finset collar.commonCore.edgeSet).card = 2 := by
      exact Finset.card_pair hfirstSecondNe
    rw [hcard, hpairCard] at hcardLe
    omega
  rcases Finset.not_subset.mp hnotSubset with
    ⟨thirdEdge, hthirdIncident, hthirdNotPair⟩
  have hthirdVertex : vertex ∈ (thirdEdge.1 : Sym2 collar.commonCoreVertex) := by
    simpa only [incidentEdgeFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] using hthirdIncident
  have hthirdNeFirst : thirdEdge ≠ first.1 := by
    intro heq
    apply hthirdNotPair
    rw [heq]
    exact Finset.mem_insert_self _ _
  have hthirdNeSecond : thirdEdge ≠ second.1 := by
    intro heq
    apply hthirdNotPair
    rw [heq]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  exact ⟨thirdEdge,
    collar.commonCore.lineGraph_adj_of_edgeSet_common_vertex
      hthirdNeFirst.symm
      (SimpleGraph.lineGraphCommonVertex_mem_left hfirstSecond)
      hthirdVertex,
    collar.commonCore.lineGraph_adj_of_edgeSet_common_vertex
      hthirdNeSecond.symm
      (SimpleGraph.lineGraphCommonVertex_mem_right hfirstSecond)
      hthirdVertex⟩

/-- A located companion change emits the distinguished discrepancy on every
third edge completing its cubic junction. -/
theorem changedAdjacent_emits_on_thirdEdge
    (first second : transfer.SupportEdge)
    (hfirstSecond : collar.commonCore.lineGraph.Adj first.1 second.1)
    (hcompanion :
      (transfer.supportEdgeState first).companionColor ≠
        (transfer.supportEdgeState second).companionColor)
    {thirdEdge : collar.commonCore.edgeSet}
    (hfirstThird : collar.commonCore.lineGraph.Adj first.1 thirdEdge)
    (hsecondThird : collar.commonCore.lineGraph.Adj second.1 thirdEdge) :
    collar.sourceCommonColoring sourceEscape thirdEdge +
        collar.targetCommonColoring thirdEdge =
      crossFaceZeroColor transfer.coordinate := by
  exact thirdEdge_discrepancy_eq_zeroColor_of_companionColor_ne
    (collar.sourceCommonColoring sourceEscape)
    collar.targetCommonColoring
    (collar.sourceCommonColoring_isTait sourceEscape)
    collar.targetCommonColoring_isTait
    transfer.coordinate hfirstSecond hfirstThird hsecondThird
    (transfer.support first.1 first.2)
    (transfer.support second.1 second.2) hcompanion

/-- Every located companion change is resolved geometrically: its junction
is a source port, is a target port, or has a certified transverse edge carrying
the distinguished discrepancy. -/
theorem changedAdjacent_boundaryPort_or_transverseEmission
    (first second : transfer.SupportEdge)
    (hfirstSecond : collar.commonCore.lineGraph.Adj first.1 second.1)
    (hcompanion :
      (transfer.supportEdgeState first).companionColor ≠
        (transfer.supportEdgeState second).companionColor) :
    (∃ sourcePort : Fin 4,
        SimpleGraph.lineGraphCommonVertex hfirstSecond =
          collar.sourcePortInCommonCore sourcePort) ∨
      (∃ targetPort : Fin 4,
        SimpleGraph.lineGraphCommonVertex hfirstSecond =
          collar.targetPortInCommonCore targetPort) ∨
      ∃ thirdEdge : collar.commonCore.edgeSet,
        collar.commonCore.lineGraph.Adj first.1 thirdEdge ∧
          collar.commonCore.lineGraph.Adj second.1 thirdEdge ∧
          collar.sourceCommonColoring sourceEscape thirdEdge +
              collar.targetCommonColoring thirdEdge =
            crossFaceZeroColor transfer.coordinate := by
  by_cases hsource : ∃ sourcePort : Fin 4,
      SimpleGraph.lineGraphCommonVertex hfirstSecond =
        collar.sourcePortInCommonCore sourcePort
  · exact Or.inl hsource
  · by_cases htarget : ∃ targetPort : Fin 4,
        SimpleGraph.lineGraphCommonVertex hfirstSecond =
          collar.targetPortInCommonCore targetPort
    · exact Or.inr (Or.inl htarget)
    · have hsourceAvoid : ∀ sourcePort : Fin 4,
          SimpleGraph.lineGraphCommonVertex hfirstSecond ≠
            collar.sourcePortInCommonCore sourcePort := by
        intro sourcePort heq
        exact hsource ⟨sourcePort, heq⟩
      have htargetAvoid : ∀ targetPort : Fin 4,
          SimpleGraph.lineGraphCommonVertex hfirstSecond ≠
            collar.targetPortInCommonCore targetPort := by
        intro targetPort heq
        exact htarget ⟨targetPort, heq⟩
      rcases transfer.exists_thirdEdge_of_adjacent_of_commonVertex_not_ports
          first second hfirstSecond hsourceAvoid htargetAvoid with
        ⟨thirdEdge, hfirstThird, hsecondThird⟩
      exact Or.inr (Or.inr ⟨thirdEdge, hfirstThird, hsecondThird,
        transfer.changedAdjacent_emits_on_thirdEdge first second
          hfirstSecond hcompanion hfirstThird hsecondThird⟩)

/-- The fully resolved global split.  The singleton trail is a fixed
two-color pattern, or an explicitly located change occurs at a boundary port
or emits a certified transverse discrepancy in the cubic interior. -/
theorem fixedTwoColorPattern_or_exists_resolvedChangedAdjacent :
    (∃ companion : Color,
      companion ≠ 0 ∧
      companion ≠ crossFaceZeroColor transfer.coordinate ∧
      ∀ edge ∈ transfer.supportEdgeWord,
        (collar.sourceCommonColoring sourceEscape edge.1 =
              crossFaceZeroColor transfer.coordinate ∧
            collar.targetCommonColoring edge.1 = companion) ∨
          (collar.sourceCommonColoring sourceEscape edge.1 = companion ∧
            collar.targetCommonColoring edge.1 =
              crossFaceZeroColor transfer.coordinate)) ∨
      ∃ (before : List transfer.SupportEdge)
          (first second : transfer.SupportEdge)
          (after : List transfer.SupportEdge)
          (hfirstSecond : collar.commonCore.lineGraph.Adj first.1 second.1),
        transfer.supportEdgeWord =
            before ++ first :: second :: after ∧
          (transfer.supportEdgeState first).companionColor ≠
              (transfer.supportEdgeState second).companionColor ∧
          ((∃ sourcePort : Fin 4,
              SimpleGraph.lineGraphCommonVertex hfirstSecond =
                collar.sourcePortInCommonCore sourcePort) ∨
            (∃ targetPort : Fin 4,
              SimpleGraph.lineGraphCommonVertex hfirstSecond =
                collar.targetPortInCommonCore targetPort) ∨
            ∃ thirdEdge : collar.commonCore.edgeSet,
              collar.commonCore.lineGraph.Adj first.1 thirdEdge ∧
                collar.commonCore.lineGraph.Adj second.1 thirdEdge ∧
                collar.sourceCommonColoring sourceEscape thirdEdge +
                    collar.targetCommonColoring thirdEdge =
                  crossFaceZeroColor transfer.coordinate) := by
  rcases transfer.fixedTwoColorPattern_or_exists_changedAdjacent with
    hfixed | ⟨before, first, second, after, hword,
      hfirstSecond, hcompanion⟩
  · exact Or.inl hfixed
  · exact Or.inr ⟨before, first, second, after, hfirstSecond,
      hword, hcompanion,
      transfer.changedAdjacent_boundaryPort_or_transverseEmission
        first second hfirstSecond hcompanion⟩

end SingletonCompanionTransferPath

end IntrinsicShortTargetEscapeCollar

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
