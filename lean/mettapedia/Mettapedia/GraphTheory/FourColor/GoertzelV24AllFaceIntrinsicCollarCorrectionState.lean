import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceEscapeStateFacialCoordinates

/-! Finite collar states carrying the completion correction of an intrinsic
cross-base discrepancy. -/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
open GoertzelV24InducedChainExtension
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
open RotationOrderedFusionEscapeColorState

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

/-- The five ambient edges removed by an adjacent-pair deletion: its
central edge and its four ordered boundary edges. -/
def adjacentPairCollarEdgeFinset (data : AdjacentPairData G) :
    Finset G.edgeSet :=
  {centralEdge data} ∪ Finset.univ.image (boundaryEdge data)

omit [Fintype V] [DecidableRel G.Adj] in
/-- Membership in the explicit five-edge collar is exactly failure of
retention by the adjacent-pair deletion. -/
theorem mem_adjacentPairCollarEdgeFinset_iff
    (data : AdjacentPairData G) (edge : G.edgeSet) :
    edge ∈ adjacentPairCollarEdgeFinset data ↔
      ¬ IsRetainedAmbientEdge data edge := by
  rw [adjacentPairCollarEdgeFinset, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_image]
  constructor
  · rintro (rfl | ⟨port, _hport, rfl⟩)
    · exact (not_isRetainedAmbientEdge_iff data (centralEdge data)).2
        (Or.inl rfl)
    · exact (not_isRetainedAmbientEdge_iff data (boundaryEdge data port)).2
        (Or.inr ⟨port, rfl⟩)
  · intro hnot
    rcases (not_isRetainedAmbientEdge_iff data edge).1 hnot with
      hcentral | ⟨port, hport⟩
    · exact Or.inl (Subtype.ext hcentral)
    · exact Or.inr ⟨port, Finset.mem_univ port,
        Subtype.ext hport.symm⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- An adjacent-pair collar contains at most five ambient edges. -/
theorem card_adjacentPairCollarEdgeFinset_le_five
    (data : AdjacentPairData G) :
    (adjacentPairCollarEdgeFinset data).card ≤ 5 := by
  unfold adjacentPairCollarEdgeFinset
  calc
    ({centralEdge data} ∪
        Finset.univ.image (boundaryEdge data)).card ≤
        ({centralEdge data} : Finset G.edgeSet).card +
          (Finset.univ.image (boundaryEdge data)).card :=
      Finset.card_union_le _ _
    _ ≤ 1 + (Finset.univ : Finset (Fin 4)).card := by
      exact Nat.add_le_add_left Finset.card_image_le 1
    _ = 5 := by decide

namespace CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

namespace IntrinsicShortTargetEscapeCollar

/-- The union of the source and target adjacent-pair collars.  It is the
entire ambient complement of their exact common four-vertex deletion. -/
def intrinsicCollarEdgeFinset
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    Finset G.edgeSet :=
  adjacentPairCollarEdgeFinset collar.sourceData ∪
    adjacentPairCollarEdgeFinset collar.targetData

/-- The intrinsic completion collar has at most ten ambient edges. -/
theorem card_intrinsicCollarEdgeFinset_le_ten
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    collar.intrinsicCollarEdgeFinset.card ≤ 10 := by
  unfold intrinsicCollarEdgeFinset
  calc
    (adjacentPairCollarEdgeFinset collar.sourceData ∪
        adjacentPairCollarEdgeFinset collar.targetData).card ≤
      (adjacentPairCollarEdgeFinset collar.sourceData).card +
        (adjacentPairCollarEdgeFinset collar.targetData).card :=
      Finset.card_union_le _ _
    _ ≤ 5 + 5 := Nat.add_le_add
      (card_adjacentPairCollarEdgeFinset_le_five collar.sourceData)
      (card_adjacentPairCollarEdgeFinset_le_five collar.targetData)
    _ = 10 := rfl

/-- Outside the ten-edge collar, an ambient edge is retained by the source
adjacent-pair deletion. -/
theorem sourceData_isRetainedAmbientEdge_of_not_mem_intrinsicCollar
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (edge : G.edgeSet)
    (houtside : edge ∉ collar.intrinsicCollarEdgeFinset) :
    IsRetainedAmbientEdge collar.sourceData edge := by
  by_contra hnot
  apply houtside
  rw [intrinsicCollarEdgeFinset, Finset.mem_union]
  exact Or.inl
    ((mem_adjacentPairCollarEdgeFinset_iff collar.sourceData edge).2 hnot)

/-- Outside the ten-edge collar, an ambient edge is retained by the target
adjacent-pair deletion. -/
theorem targetData_isRetainedAmbientEdge_of_not_mem_intrinsicCollar
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (edge : G.edgeSet)
    (houtside : edge ∉ collar.intrinsicCollarEdgeFinset) :
    IsRetainedAmbientEdge collar.targetData edge := by
  by_contra hnot
  apply houtside
  rw [intrinsicCollarEdgeFinset, Finset.mem_union]
  exact Or.inr
    ((mem_adjacentPairCollarEdgeFinset_iff collar.targetData edge).2 hnot)

/-- Every edge outside the two adjacent-pair collars is the image of one
exact common-core edge. -/
theorem exists_commonCoreEdge_of_not_mem_intrinsicCollar
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (edge : G.edgeSet)
    (houtside : edge ∉ collar.intrinsicCollarEdgeFinset) :
    ∃ commonEdge : collar.commonCore.edgeSet,
      inducedEdgeEmbedding G collar.commonCorePredicate commonEdge = edge := by
  have hsource :=
    collar.sourceData_isRetainedAmbientEdge_of_not_mem_intrinsicCollar
      edge houtside
  have htarget :=
    collar.targetData_isRetainedAmbientEdge_of_not_mem_intrinsicCollar
      edge houtside
  rcases Sym2.mk_surjective (edge.1 : Sym2 V) with
    ⟨⟨left, right⟩, hedge⟩
  have hedge' : s(left, right) = (edge.1 : Sym2 V) := hedge
  have hleftMem : left ∈ (edge.1 : Sym2 V) := by
    rw [← hedge']
    exact Sym2.mem_mk_left _ _
  have hrightMem : right ∈ (edge.1 : Sym2 V) := by
    rw [← hedge']
    exact Sym2.mem_mk_right _ _
  have hleftSource := endpoints_mem_retainedVertexSet
    collar.sourceData edge hsource left hleftMem
  have hrightSource := endpoints_mem_retainedVertexSet
    collar.sourceData edge hsource right hrightMem
  have hleftTarget := endpoints_mem_retainedVertexSet
    collar.targetData edge htarget left hleftMem
  have hrightTarget := endpoints_mem_retainedVertexSet
    collar.targetData edge htarget right hrightMem
  have hleft : collar.commonCorePredicate left :=
    ⟨hleftSource.1, hleftSource.2, hleftTarget.1, hleftTarget.2⟩
  have hright : collar.commonCorePredicate right :=
    ⟨hrightSource.1, hrightSource.2, hrightTarget.1, hrightTarget.2⟩
  have hadj : G.Adj left right := by
    apply (SimpleGraph.mem_edgeSet G).mp
    rw [hedge']
    exact edge.2
  let commonEdge : collar.commonCore.edgeSet :=
    ⟨s(⟨left, hleft⟩, ⟨right, hright⟩), by
      apply (SimpleGraph.mem_edgeSet collar.commonCore).2
      exact hadj⟩
  refine ⟨commonEdge, ?_⟩
  apply Subtype.ext
  rw [inducedEdgeEmbedding_val]
  change Sym2.map Subtype.val
      s(⟨left, hleft⟩, ⟨right, hright⟩) = edge.1
  rw [Sym2.map_mk]
  exact hedge'

/-- The intrinsic completion correction vanishes on every ambient edge
outside the finite source-target collar. -/
theorem intrinsicCollarCompletionCorrection_eq_zero_of_not_mem
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (edge : G.edgeSet)
    (houtside : edge ∉ collar.intrinsicCollarEdgeFinset) :
    intrinsicCollarCompletionCorrection collar sourceEscape edge = 0 := by
  rcases collar.exists_commonCoreEdge_of_not_mem_intrinsicCollar
      edge houtside with ⟨commonEdge, hedge⟩
  rw [← hedge,
    ← commonCoreAmbientEdge_eq_inducedEdgeEmbedding collar commonEdge]
  exact intrinsicCollarCompletionCorrection_apply_commonCoreAmbientEdge
    collar sourceEscape commonEdge

/-- The finite state space containing a completion correction. -/
abbrev IntrinsicCollarCorrectionState
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :=
  collar.intrinsicCollarEdgeFinset → Color

/-- Restrict the intrinsic completion correction to its finite collar. -/
def intrinsicCollarCorrectionState
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    collar.IntrinsicCollarCorrectionState :=
  fun edge => intrinsicCollarCompletionCorrection
    collar sourceEscape edge.1

/-- Extend a finite collar state by zero to all ambient edges. -/
def intrinsicCollarCorrectionStateExtendZero
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (state : collar.IntrinsicCollarCorrectionState) :
    G.edgeSet → Color :=
  fun edge => if h : edge ∈ collar.intrinsicCollarEdgeFinset
    then state ⟨edge, h⟩ else 0

@[simp]
theorem intrinsicCollarCorrectionStateExtendZero_apply_mem
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (state : collar.IntrinsicCollarCorrectionState)
    (edge : G.edgeSet) (hedge : edge ∈ collar.intrinsicCollarEdgeFinset) :
    collar.intrinsicCollarCorrectionStateExtendZero state edge =
      state ⟨edge, hedge⟩ := by
  simp [intrinsicCollarCorrectionStateExtendZero, hedge]

@[simp]
theorem intrinsicCollarCorrectionStateExtendZero_apply_not_mem
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (state : collar.IntrinsicCollarCorrectionState)
    (edge : G.edgeSet) (hedge : edge ∉ collar.intrinsicCollarEdgeFinset) :
    collar.intrinsicCollarCorrectionStateExtendZero state edge = 0 := by
  simp [intrinsicCollarCorrectionStateExtendZero, hedge]

/-- Zero extension of the restricted state reconstructs the entire
completion correction exactly. -/
theorem intrinsicCollarCorrectionStateExtendZero_eq_completionCorrection
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    collar.intrinsicCollarCorrectionStateExtendZero
        (collar.intrinsicCollarCorrectionState sourceEscape) =
      intrinsicCollarCompletionCorrection collar sourceEscape := by
  funext edge
  by_cases hedge : edge ∈ collar.intrinsicCollarEdgeFinset
  · simp [intrinsicCollarCorrectionStateExtendZero,
      intrinsicCollarCorrectionState, hedge]
  · rw [collar.intrinsicCollarCorrectionStateExtendZero_apply_not_mem
      _ edge hedge]
    exact (collar.intrinsicCollarCompletionCorrection_eq_zero_of_not_mem
      sourceEscape edge hedge).symm

/-- The restricted finite collar state is nonzero. -/
theorem intrinsicCollarCorrectionState_ne_zero
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    collar.intrinsicCollarCorrectionState sourceEscape ≠ 0 := by
  intro hzero
  apply intrinsicCollarCompletionCorrection_ne_zeroChain collar sourceEscape
  rw [← collar.intrinsicCollarCorrectionStateExtendZero_eq_completionCorrection
    sourceEscape]
  funext edge
  by_cases hedge : edge ∈ collar.intrinsicCollarEdgeFinset
  · rw [collar.intrinsicCollarCorrectionStateExtendZero_apply_mem
      _ edge hedge]
    exact congrFun hzero ⟨edge, hedge⟩
  · exact collar.intrinsicCollarCorrectionStateExtendZero_apply_not_mem
      _ edge hedge

/-- The full unconstrained collar-state alphabet has at most `4^10`
elements. -/
theorem card_intrinsicCollarCorrectionState_le_1048576
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    Fintype.card collar.IntrinsicCollarCorrectionState ≤ 1048576 := by
  rw [Fintype.card_fun, Fintype.card_coe]
  have hcolor : Fintype.card Color = 4 := by decide
  rw [hcolor]
  calc
    4 ^ collar.intrinsicCollarEdgeFinset.card ≤ 4 ^ 10 :=
      Nat.pow_le_pow_right (by decide)
        collar.card_intrinsicCollarEdgeFinset_le_ten
    _ = 1048576 := by norm_num

/-- The finite collar state carries exactly the forced nonzero terminal
boundary state of the common-core discrepancy. -/
theorem vertexKirchhoffSum_correctionStateExtendZero_eq_boundaryState
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (terminal : collar.commonPortVertexFinset) :
    vertexKirchhoffSum G
        (collar.intrinsicCollarCorrectionStateExtendZero
          (collar.intrinsicCollarCorrectionState sourceEscape))
        terminal.1.1 =
      (collar.commonDiscrepancyBoundaryState sourceEscape).1 terminal := by
  rw [collar.intrinsicCollarCorrectionStateExtendZero_eq_completionCorrection]
  calc
    vertexKirchhoffSum G
        (intrinsicCollarCompletionCorrection collar sourceEscape)
        terminal.1.1 =
      vertexKirchhoffSum G
        (collar.commonCoreChainExtendZero
          (collar.commonDiscrepancy sourceEscape)) terminal.1.1 :=
      vertexKirchhoffSum_intrinsicCollarCompletionCorrection
        collar sourceEscape terminal.1.1
    _ = vertexKirchhoffSum collar.commonCore
        (collar.commonDiscrepancy sourceEscape) terminal.1 :=
      vertexKirchhoffSum_inducedEdgeChainExtendZero G
        collar.commonCorePredicate
        (collar.commonDiscrepancy sourceEscape) terminal.1
    _ = (collar.commonDiscrepancyBoundaryState sourceEscape).1 terminal :=
      rfl

/-- Consequently the ambient Kirchhoff boundary carried by the finite
collar state is a nonzero function on its at-most-eight terminal vertices. -/
theorem correctionState_terminalBoundary_ne_zero
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    (fun terminal : collar.commonPortVertexFinset =>
      vertexKirchhoffSum G
        (collar.intrinsicCollarCorrectionStateExtendZero
          (collar.intrinsicCollarCorrectionState sourceEscape))
        terminal.1.1) ≠ 0 := by
  intro hzero
  apply collar.commonDiscrepancyBoundaryState_ne_zero sourceEscape
  funext terminal
  rw [← collar.vertexKirchhoffSum_correctionStateExtendZero_eq_boundaryState
    sourceEscape terminal]
  exact congrFun hzero terminal

end IntrinsicShortTargetEscapeCollar

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
