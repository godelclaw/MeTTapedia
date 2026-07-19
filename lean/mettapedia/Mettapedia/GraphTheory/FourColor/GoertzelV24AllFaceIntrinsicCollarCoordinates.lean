import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCorrectionState

/-! Fixed coordinates for the two five-edge collars supporting an intrinsic
cross-base completion correction. -/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
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

/-- A fixed coordinate for the five edges removed by one adjacent-pair
deletion: `none` is the central edge and `some port` is a boundary edge. -/
def adjacentPairCollarCoordinateEdge (data : AdjacentPairData G) :
    Option (Fin 4) → G.edgeSet
  | none => centralEdge data
  | some port => boundaryEdge data port

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The five fixed collar coordinates name distinct ambient edges. -/
theorem adjacentPairCollarCoordinateEdge_injective
    (data : AdjacentPairData G) :
    Function.Injective (adjacentPairCollarCoordinateEdge data) := by
  intro first second hedge
  cases first with
  | none =>
      cases second with
      | none => rfl
      | some port =>
          exfalso
          exact (centralEdgeValue_ne_boundaryEdgeValue data port)
            (congrArg Subtype.val hedge)
  | some firstPort =>
      cases second with
      | none =>
          exfalso
          exact (centralEdgeValue_ne_boundaryEdgeValue data firstPort)
            (congrArg Subtype.val hedge).symm
      | some secondPort =>
          exact congrArg some
            (boundaryEdgeValue_injective data
              (congrArg Subtype.val hedge))

omit [Fintype V] [DecidableRel G.Adj] in
/-- Every fixed adjacent-pair coordinate belongs to the explicit collar. -/
theorem adjacentPairCollarCoordinateEdge_mem
    (data : AdjacentPairData G) (coordinate : Option (Fin 4)) :
    adjacentPairCollarCoordinateEdge data coordinate ∈
      adjacentPairCollarEdgeFinset data := by
  cases coordinate with
  | none =>
      simp [adjacentPairCollarCoordinateEdge,
        adjacentPairCollarEdgeFinset]
  | some port =>
      simp [adjacentPairCollarCoordinateEdge,
        adjacentPairCollarEdgeFinset]

/-- The fixed five coordinates enumerate the adjacent-pair collar exactly. -/
def adjacentPairCollarCoordinateEquiv (data : AdjacentPairData G) :
    Option (Fin 4) ≃ adjacentPairCollarEdgeFinset data :=
  Equiv.ofBijective
    (fun coordinate =>
      ⟨adjacentPairCollarCoordinateEdge data coordinate,
        adjacentPairCollarCoordinateEdge_mem data coordinate⟩)
    ⟨by
      intro first second hedge
      apply adjacentPairCollarCoordinateEdge_injective data
      exact congrArg Subtype.val hedge,
    by
      intro edge
      rcases edge with ⟨edge, hedge⟩
      rw [adjacentPairCollarEdgeFinset, Finset.mem_union,
        Finset.mem_singleton, Finset.mem_image] at hedge
      rcases hedge with hcentral | ⟨port, _hport, hboundary⟩
      · subst edge
        exact ⟨none, rfl⟩
      · subst edge
        exact ⟨some port, rfl⟩⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- An adjacent-pair collar has exactly five edges. -/
theorem card_adjacentPairCollarEdgeFinset_eq_five
    (data : AdjacentPairData G) :
    (adjacentPairCollarEdgeFinset data).card = 5 := by
  rw [← Fintype.card_coe]
  calc
    Fintype.card (adjacentPairCollarEdgeFinset data) =
        Fintype.card (Option (Fin 4)) :=
      Fintype.card_congr (adjacentPairCollarCoordinateEquiv data).symm
    _ = 5 := by decide

namespace CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

namespace IntrinsicShortTargetEscapeCollar

/-- The source and target five-edge collars are disjoint. Reciprocal
retention is the exact graph-theoretic reason. -/
theorem disjoint_source_target_adjacentPairCollarEdgeFinset
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    Disjoint (adjacentPairCollarEdgeFinset collar.sourceData)
      (adjacentPairCollarEdgeFinset collar.targetData) := by
  rw [Finset.disjoint_left]
  intro edge hsource htarget
  have hnotRetained : ¬ IsRetainedAmbientEdge collar.sourceData edge :=
    (mem_adjacentPairCollarEdgeFinset_iff collar.sourceData edge).1 hsource
  apply hnotRetained
  rw [adjacentPairCollarEdgeFinset, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_image] at htarget
  rcases htarget with hcentral | ⟨port, _hport, hboundary⟩
  · subst edge
    exact collar.targetCentralRetainedBySource
  · subst edge
    exact collar.targetBoundaryRetainedBySource port

/-- A fixed coordinate for the intrinsic collar union, retaining which of
the two adjacent-pair collars supplied the edge. -/
abbrev IntrinsicCollarCoordinate :=
  Sum (Option (Fin 4)) (Option (Fin 4))

/-- Interpret a fixed intrinsic-collar coordinate as an ambient edge. -/
def intrinsicCollarCoordinateEdge
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    IntrinsicCollarCoordinate → G.edgeSet
  | Sum.inl coordinate =>
      adjacentPairCollarCoordinateEdge collar.sourceData coordinate
  | Sum.inr coordinate =>
      adjacentPairCollarCoordinateEdge collar.targetData coordinate

/-- Every fixed intrinsic coordinate belongs to the ten-edge collar union. -/
theorem intrinsicCollarCoordinateEdge_mem
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (coordinate : IntrinsicCollarCoordinate) :
    collar.intrinsicCollarCoordinateEdge coordinate ∈
      collar.intrinsicCollarEdgeFinset := by
  cases coordinate with
  | inl coordinate =>
      exact Finset.mem_union_left _
        (adjacentPairCollarCoordinateEdge_mem collar.sourceData coordinate)
  | inr coordinate =>
      exact Finset.mem_union_right _
        (adjacentPairCollarCoordinateEdge_mem collar.targetData coordinate)

/-- The ten fixed intrinsic-collar coordinates name distinct ambient edges. -/
theorem intrinsicCollarCoordinateEdge_injective
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    Function.Injective collar.intrinsicCollarCoordinateEdge := by
  intro first second hedge
  cases first with
  | inl firstCoordinate =>
      cases second with
      | inl secondCoordinate =>
          exact congrArg Sum.inl
            (adjacentPairCollarCoordinateEdge_injective collar.sourceData
              hedge)
      | inr secondCoordinate =>
          exfalso
          change adjacentPairCollarCoordinateEdge collar.sourceData
              firstCoordinate =
            adjacentPairCollarCoordinateEdge collar.targetData
              secondCoordinate at hedge
          have hsource :=
            adjacentPairCollarCoordinateEdge_mem collar.sourceData
              firstCoordinate
          have htarget :=
            adjacentPairCollarCoordinateEdge_mem collar.targetData
              secondCoordinate
          rw [← hedge] at htarget
          exact (Finset.disjoint_left.mp
            collar.disjoint_source_target_adjacentPairCollarEdgeFinset)
              hsource htarget
  | inr firstCoordinate =>
      cases second with
      | inl secondCoordinate =>
          exfalso
          change adjacentPairCollarCoordinateEdge collar.targetData
              firstCoordinate =
            adjacentPairCollarCoordinateEdge collar.sourceData
              secondCoordinate at hedge
          have htarget :=
            adjacentPairCollarCoordinateEdge_mem collar.targetData
              firstCoordinate
          have hsource :=
            adjacentPairCollarCoordinateEdge_mem collar.sourceData
              secondCoordinate
          rw [hedge] at htarget
          exact (Finset.disjoint_left.mp
            collar.disjoint_source_target_adjacentPairCollarEdgeFinset)
              hsource htarget
      | inr secondCoordinate =>
          exact congrArg Sum.inr
            (adjacentPairCollarCoordinateEdge_injective collar.targetData
              hedge)

/-- The fixed ten coordinates enumerate the intrinsic collar union exactly. -/
def intrinsicCollarCoordinateEquiv
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    IntrinsicCollarCoordinate ≃ collar.intrinsicCollarEdgeFinset :=
  Equiv.ofBijective
    (fun coordinate =>
      ⟨collar.intrinsicCollarCoordinateEdge coordinate,
        collar.intrinsicCollarCoordinateEdge_mem coordinate⟩)
    ⟨by
      intro first second hedge
      apply collar.intrinsicCollarCoordinateEdge_injective
      exact congrArg Subtype.val hedge,
    by
      intro edge
      rcases edge with ⟨edge, hedge⟩
      rw [intrinsicCollarEdgeFinset, Finset.mem_union] at hedge
      rcases hedge with hsource | htarget
      · rcases (adjacentPairCollarCoordinateEquiv
          collar.sourceData).surjective
          ⟨edge, hsource⟩ with ⟨coordinate, hcoordinate⟩
        refine ⟨Sum.inl coordinate, ?_⟩
        apply Subtype.ext
        change adjacentPairCollarCoordinateEdge collar.sourceData
          coordinate = edge
        exact congrArg Subtype.val hcoordinate
      · rcases (adjacentPairCollarCoordinateEquiv
          collar.targetData).surjective
          ⟨edge, htarget⟩ with ⟨coordinate, hcoordinate⟩
        refine ⟨Sum.inr coordinate, ?_⟩
        apply Subtype.ext
        change adjacentPairCollarCoordinateEdge collar.targetData
          coordinate = edge
        exact congrArg Subtype.val hcoordinate⟩

/-- The intrinsic collar union has exactly ten edges. -/
theorem card_intrinsicCollarEdgeFinset_eq_ten
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    collar.intrinsicCollarEdgeFinset.card = 10 := by
  rw [← Fintype.card_coe]
  calc
    Fintype.card collar.intrinsicCollarEdgeFinset =
        Fintype.card IntrinsicCollarCoordinate :=
      Fintype.card_congr collar.intrinsicCollarCoordinateEquiv.symm
    _ = 10 := by decide

/-- A correction word on the fixed source-target collar coordinates. -/
abbrev IntrinsicCollarCorrectionWord := IntrinsicCollarCoordinate → Color

/-- Reindex finite collar states by the fixed ten coordinates. -/
def intrinsicCollarStateEquivCorrectionWord
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    collar.IntrinsicCollarCorrectionState ≃ IntrinsicCollarCorrectionWord :=
  collar.intrinsicCollarCoordinateEquiv.symm.arrowCongr (Equiv.refl Color)

/-- Reindexing a state reads it at the ambient edge named by the fixed
coordinate. -/
@[simp]
theorem intrinsicCollarStateEquivCorrectionWord_apply
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (state : collar.IntrinsicCollarCorrectionState)
    (coordinate : IntrinsicCollarCoordinate) :
    collar.intrinsicCollarStateEquivCorrectionWord state coordinate =
      state (collar.intrinsicCollarCoordinateEquiv coordinate) := by
  rfl

/-- The intrinsic completion correction as a word on ten fixed coordinates. -/
def intrinsicCollarCorrectionWord
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    IntrinsicCollarCorrectionWord :=
  collar.intrinsicCollarStateEquivCorrectionWord
    (collar.intrinsicCollarCorrectionState sourceEscape)

/-- Each symbol of the fixed word is the ambient completion correction on
the edge named by that coordinate. -/
@[simp]
theorem intrinsicCollarCorrectionWord_apply
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (coordinate : IntrinsicCollarCoordinate) :
    collar.intrinsicCollarCorrectionWord sourceEscape coordinate =
      intrinsicCollarCompletionCorrection collar sourceEscape
        (collar.intrinsicCollarCoordinateEdge coordinate) := by
  rfl

/-- Extend a fixed ten-coordinate correction word by zero to the ambient
edge set. -/
def intrinsicCollarCorrectionWordExtendZero
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (word : IntrinsicCollarCorrectionWord) : G.edgeSet → Color :=
  collar.intrinsicCollarCorrectionStateExtendZero
    (collar.intrinsicCollarStateEquivCorrectionWord.symm word)

/-- Zero extension of the fixed correction word reconstructs the entire
ambient completion correction exactly. -/
theorem intrinsicCollarCorrectionWordExtendZero_eq_completionCorrection
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    collar.intrinsicCollarCorrectionWordExtendZero
        (collar.intrinsicCollarCorrectionWord sourceEscape) =
      intrinsicCollarCompletionCorrection collar sourceEscape := by
  rw [intrinsicCollarCorrectionWordExtendZero,
    intrinsicCollarCorrectionWord, Equiv.symm_apply_apply]
  exact collar.intrinsicCollarCorrectionStateExtendZero_eq_completionCorrection
    sourceEscape

/-- The fixed correction word retains the exact nonzero terminal boundary
of the common-core discrepancy. -/
theorem vertexKirchhoffSum_correctionWordExtendZero_eq_boundaryState
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
        (collar.intrinsicCollarCorrectionWordExtendZero
          (collar.intrinsicCollarCorrectionWord sourceEscape))
        terminal.1.1 =
      (collar.commonDiscrepancyBoundaryState sourceEscape).1 terminal := by
  rw [collar.intrinsicCollarCorrectionWordExtendZero_eq_completionCorrection,
    ← collar.intrinsicCollarCorrectionStateExtendZero_eq_completionCorrection
      sourceEscape]
  exact collar.vertexKirchhoffSum_correctionStateExtendZero_eq_boundaryState
    sourceEscape terminal

/-- The fixed correction word is nonzero. -/
theorem intrinsicCollarCorrectionWord_ne_zero
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    collar.intrinsicCollarCorrectionWord sourceEscape ≠ 0 := by
  exact (collar.intrinsicCollarStateEquivCorrectionWord.injective.ne_iff).2
    (collar.intrinsicCollarCorrectionState_ne_zero sourceEscape)

/-- The fixed correction-word alphabet has exactly `4^10` elements. -/
theorem card_intrinsicCollarCorrectionWord_eq_1048576 :
    Fintype.card IntrinsicCollarCorrectionWord = 1048576 := by
  rw [Fintype.card_fun]
  have hcoordinate : Fintype.card IntrinsicCollarCoordinate = 10 := by decide
  have hcolor : Fintype.card Color = 4 := by decide
  rw [hcoordinate, hcolor]
  norm_num

/-- Consequently the original collar-state type also has exactly `4^10`
elements, not merely an upper bound. -/
theorem card_intrinsicCollarCorrectionState_eq_1048576
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    Fintype.card collar.IntrinsicCollarCorrectionState = 1048576 := by
  calc
    Fintype.card collar.IntrinsicCollarCorrectionState =
        Fintype.card IntrinsicCollarCorrectionWord :=
      Fintype.card_congr collar.intrinsicCollarStateEquivCorrectionWord
    _ = 1048576 := card_intrinsicCollarCorrectionWord_eq_1048576

end IntrinsicShortTargetEscapeCollar

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
