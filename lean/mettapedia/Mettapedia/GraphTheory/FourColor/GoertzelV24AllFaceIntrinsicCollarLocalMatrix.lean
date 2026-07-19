import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCoordinates

/-! Exact local color-matrix formulas for the ten intrinsic-collar
correction coordinates. -/

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

namespace CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

namespace IntrinsicShortTargetEscapeCollar

/-- A chain on the exact common core extends by zero on every edge of the
source-target collar. -/
theorem commonCoreChainExtendZero_eq_zero_of_mem_intrinsicCollar
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (chain : collar.commonCore.edgeSet → Color)
    (edge : G.edgeSet) (hcollar : edge ∈ collar.intrinsicCollarEdgeFinset) :
    collar.commonCoreChainExtendZero chain edge = 0 := by
  apply inducedEdgeChainExtendZero_eq_zero_of_not_exists
  intro hexists
  rcases hexists with ⟨commonEdge, hcommon⟩
  have hsourceRetained : IsRetainedAmbientEdge collar.sourceData edge := by
    rw [← hcommon,
      ← commonCoreAmbientEdge_eq_inducedEdgeEmbedding collar commonEdge]
    exact collar.retainedEdgeToAmbientEdge_commonEdgeInSource_retainedBySource
      commonEdge
  have htargetRetained : IsRetainedAmbientEdge collar.targetData edge := by
    rw [← hcommon,
      ← commonCoreAmbientEdge_eq_inducedEdgeEmbedding collar commonEdge]
    exact collar.retainedEdgeToAmbientEdge_commonEdgeInSource_retainedByTarget
      commonEdge
  rw [intrinsicCollarEdgeFinset, Finset.mem_union] at hcollar
  rcases hcollar with hsource | htarget
  · exact ((mem_adjacentPairCollarEdgeFinset_iff collar.sourceData edge).1
      hsource) hsourceRetained
  · exact ((mem_adjacentPairCollarEdgeFinset_iff collar.targetData edge).1
      htarget) htargetRetained

/-- On the collar support, the completion correction is exactly the sum of
the source and target singleton-zero ambient completions. -/
theorem intrinsicCollarCompletionCorrection_eq_aligned_of_mem
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (edge : G.edgeSet) (hcollar : edge ∈ collar.intrinsicCollarEdgeFinset) :
    intrinsicCollarCompletionCorrection collar sourceEscape edge =
      alignedOneZeroDiscrepancy collar sourceEscape edge := by
  unfold intrinsicCollarCompletionCorrection
  change alignedOneZeroDiscrepancy collar sourceEscape edge +
      collar.commonCoreChainExtendZero
        (collar.commonDiscrepancy sourceEscape) edge =
    alignedOneZeroDiscrepancy collar sourceEscape edge
  rw [collar.commonCoreChainExtendZero_eq_zero_of_mem_intrinsicCollar
    _ edge hcollar, add_zero]

/-- Every fixed correction symbol is the aligned singleton-zero discrepancy
on its named collar edge. -/
theorem intrinsicCollarCorrectionWord_apply_eq_aligned
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
      alignedOneZeroDiscrepancy collar sourceEscape
        (collar.intrinsicCollarCoordinateEdge coordinate) := by
  rw [collar.intrinsicCollarCorrectionWord_apply,
    collar.intrinsicCollarCompletionCorrection_eq_aligned_of_mem
      sourceEscape _ (collar.intrinsicCollarCoordinateEdge_mem coordinate)]

/-- The source central coordinate is the bridge color supplied by the
target escape. -/
theorem intrinsicCollarCorrectionWord_sourceCentral
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    collar.intrinsicCollarCorrectionWord sourceEscape (Sum.inl none) =
      collar.sourceBridgeColor := by
  rw [collar.intrinsicCollarCorrectionWord_apply_eq_aligned]
  change alignedOneZeroDiscrepancy collar sourceEscape
      (centralEdge collar.sourceData) = collar.sourceBridgeColor
  unfold alignedOneZeroDiscrepancy
  rw [Pi.add_apply,
    oneZeroAmbientChain_central,
    oneZeroAmbientChain_retained collar.targetData
      collar.targetEscape.coloring (centralEdge collar.sourceData)
      collar.sourceCentralRetainedByTarget,
    zero_add]
  rfl

/-- A source boundary coordinate is the sum of the source's own canonical
boundary request and the same edge's color in the target escape. -/
theorem intrinsicCollarCorrectionWord_sourceBoundary
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (port : Fin 4) :
    collar.intrinsicCollarCorrectionWord sourceEscape (Sum.inl (some port)) =
      collar.sourceData.degreeTwoBoundaryData.colorWord
          sourceEscape.coloring port +
        collar.sourceBoundaryWord port := by
  rw [collar.intrinsicCollarCorrectionWord_apply_eq_aligned]
  change alignedOneZeroDiscrepancy collar sourceEscape
      (boundaryEdge collar.sourceData port) = _
  unfold alignedOneZeroDiscrepancy
  rw [Pi.add_apply,
    oneZeroAmbientChain_boundary,
    oneZeroAmbientChain_retained collar.targetData
      collar.targetEscape.coloring (boundaryEdge collar.sourceData port)
      (collar.sourceBoundaryRetainedByTarget port)]
  rfl

/-- The target central coordinate is the bridge color supplied by the
source escape. -/
theorem intrinsicCollarCorrectionWord_targetCentral
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    collar.intrinsicCollarCorrectionWord sourceEscape (Sum.inr none) =
      collar.targetBridgeColorInSource sourceEscape := by
  rw [collar.intrinsicCollarCorrectionWord_apply_eq_aligned]
  change alignedOneZeroDiscrepancy collar sourceEscape
      (centralEdge collar.targetData) =
    collar.targetBridgeColorInSource sourceEscape
  unfold alignedOneZeroDiscrepancy
  rw [Pi.add_apply,
    oneZeroAmbientChain_retained collar.sourceData sourceEscape.coloring
      (centralEdge collar.targetData) collar.targetCentralRetainedBySource,
    oneZeroAmbientChain_central,
    add_zero]
  rfl

/-- A target boundary coordinate is the sum of the edge's color in the
source escape and the target's own canonical boundary request. -/
theorem intrinsicCollarCorrectionWord_targetBoundary
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (port : Fin 4) :
    collar.intrinsicCollarCorrectionWord sourceEscape (Sum.inr (some port)) =
      collar.targetData.degreeTwoBoundaryData.colorWord
          collar.targetEscape.coloring port +
        collar.targetBoundaryWordInSource sourceEscape port := by
  rw [collar.intrinsicCollarCorrectionWord_apply_eq_aligned]
  change alignedOneZeroDiscrepancy collar sourceEscape
      (boundaryEdge collar.targetData port) = _
  unfold alignedOneZeroDiscrepancy
  rw [Pi.add_apply,
    oneZeroAmbientChain_retained collar.sourceData sourceEscape.coloring
      (boundaryEdge collar.targetData port)
      (collar.targetBoundaryRetainedBySource port),
    oneZeroAmbientChain_boundary]
  exact add_comm _ _

/-- One five-symbol half of a fixed intrinsic correction word. -/
abbrev IntrinsicCollarCorrectionHalfWord := Option (Fin 4) → Color

/-- Pure local formula for one half of the correction word. -/
def localCorrectionHalfWord
    (own cross : SquareBoundaryWord) (bridge : Color) :
    IntrinsicCollarCorrectionHalfWord
  | none => bridge
  | some port => own port + cross port

/-- Join source and target half words into the fixed ten-symbol word. -/
def correctionWordOfHalfWords
    (source target : IntrinsicCollarCorrectionHalfWord) :
    IntrinsicCollarCorrectionWord
  | Sum.inl coordinate => source coordinate
  | Sum.inr coordinate => target coordinate

/-- The source half determined by the two actual escape colorings. -/
def sourceLocalCorrectionHalfWord
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    IntrinsicCollarCorrectionHalfWord :=
  localCorrectionHalfWord
    (collar.sourceData.degreeTwoBoundaryData.colorWord sourceEscape.coloring)
    collar.sourceBoundaryWord collar.sourceBridgeColor

/-- The target half determined by the two actual escape colorings. -/
def targetLocalCorrectionHalfWord
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    IntrinsicCollarCorrectionHalfWord :=
  localCorrectionHalfWord
    (collar.targetData.degreeTwoBoundaryData.colorWord
      collar.targetEscape.coloring)
    (collar.targetBoundaryWordInSource sourceEscape)
    (collar.targetBridgeColorInSource sourceEscape)

/-- The entire fixed correction word is exactly the join of the two local
five-symbol matrix formulas. -/
theorem intrinsicCollarCorrectionWord_eq_correctionWordOfHalfWords
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    collar.intrinsicCollarCorrectionWord sourceEscape =
      correctionWordOfHalfWords
        (collar.sourceLocalCorrectionHalfWord sourceEscape)
        (collar.targetLocalCorrectionHalfWord sourceEscape) := by
  funext coordinate
  cases coordinate with
  | inl coordinate =>
      cases coordinate with
      | none =>
          exact collar.intrinsicCollarCorrectionWord_sourceCentral
            sourceEscape
      | some port =>
          exact collar.intrinsicCollarCorrectionWord_sourceBoundary
            sourceEscape port
  | inr coordinate =>
      cases coordinate with
      | none =>
          exact collar.intrinsicCollarCorrectionWord_targetCentral
            sourceEscape
      | some port =>
          exact collar.intrinsicCollarCorrectionWord_targetBoundary
            sourceEscape port

end IntrinsicShortTargetEscapeCollar

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
