import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicShortCommonBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoDefectParity

/-! The two-by-two local completion matrix at an intrinsic singleton-star
reentry. -/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24DualPathTransversal
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24MinimalFaceIntersections
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

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

/-- The target central edge survives the source adjacent-pair deletion. -/
theorem targetCentralRetainedBySource
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    IsRetainedAmbientEdge collar.sourceData
      (centralEdge collar.targetData) := by
  rw [collar.targetCentral_eq]
  exact collar.targetRetainedBySource

/-- Every target boundary edge survives the source adjacent-pair deletion. -/
theorem targetBoundaryRetainedBySource
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (port : Fin 4) :
    IsRetainedAmbientEdge collar.sourceData
      (boundaryEdge collar.targetData port) := by
  apply (isRetainedAmbientEdge_iff_endpoints_mem_retainedVertexSet
    collar.sourceData (boundaryEdge collar.targetData port)).2
  intro vertex hvertex
  rw [boundaryEdge_val, boundaryEdgeValue_eq] at hvertex
  rcases (Sym2.mem_iff.mp hvertex) with hdeleted | hport
  · subst vertex
    fin_cases port
    · simpa [boundaryDeletedVertex] using
        collar.targetFirst_mem_sourceRetainedVertexSet
    · simpa [boundaryDeletedVertex] using
        collar.targetFirst_mem_sourceRetainedVertexSet
    · simpa [boundaryDeletedVertex] using
        collar.targetSecond_mem_sourceRetainedVertexSet
    · simpa [boundaryDeletedVertex] using
        collar.targetSecond_mem_sourceRetainedVertexSet
  · subst vertex
    exact collar.targetPort_mem_sourceRetainedVertexSet port

/-- The target central edge as an edge of the source-pair deletion. -/
def targetCentralInSource
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
      collar.sourceData.secondVertex).edgeSet :=
  ambientEdgeToRetainedEdge collar.sourceData
    (centralEdge collar.targetData) collar.targetCentralRetainedBySource

/-- A target boundary edge as an edge of the source-pair deletion. -/
def targetBoundaryInSource
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (port : Fin 4) :
    (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
      collar.sourceData.secondVertex).edgeSet :=
  ambientEdgeToRetainedEdge collar.sourceData
    (boundaryEdge collar.targetData port)
      (collar.targetBoundaryRetainedBySource port)

/-- The target collar word read in a source escape coloring. -/
def targetBoundaryWordInSource
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    SquareBoundaryWord :=
  fun port => sourceEscape.coloring
    (collar.targetBoundaryInSource port)

/-- The target bridge color read in a source escape coloring. -/
def targetBridgeColorInSource
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) : Color :=
  sourceEscape.coloring collar.targetCentralInSource

theorem targetCentralInSource_adj_targetBoundaryInSource
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (port : Fin 4) :
    (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
      collar.sourceData.secondVertex).lineGraph.Adj
        collar.targetCentralInSource
        (collar.targetBoundaryInSource port) := by
  exact ambientEdgeToRetainedEdge_adj collar.sourceData
    (centralEdge collar.targetData) (boundaryEdge collar.targetData port)
      collar.targetCentralRetainedBySource
        (collar.targetBoundaryRetainedBySource port)
          (centralEdge_adj_boundaryEdge collar.targetData port)

theorem targetBoundaryInSource_zero_adj_one
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
      collar.sourceData.secondVertex).lineGraph.Adj
        (collar.targetBoundaryInSource 0)
        (collar.targetBoundaryInSource 1) := by
  exact ambientEdgeToRetainedEdge_adj collar.sourceData
    (boundaryEdge collar.targetData 0) (boundaryEdge collar.targetData 1)
      (collar.targetBoundaryRetainedBySource 0)
        (collar.targetBoundaryRetainedBySource 1)
          (boundaryEdge_zero_adj_one collar.targetData)

theorem targetBoundaryInSource_two_adj_three
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
      collar.sourceData.secondVertex).lineGraph.Adj
        (collar.targetBoundaryInSource 2)
        (collar.targetBoundaryInSource 3) := by
  exact ambientEdgeToRetainedEdge_adj collar.sourceData
    (boundaryEdge collar.targetData 2) (boundaryEdge collar.targetData 3)
      (collar.targetBoundaryRetainedBySource 2)
        (collar.targetBoundaryRetainedBySource 3)
          (boundaryEdge_two_adj_three collar.targetData)

/-- A source escape coloring gives a literal accepted local extension across
the target adjacent-pair collar. -/
theorem targetBridgeExtensionInSource
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    IsTwoVertexBridgeExtension
      (collar.targetBoundaryWordInSource sourceEscape)
      (collar.targetBridgeColorInSource sourceEscape) := by
  constructor
  · refine ⟨sourceEscape.isTait _, sourceEscape.isTait _,
      sourceEscape.isTait _, ?_, ?_, ?_⟩
    · exact sourceEscape.coloring.valid
        collar.targetBoundaryInSource_zero_adj_one
    · exact (sourceEscape.coloring.valid
        (collar.targetCentralInSource_adj_targetBoundaryInSource 0)).symm
    · exact (sourceEscape.coloring.valid
        (collar.targetCentralInSource_adj_targetBoundaryInSource 1)).symm
  · refine ⟨sourceEscape.isTait _, sourceEscape.isTait _,
      sourceEscape.isTait _, ?_, ?_, ?_⟩
    · exact sourceEscape.coloring.valid
        collar.targetBoundaryInSource_two_adj_three
    · exact (sourceEscape.coloring.valid
        (collar.targetCentralInSource_adj_targetBoundaryInSource 2)).symm
    · exact (sourceEscape.coloring.valid
        (collar.targetCentralInSource_adj_targetBoundaryInSource 3)).symm

/-- The target collar is locally extendable when read in a source escape. -/
theorem targetBoundaryWordInSource_extendableClass
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    (collar.targetBoundaryWordInSource sourceEscape).Nonzero ∧
      ((collar.targetBoundaryWordInSource sourceEscape).Adjacent12_30 ∨
        (collar.targetBoundaryWordInSource sourceEscape).OppositePairs) := by
  have hmem : collar.targetBridgeColorInSource sourceEscape ∈
      twoVertexBridgeExtensions
        (collar.targetBoundaryWordInSource sourceEscape) :=
    mem_twoVertexBridgeExtensions_iff.mpr
      (collar.targetBridgeExtensionInSource sourceEscape)
  have hpositive : 0 <
      (twoVertexBridgeExtensions
        (collar.targetBoundaryWordInSource sourceEscape)).card :=
    Finset.card_pos.mpr
      ⟨collar.targetBridgeColorInSource sourceEscape, hmem⟩
  rw [twoVertexBridgeExtension_card] at hpositive
  by_cases hclass :
      (collar.targetBoundaryWordInSource sourceEscape).Nonzero ∧
        ((collar.targetBoundaryWordInSource sourceEscape).Adjacent12_30 ∨
          (collar.targetBoundaryWordInSource sourceEscape).OppositePairs)
  · exact hclass
  · simp [hclass] at hpositive

/-- The source escape and target escape give the complementary diagonal
completion matrix: each own collar is the canonical nonextendable class,
while each opposite collar has a certified local bridge extension. -/
theorem completionClassMatrix
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    SquareBoundaryWord.Adjacent01_23
        (collar.sourceData.degreeTwoBoundaryData.colorWord
          sourceEscape.coloring) ∧
      (collar.targetBoundaryWordInSource sourceEscape).Nonzero ∧
      ((collar.targetBoundaryWordInSource sourceEscape).Adjacent12_30 ∨
        (collar.targetBoundaryWordInSource sourceEscape).OppositePairs) ∧
      SquareBoundaryWord.Adjacent01_23
        (collar.targetData.degreeTwoBoundaryData.colorWord
          collar.targetEscape.coloring) ∧
      collar.sourceBoundaryWord.Nonzero ∧
      (collar.sourceBoundaryWord.Adjacent12_30 ∨
        collar.sourceBoundaryWord.OppositePairs) := by
  rcases collar.targetBoundaryWordInSource_extendableClass sourceEscape with
    ⟨htargetNonzero, htargetClass⟩
  rcases collar.sourceBoundaryWord_extendableClass with
    ⟨hsourceNonzero, hsourceClass⟩
  exact ⟨sourceEscape.boundary_adjacent01_23,
    htargetNonzero, htargetClass,
    collar.targetEscape.boundary_adjacent01_23,
    hsourceNonzero, hsourceClass⟩

/-- The source escape restricted to the exact common core. -/
def sourceCommonColoring
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    collar.commonCore.EdgeColoring Color :=
  firstDeletionCommonCoreColoring
    (third := collar.targetData.firstVertex)
    (fourth := collar.targetData.secondVertex)
    sourceEscape.coloring

/-- The target escape restricted to the exact common core. -/
def targetCommonColoring
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    collar.commonCore.EdgeColoring Color :=
  secondDeletionCommonCoreColoring
    (first := collar.sourceData.firstVertex)
    (second := collar.sourceData.secondVertex)
    collar.targetEscape.coloring

/-- Restriction preserves the source Tait condition. -/
theorem sourceCommonColoring_isTait
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    IsTaitEdgeColoring collar.commonCore
      (collar.sourceCommonColoring sourceEscape) := by
  intro edge
  exact sourceEscape.isTait _

/-- Restriction preserves the target Tait condition. -/
theorem targetCommonColoring_isTait
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    IsTaitEdgeColoring collar.commonCore collar.targetCommonColoring := by
  intro edge
  exact collar.targetEscape.isTait _

/-- The source common-core restriction obeys Kirchhoff's law away from the
two four-port images. -/
theorem vertexKirchhoffSum_sourceCommonColoring_eq_zero_of_not_ports
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (vertex : collar.commonCoreVertex)
    (hsource : ∀ port : Fin 4,
      vertex ≠ collar.sourcePortInCommonCore port)
    (htarget : ∀ port : Fin 4,
      vertex ≠ collar.targetPortInCommonCore port) :
    vertexKirchhoffSum collar.commonCore
      (collar.sourceCommonColoring sourceEscape) vertex = 0 := by
  apply GoertzelV24TwoDefectParity.vertexKirchhoffSum_eq_zero_of_card_three
    (collar.sourceCommonColoring sourceEscape)
      (collar.sourceCommonColoring_isTait sourceEscape)
  exact collar.card_incidentEdgeFinset_commonCore_eq_three_of_not_ports
    vertex hsource htarget

/-- The target common-core restriction obeys Kirchhoff's law away from the
same two four-port images. -/
theorem vertexKirchhoffSum_targetCommonColoring_eq_zero_of_not_ports
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (vertex : collar.commonCoreVertex)
    (hsource : ∀ port : Fin 4,
      vertex ≠ collar.sourcePortInCommonCore port)
    (htarget : ∀ port : Fin 4,
      vertex ≠ collar.targetPortInCommonCore port) :
    vertexKirchhoffSum collar.commonCore collar.targetCommonColoring
      vertex = 0 := by
  apply GoertzelV24TwoDefectParity.vertexKirchhoffSum_eq_zero_of_card_three
    collar.targetCommonColoring collar.targetCommonColoring_isTait
  exact collar.card_incidentEdgeFinset_commonCore_eq_three_of_not_ports
    vertex hsource htarget

end IntrinsicShortTargetEscapeCollar

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
