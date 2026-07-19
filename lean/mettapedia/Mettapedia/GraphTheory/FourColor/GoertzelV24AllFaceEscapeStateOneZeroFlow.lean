import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientOneZeroFlow
import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceEscapeStateMonodromy
import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicShortDiscrepancyQuotient

/-! Canonical singleton-zero ambient flows attached to finite all-face
escape states. -/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24InducedChainExtension
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}

namespace RotationOrderedFusionEscapeColorState

/-- The coloring stored by an admissible finite state is an actual Tait
coloring of its exact adjacent-pair deletion. -/
theorem AdmissibleState.escapeColoring_isTait
    (state :
      AdmissibleState (graphData := graphData) (minimal := minimal)) :
    IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G
        (RecoveredRotationOrderedData graphData minimal
          state.1.1).firstVertex
        (RecoveredRotationOrderedData graphData minimal
          state.1.1).secondVertex)
      state.1.2 := by
  rcases state.2 with
    ⟨_normal, _outcome, escape, hcolor⟩
  rw [hcolor]
  exact escape.isTait

/-- Its ordered boundary word is the canonical adjacent `01|23` escape
class. -/
theorem AdmissibleState.escapeColoring_boundary_adjacent01_23
    (state :
      AdmissibleState (graphData := graphData) (minimal := minimal)) :
    SquareBoundaryWord.Adjacent01_23
      ((RecoveredRotationOrderedData graphData minimal
          state.1.1).degreeTwoBoundaryData.colorWord state.1.2) := by
  rcases state.2 with
    ⟨_normal, _outcome, escape, hcolor⟩
  rw [hcolor]
  exact escape.boundary_adjacent01_23

/-- Complete the stored deletion coloring canonically by assigning zero to
the restored central edge and the requested colors to its four boundary
edges. -/
def AdmissibleState.oneZeroAmbientFlow
    (state :
      AdmissibleState (graphData := graphData) (minimal := minimal)) :
    G.edgeSet → Color :=
  oneZeroAmbientChain
    (RecoveredRotationOrderedData graphData minimal state.1.1) state.1.2

/-- Every admissible state's canonical completion is a CDL-good ambient
graph flow. -/
theorem AdmissibleState.oneZeroAmbientFlow_isCDLGoodFlow
    (state :
      AdmissibleState (graphData := graphData) (minimal := minimal)) :
    IsCDLGoodFlow G state.oneZeroAmbientFlow := by
  let data := RecoveredRotationOrderedData graphData minimal state.1.1
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
        IsTaitEdgeColoring G ambientColoring :=
    graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
      graphData minimal
  exact oneZeroAmbientChain_isCDLGoodFlow_of_not_taitColorable
    data hcubic hnotColorable state.1.2 state.escapeColoring_isTait

/-- The central edge is the unique zero of the canonical ambient flow. -/
theorem AdmissibleState.zeroEdgeFinset_oneZeroAmbientFlow
    (state :
      AdmissibleState (graphData := graphData) (minimal := minimal)) :
    zeroEdgeFinset G state.oneZeroAmbientFlow =
      {centralEdge
        (RecoveredRotationOrderedData graphData minimal state.1.1)} := by
  apply zeroEdgeFinset_oneZeroAmbientChain
  · exact incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  · exact state.escapeColoring_isTait

@[simp]
theorem AdmissibleState.oneZeroAmbientFlow_central
    (state :
      AdmissibleState (graphData := graphData) (minimal := minimal)) :
    state.oneZeroAmbientFlow
        (centralEdge
          (RecoveredRotationOrderedData graphData minimal state.1.1)) = 0 :=
  oneZeroAmbientChain_central _ _

/-- The two central edges of a reentry are distinct as undirected ambient
edges. -/
theorem AdmissibleReentry.centralEdge_ne
    {source target :
      AdmissibleState (graphData := graphData) (minimal := minimal)}
    (step : AdmissibleReentry source target) :
    centralEdge
        (RecoveredRotationOrderedData graphData minimal source.1.1) ≠
      centralEdge
        (RecoveredRotationOrderedData graphData minimal target.1.1) := by
  rcases step with
    ⟨_sourceNormal, _sourceLaunch, _sourceEscape, _hsourceColor,
      targetEdge, hne, htarget, _geometry, _targetNormal, _targetOutcome,
      _targetEscape, _htargetColor⟩
  exact fun heq => hne (heq.trans htarget)

/-- The difference of the canonical singleton-zero flows at the two ends of
a stateful reentry. -/
def oneZeroReentryDiscrepancy
    (source target :
      AdmissibleState (graphData := graphData) (minimal := minimal)) :
    G.edgeSet → Color :=
  source.oneZeroAmbientFlow + target.oneZeroAmbientFlow

/-- Every reentry carries a nonzero canonical flow discrepancy: at the
source central edge the source flow vanishes and the target flow does not. -/
theorem AdmissibleReentry.oneZeroReentryDiscrepancy_ne_zeroChain
    {source target :
      AdmissibleState (graphData := graphData) (minimal := minimal)}
    (step : AdmissibleReentry source target) :
    oneZeroReentryDiscrepancy source target ≠ zeroChain := by
  let sourceCentral := centralEdge
    (RecoveredRotationOrderedData graphData minimal source.1.1)
  have htargetNonzero : target.oneZeroAmbientFlow sourceCentral ≠ 0 := by
    apply oneZeroAmbientChain_ne_zero_of_ne_central
    · exact incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
        graphData minimal.spherical.cubic
    · exact target.escapeColoring_isTait
    · exact step.centralEdge_ne
  intro hzero
  have hvalue := congrFun hzero sourceCentral
  change source.oneZeroAmbientFlow sourceCentral +
      target.oneZeroAmbientFlow sourceCentral = 0 at hvalue
  rw [show source.oneZeroAmbientFlow sourceCentral = 0 from
    source.oneZeroAmbientFlow_central, zero_add] at hvalue
  exact htargetNonzero hvalue

/-- The canonical discrepancy of every reentry is itself an ambient graph
flow. -/
theorem oneZeroReentryDiscrepancy_isGraphFlow
    (source target :
      AdmissibleState (graphData := graphData) (minimal := minimal)) :
    IsGraphFlow G (oneZeroReentryDiscrepancy source target) := by
  exact source.oneZeroAmbientFlow_isCDLGoodFlow.1.add
    target.oneZeroAmbientFlow_isCDLGoodFlow.1

/-- On the spherical ambient graph, the canonical difference between any
two admissible states has two exact facial-boundary coefficient vectors. -/
theorem exists_orbitFaceBoundary_coefficients_oneZeroReentryDiscrepancy
    (source target :
      AdmissibleState (graphData := graphData) (minimal := minimal)) :
    ∃ first second : OrbitFace graphData.toRotationSystem → F2,
      orbitFaceBoundaryLinearMap graphData.toRotationSystem first =
          (fun edge =>
            (oneZeroReentryDiscrepancy source target edge).1) ∧
        orbitFaceBoundaryLinearMap graphData.toRotationSystem second =
          (fun edge =>
            (oneZeroReentryDiscrepancy source target edge).2) := by
  have hconnected : G.Connected := by
    rw [← GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
      G graphData]
    exact minimal.primalConnected
  have hdual : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Connected :=
    orbitFaceInteriorDual_connected graphData.toRotationSystem
      minimal.spherical.cubic minimal.primalConnected
      minimal.vertexRotationCyclic
  exact
    (isGraphFlow_iff_exists_orbitFaceBoundary_coefficients graphData
      minimal.facesTwoSided hdual hconnected minimal.spherical).1
        (oneZeroReentryDiscrepancy_isGraphFlow source target)

/-- On a common-core edge, the source singleton-zero completion has exactly
the source escape color. -/
@[simp]
theorem sourceOneZeroAmbientFlow_apply_commonCoreAmbientEdge
    {baseData : AdjacentPairData G}
    {rebaseCircuit :
      CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (edge : collar.commonCore.edgeSet) :
    oneZeroAmbientChain collar.sourceData sourceEscape.coloring
        (commonCoreAmbientEdge collar edge) =
      collar.sourceCommonColoring sourceEscape edge := by
  rw [commonCoreAmbientEdge,
    oneZeroAmbientChain_retained collar.sourceData sourceEscape.coloring
      (retainedEdgeToAmbientEdge collar.sourceData
        (collar.commonEdgeInSource edge))
      (collar.retainedEdgeToAmbientEdge_commonEdgeInSource_retainedBySource
        edge)]
  rw [ambientEdgeToRetainedEdge_retainedEdgeToAmbientEdge]
  rfl

/-- On the same common-core edge, the target singleton-zero completion has
exactly the target escape color. -/
@[simp]
theorem targetOneZeroAmbientFlow_apply_commonCoreAmbientEdge
    {baseData : AdjacentPairData G}
    {rebaseCircuit :
      CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (edge : collar.commonCore.edgeSet) :
    oneZeroAmbientChain collar.targetData collar.targetEscape.coloring
        (commonCoreAmbientEdge collar edge) =
      collar.targetCommonColoring edge := by
  rw [commonCoreAmbientEdge,
    collar.retainedEdgeToAmbientEdge_commonEdgeInSource_eq_target edge,
    oneZeroAmbientChain_retained collar.targetData
      collar.targetEscape.coloring
      (retainedEdgeToAmbientEdge collar.targetData
        (collar.commonEdgeInTarget edge))
      (retainedEdgeToAmbientEdge_isRetainedAmbientEdge collar.targetData
        (collar.commonEdgeInTarget edge))]
  rw [ambientEdgeToRetainedEdge_retainedEdgeToAmbientEdge]
  rfl

/-- The global flow difference between the two canonical singleton-zero
completions in an intrinsic collar. -/
def alignedOneZeroDiscrepancy
    {baseData : AdjacentPairData G}
    {rebaseCircuit :
      CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    G.edgeSet → Color :=
  oneZeroAmbientChain collar.sourceData sourceEscape.coloring +
    oneZeroAmbientChain collar.targetData collar.targetEscape.coloring

/-- The canonical singleton-zero flow difference restricts to the exact
intrinsic singleton collar discrepancy. -/
theorem alignedOneZeroDiscrepancy_apply_commonCoreAmbientEdge
    {baseData : AdjacentPairData G}
    {rebaseCircuit :
      CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (edge : collar.commonCore.edgeSet) :
    alignedOneZeroDiscrepancy collar sourceEscape
        (commonCoreAmbientEdge collar edge) =
      collar.commonDiscrepancy sourceEscape edge := by
  unfold alignedOneZeroDiscrepancy
  change
    oneZeroAmbientChain collar.sourceData sourceEscape.coloring
          (commonCoreAmbientEdge collar edge) +
        oneZeroAmbientChain collar.targetData collar.targetEscape.coloring
          (commonCoreAmbientEdge collar edge) =
      collar.commonDiscrepancy sourceEscape edge
  rw [sourceOneZeroAmbientFlow_apply_commonCoreAmbientEdge,
    targetOneZeroAmbientFlow_apply_commonCoreAmbientEdge]
  rfl

/-- The two-stage common-core inclusion through the source deletion is the
direct induced-edge inclusion into the ambient graph. -/
theorem commonCoreAmbientEdge_eq_inducedEdgeEmbedding
    {baseData : AdjacentPairData G}
    {rebaseCircuit :
      CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (edge : collar.commonCore.edgeSet) :
    commonCoreAmbientEdge collar edge =
      inducedEdgeEmbedding G collar.commonCorePredicate edge := by
  apply Subtype.ext
  calc
    (commonCoreAmbientEdge collar edge).1 =
        Sym2.map Subtype.val (collar.commonEdgeInSource edge).1 :=
      retainedEdgeToAmbientEdge_val collar.sourceData
        (collar.commonEdgeInSource edge)
    _ = Sym2.map Subtype.val edge.1 := by
      change Sym2.map Subtype.val
          (Sym2.map
            (deletedTwoPairsToFirstDeletionEmbedding G
              collar.sourceData.firstVertex collar.sourceData.secondVertex
              collar.targetData.firstVertex collar.targetData.secondVertex)
            edge.1) =
        Sym2.map Subtype.val edge.1
      rw [Sym2.map_map]
      rfl
    _ = (inducedEdgeEmbedding G collar.commonCorePredicate edge).1 :=
      (inducedEdgeEmbedding_val G collar.commonCorePredicate edge).symm

/-- The finite collar correction is the difference between the global
singleton-zero flow discrepancy and the zero extension of its exact
common-core restriction. -/
def intrinsicCollarCompletionCorrection
    {baseData : AdjacentPairData G}
    {rebaseCircuit :
      CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    G.edgeSet → Color :=
  alignedOneZeroDiscrepancy collar sourceEscape +
    collar.commonCoreChainExtendZero
      (collar.commonDiscrepancy sourceEscape)

/-- The collar correction vanishes on every edge of the exact common core. -/
theorem intrinsicCollarCompletionCorrection_apply_commonCoreAmbientEdge
    {baseData : AdjacentPairData G}
    {rebaseCircuit :
      CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (edge : collar.commonCore.edgeSet) :
    intrinsicCollarCompletionCorrection collar sourceEscape
        (commonCoreAmbientEdge collar edge) = 0 := by
  unfold intrinsicCollarCompletionCorrection
  change alignedOneZeroDiscrepancy collar sourceEscape
        (commonCoreAmbientEdge collar edge) +
      collar.commonCoreChainExtendZero
        (collar.commonDiscrepancy sourceEscape)
          (commonCoreAmbientEdge collar edge) = 0
  rw [alignedOneZeroDiscrepancy_apply_commonCoreAmbientEdge,
    commonCoreAmbientEdge_eq_inducedEdgeEmbedding,
    collar.commonCoreChainExtendZero_apply_inducedEdgeEmbedding]
  exact color_add_self _

/-- Adding the finite collar correction to the zero-extended common-core
discrepancy reconstructs the global singleton-zero flow difference. -/
theorem alignedOneZeroDiscrepancy_eq_commonCore_add_completionCorrection
    {baseData : AdjacentPairData G}
    {rebaseCircuit :
      CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    alignedOneZeroDiscrepancy collar sourceEscape =
      collar.commonCoreChainExtendZero
          (collar.commonDiscrepancy sourceEscape) +
        intrinsicCollarCompletionCorrection collar sourceEscape := by
  unfold intrinsicCollarCompletionCorrection
  let common := collar.commonCoreChainExtendZero
    (collar.commonDiscrepancy sourceEscape)
  let aligned := alignedOneZeroDiscrepancy collar sourceEscape
  change aligned = common + (aligned + common)
  calc
    aligned = common + (common + aligned) :=
      (chain_add_self_add common aligned).symm
    _ = common + (aligned + common) := by rw [add_comm common aligned]

/-- The global aligned completion is an ambient graph flow. -/
theorem alignedOneZeroDiscrepancy_isGraphFlow
    {baseData : AdjacentPairData G}
    {rebaseCircuit :
      CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    IsGraphFlow G (alignedOneZeroDiscrepancy collar sourceEscape) := by
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have hsource := oneZeroAmbientChain_isGraphFlow collar.sourceData hcubic
    sourceEscape.coloring sourceEscape.isTait
      ⟨sourceEscape.boundary_adjacent01_23.1,
        sourceEscape.boundary_adjacent01_23.2.1⟩
  have htarget := oneZeroAmbientChain_isGraphFlow collar.targetData hcubic
    collar.targetEscape.coloring collar.targetEscape.isTait
      ⟨collar.targetEscape.boundary_adjacent01_23.1,
        collar.targetEscape.boundary_adjacent01_23.2.1⟩
  exact hsource.add htarget

/-- The completed intrinsic discrepancy is represented by two exact binary
combinations of ambient facial boundaries. -/
theorem exists_orbitFaceBoundary_coefficients_alignedOneZeroDiscrepancy
    {baseData : AdjacentPairData G}
    {rebaseCircuit :
      CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    ∃ first second : OrbitFace graphData.toRotationSystem → F2,
      orbitFaceBoundaryLinearMap graphData.toRotationSystem first =
          (fun edge =>
            (alignedOneZeroDiscrepancy collar sourceEscape edge).1) ∧
        orbitFaceBoundaryLinearMap graphData.toRotationSystem second =
          (fun edge =>
            (alignedOneZeroDiscrepancy collar sourceEscape edge).2) := by
  have hconnected : G.Connected := by
    rw [← GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
      G graphData]
    exact minimal.primalConnected
  have hdual : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Connected :=
    orbitFaceInteriorDual_connected graphData.toRotationSystem
      minimal.spherical.cubic minimal.primalConnected
      minimal.vertexRotationCyclic
  exact
    (isGraphFlow_iff_exists_orbitFaceBoundary_coefficients graphData
      minimal.facesTwoSided hdual hconnected minimal.spherical).1
        (alignedOneZeroDiscrepancy_isGraphFlow collar sourceEscape)

/-- Equivalently, adjoining the finite collar correction to the nonfacial
zero-extended terminal discrepancy gives an explicit ambient facial
circulation. -/
theorem exists_orbitFaceBoundary_coefficients_commonCore_add_completionCorrection
    {baseData : AdjacentPairData G}
    {rebaseCircuit :
      CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    ∃ first second : OrbitFace graphData.toRotationSystem → F2,
      orbitFaceBoundaryLinearMap graphData.toRotationSystem first =
          (fun edge =>
            ((collar.commonCoreChainExtendZero
                  (collar.commonDiscrepancy sourceEscape) +
                intrinsicCollarCompletionCorrection collar sourceEscape)
              edge).1) ∧
        orbitFaceBoundaryLinearMap graphData.toRotationSystem second =
          (fun edge =>
            ((collar.commonCoreChainExtendZero
                  (collar.commonDiscrepancy sourceEscape) +
                intrinsicCollarCompletionCorrection collar sourceEscape)
              edge).2) := by
  rw [← alignedOneZeroDiscrepancy_eq_commonCore_add_completionCorrection
    collar sourceEscape]
  exact exists_orbitFaceBoundary_coefficients_alignedOneZeroDiscrepancy
    collar sourceEscape

/-- The finite collar correction has exactly the same Kirchhoff boundary as
the zero-extended common-core discrepancy; it is the precise boundary
completion needed to obtain the global flow. -/
theorem vertexKirchhoffSum_intrinsicCollarCompletionCorrection
    {baseData : AdjacentPairData G}
    {rebaseCircuit :
      CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (vertex : V) :
    vertexKirchhoffSum G
        (intrinsicCollarCompletionCorrection collar sourceEscape) vertex =
      vertexKirchhoffSum G
        (collar.commonCoreChainExtendZero
          (collar.commonDiscrepancy sourceEscape)) vertex := by
  have hflow := alignedOneZeroDiscrepancy_isGraphFlow
    collar sourceEscape vertex
  unfold vertexKirchhoffSum at hflow
  unfold intrinsicCollarCompletionCorrection vertexKirchhoffSum
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib, hflow, zero_add]

/-- The collar correction is necessarily nonzero: otherwise the nonzero
terminal boundary of the common-core discrepancy would itself be an ambient
circulation. -/
theorem intrinsicCollarCompletionCorrection_ne_zeroChain
    {baseData : AdjacentPairData G}
    {rebaseCircuit :
      CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    intrinsicCollarCompletionCorrection collar sourceEscape ≠ zeroChain := by
  intro hzero
  have hflow := alignedOneZeroDiscrepancy_isGraphFlow collar sourceEscape
  rw [alignedOneZeroDiscrepancy_eq_commonCore_add_completionCorrection
    collar sourceEscape, hzero] at hflow
  have hcommonFlow : IsGraphFlow G
      (collar.commonCoreChainExtendZero
        (collar.commonDiscrepancy sourceEscape)) := by
    intro vertex
    have hvalue := hflow vertex
    unfold vertexKirchhoffSum at hvalue ⊢
    simpa only [Pi.add_apply, zeroChain_apply, add_zero] using hvalue
  have hcoreFlow : IsGraphFlow collar.commonCore
      (collar.commonDiscrepancy sourceEscape) :=
    (isGraphFlow_inducedEdgeChainExtendZero_iff
      G collar.commonCorePredicate).1 hcommonFlow
  apply collar.commonDiscrepancyBoundaryState_ne_zero sourceEscape
  funext terminal
  exact hcoreFlow terminal.1

/-- The canonical flow discrepancy of an actual reentry either restricts to
an exact intrinsic singleton discrepancy or retains the certified recovery
geometry. -/
theorem AdmissibleReentry.exists_intrinsicOneZeroRestriction_or_recoveryGeometry
    {source target :
      AdmissibleState (graphData := graphData) (minimal := minimal)}
    (step : AdmissibleReentry source target) :
    (∃ sourceNormal :
          RotationOrderedCyclicKempeFusionChainNormalForm graphData minimal
            source.1.1,
        ∃ sourceEscape : sourceNormal.KempeOrbitAdjacentEscape,
          ∃ targetEdge : G.edgeSet,
            ∃ circuit : CrossCentralExactFaceCertifiedRebaseCircuit
                graphData minimal source.1.1,
              circuit.IsLengthMinimal ∧
                ∃ cycle :
                    CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
                      circuit,
                  cycle.IntrinsicShortFusionTarget targetEdge ∧
                    ∃ collar :
                        cycle.IntrinsicShortTargetEscapeCollar targetEdge,
                      source.1.2 = sourceEscape.coloring ∧
                        target.1 = ⟨collar.targetBase,
                          collar.targetEscape.coloring⟩ ∧
                        ∀ edge : collar.commonCore.edgeSet,
                          oneZeroReentryDiscrepancy source target
                              (commonCoreAmbientEdge collar edge) =
                            collar.commonDiscrepancy sourceEscape edge) ∨
      ∃ targetEdge : G.edgeSet,
        centralEdge
            (RecoveredRotationOrderedData graphData minimal source.1.1) ≠
          targetEdge ∧
        centralEdge
            (RecoveredRotationOrderedData graphData minimal target.1.1) =
          targetEdge ∧
        ∃ circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
            minimal source.1.1,
          circuit.IsLengthMinimal ∧
            ∃ rotated : CrossCentralExactFaceCertifiedRebaseCircuit graphData
                minimal source.1.1,
              rotated.arcLength = circuit.arcLength ∧
                ∃ transfer : ClosureRecoveryFaceTransfer rotated,
                  targetEdge = transfer.recovery.edge := by
  rcases step with
    ⟨sourceNormal, _sourceLaunch, sourceEscape, hsourceColor, targetEdge,
      htargetNe, htargetCentral, geometry, _targetNormal, _targetOutcome,
      _targetEscape, _htargetColor⟩
  rcases geometry with
    ⟨circuit, hminimal, cycle, hintrinsic, collar, htargetState⟩ |
      ⟨circuit, hminimal, rotated, hlength, transfer, htargetEdge⟩
  · left
    refine ⟨sourceNormal, sourceEscape, targetEdge, circuit, hminimal,
      cycle, hintrinsic, collar, hsourceColor, htargetState, ?_⟩
    intro edge
    unfold oneZeroReentryDiscrepancy AdmissibleState.oneZeroAmbientFlow
    rw [hsourceColor, htargetState]
    exact alignedOneZeroDiscrepancy_apply_commonCoreAmbientEdge
      collar sourceEscape edge
  · exact Or.inr ⟨targetEdge, htargetNe, htargetCentral, circuit,
      hminimal, rotated, hlength, transfer, htargetEdge⟩

end RotationOrderedFusionEscapeColorState

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
