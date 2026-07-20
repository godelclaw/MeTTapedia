import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAlternatingPrimalReturnChirality

set_option autoImplicit false

namespace Mettapedia.GraphTheory.FourColor

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

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

namespace GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
namespace RotationOrderedCyclicKempeFusionChainNormalForm

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}
  {normal : RotationOrderedCyclicKempeFusionChainNormalForm
    graphData minimal baseData}

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- An all-equal same-base successor is itself the recoloring of a complete
resolved fusion-chain normal form. -/
theorem AllEqualFusionSuccessor.exists_resolvedNormalForm
    (successor : normal.AllEqualFusionSuccessor) :
    ∃ successorNormal : RotationOrderedCyclicKempeFusionChainNormalForm
        graphData minimal baseData,
      successorNormal.recoloring = successor.coloring ∧
        successorNormal.profile.coloring = successor.coloring := by
  rcases successor.lens01 with ⟨lens01⟩
  rcases successor.lens23 with ⟨lens23⟩
  let data := RecoveredRotationOrderedData graphData minimal baseData
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring :=
    graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
      graphData minimal
  have hthird := third_color_properties successor.validPair.1
    successor.validPair.2.1 successor.validPair.2.2
  have hfirstSecond : successor.constant ≠ successor.other :=
    successor.validPair.2.2
  have hfirstThird :
      successor.constant ≠ successor.constant + successor.other :=
    hthird.2.1.symm
  have hsecondThird :
      successor.other ≠ successor.constant + successor.other :=
    hthird.2.2.symm
  have hsecondPair :
      ValidColorPair successor.constant
        (successor.constant + successor.other) :=
    ⟨successor.validPair.1, hthird.1, hfirstThird⟩
  have hfirstProfile :=
    data.hasSameSideKempeReachabilityProfile_of_constant_colorWord
      hcubic hnotColorable successor.coloring successor.isTait
        successor.validPair successor.boundary_constant
  have hsecondProfile :=
    data.hasSameSideKempeReachabilityProfile_of_constant_colorWord
      hcubic hnotColorable successor.coloring successor.isTait
        hsecondPair successor.boundary_constant
  have hcomponentProfile :
      ∀ K : (successor.coloring.bicoloredSubgraph successor.constant
          successor.other).ConnectedComponent,
        (data.degreeTwoBoundaryData.KempeComponentMeetsPort
            successor.coloring successor.constant successor.other K 0 ↔
          data.degreeTwoBoundaryData.KempeComponentMeetsPort
            successor.coloring successor.constant successor.other K 1) ∧
        (data.degreeTwoBoundaryData.KempeComponentMeetsPort
            successor.coloring successor.constant successor.other K 2 ↔
          data.degreeTwoBoundaryData.KempeComponentMeetsPort
            successor.coloring successor.constant successor.other K 3) := by
    intro K
    exact ⟨
      data.kempeComponentMeetsPort_zero_iff_one_of_selected_request
        hcubic hnotColorable successor.coloring successor.isTait
          successor.validPair K (Or.inl (successor.boundary_constant 0)),
      data.kempeComponentMeetsPort_two_iff_three_of_selected_request
        hcubic hnotColorable successor.coloring successor.isTait
          successor.validPair K (Or.inl (successor.boundary_constant 2))⟩
  have hfirstLinkage :
      ∃ K : (successor.coloring.bicoloredSubgraph successor.constant
          successor.other).ConnectedComponent,
        data.degreeTwoBoundaryData.KempeComponentMeetsPort
            successor.coloring successor.constant successor.other K 0 ∧
          data.degreeTwoBoundaryData.KempeComponentMeetsPort
            successor.coloring successor.constant successor.other K 1 :=
    (data.degreeTwoBoundaryData
      |>.kempePortsConnected_iff_exists_component_meets_both
        successor.coloring successor.constant successor.other 0 1).1
      ((hfirstProfile 0 1).2 (by decide))
  have hsecondLinkage :
      ∃ K : (successor.coloring.bicoloredSubgraph successor.constant
          successor.other).ConnectedComponent,
        data.degreeTwoBoundaryData.KempeComponentMeetsPort
            successor.coloring successor.constant successor.other K 2 ∧
          data.degreeTwoBoundaryData.KempeComponentMeetsPort
            successor.coloring successor.constant successor.other K 3 :=
    (data.degreeTwoBoundaryData
      |>.kempePortsConnected_iff_exists_component_meets_both
        successor.coloring successor.constant successor.other 2 3).1
      ((hfirstProfile 2 3).2 (by decide))
  let successorProfile :
      GoertzelV24AdjacentPairBoundary.AdjacentPairData.CyclicKempeProfile
        graphData data := {
    portsCyclic := normal.profile.portsCyclic
    coloring := successor.coloring
    isTaitColoring := successor.isTait
    boundaryWellFormed := normal.profile.boundaryWellFormed
    reductionCompatible := by
      simp only [SquareReductionSide.Compatible,
        SquareReductionSide.join01_23, if_pos]
      constructor
      · rw [successor.boundary_constant 0,
          successor.boundary_constant 1]
      · rw [successor.boundary_constant 2,
          successor.boundary_constant 3]
    firstColor := successor.constant
    secondColor := successor.other
    validPair := successor.validPair
    firstRequestSelected := Or.inl (successor.boundary_constant 0)
    secondRequestSelected := Or.inl (successor.boundary_constant 2)
    componentProfile := hcomponentProfile
    firstLinkage := hfirstLinkage
    secondLinkage := hsecondLinkage }
  have hdisjoint :=
    lens01.sameFamily_ambientPath_supports_disjoint
      hfirstProfile hsecondProfile lens23
  have hresolution :=
    EvenKempeFusionLens.rotationOrdered_sparseCrossFusionChainResolution_of_minimal
      graphData minimal baseData lens01 lens23
        successorProfile.boundaryWellFormed hfirstSecond hfirstThird
          hsecondThird hdisjoint.1 hdisjoint.2
  refine ⟨{
    profile := successorProfile
    recoloring := successor.coloring
    recoloring_mem_kempeClosure :=
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex
        ).mem_edgeKempeClosure_self successor.coloring
    recoloring_isTait := successor.isTait
    boundary_constant := successor.boundary_constant
    first_ne_second := hfirstSecond
    first_ne_third := hfirstThird
    second_ne_third := hsecondThird
    firstLens := lens01
    secondLens := lens23
    firstFamily_disjoint := hdisjoint.1
    secondFamily_disjoint := hdisjoint.2
    resolution := hresolution }, rfl, rfl⟩

/-- The all-equal reentry supplies a terminal-or-pumping normal form at its
actual successor coloring. -/
theorem AllEqualFusionSuccessor.exists_resolvedNormalForm_and_outcome
    (successor : normal.AllEqualFusionSuccessor) :
    ∃ successorNormal : RotationOrderedCyclicKempeFusionChainNormalForm
        graphData minimal baseData,
      successorNormal.recoloring = successor.coloring ∧
        (successorNormal.TerminalFusionOutcome ∨
          successorNormal.CertifiedRebasePumpingLaunch) := by
  rcases successor.exists_resolvedNormalForm with
    ⟨successorNormal, hrecoloring, _hprofileColoring⟩
  exact ⟨successorNormal, hrecoloring,
    successorNormal.terminalFusion_or_certifiedRebasePumpingLaunch⟩

variable {escape : normal.KempeOrbitAdjacentEscape}

/-- Every constructed same-base Kempe reentry is compositional: the
all-equal branch becomes a fully resolved normal form at the exact one-step
coloring, while the adjacent branch retains its canonical escape. -/
theorem SameBaseKempeReentry.resolvedNormalForm_or_adjacentEscape
    (reentry : normal.SameBaseKempeReentry escape) :
    (∃ successorNormal : RotationOrderedCyclicKempeFusionChainNormalForm
        graphData minimal baseData,
      (DeletedAdjacentPairGraph G
          (RecoveredRotationOrderedData graphData minimal baseData).firstVertex
          (RecoveredRotationOrderedData graphData minimal baseData).secondVertex
        ).EdgeKempeStep escape.coloring successorNormal.recoloring ∧
      successorNormal.profile.coloring = successorNormal.recoloring ∧
      (successorNormal.TerminalFusionOutcome ∨
        successorNormal.CertifiedRebasePumpingLaunch)) ∨
      ∃ successor : normal.KempeOrbitAdjacentEscape,
        (DeletedAdjacentPairGraph G
            (RecoveredRotationOrderedData graphData minimal baseData).firstVertex
            (RecoveredRotationOrderedData graphData minimal baseData).secondVertex
          ).EdgeKempeStep escape.coloring successor.coloring := by
  cases reentry with
  | allEqual successor oneStep =>
      left
      rcases successor.exists_resolvedNormalForm with
        ⟨successorNormal, hrecoloring, hprofileColoring⟩
      refine ⟨successorNormal, ?_,
        hprofileColoring.trans hrecoloring.symm,
        successorNormal.terminalFusion_or_certifiedRebasePumpingLaunch⟩
      simpa only [hrecoloring] using oneStep
  | adjacent successor oneStep =>
      exact Or.inr ⟨successor, oneStep⟩

end RotationOrderedCyclicKempeFusionChainNormalForm
end GoertzelV24RecoveredAdjacentPairFusionChainNormalForm

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
  {transfer : SingletonCompanionTransferPath collar sourceEscape}

namespace SingletonCompanionTransferPath.AllEqualSourceFusionConnector

variable (connector : transfer.AllEqualSourceFusionConnector)

/-- The first-hit all-equal connector contains a same-base all-equal
successor package. -/
noncomputable def toAllEqualFusionSuccessor :
    sourceNormal.AllEqualFusionSuccessor where
  coloring := SourceDeletionKempeRealization.coloring
    transfer connector.realization
  isTait := connector.realization.isTait
  boundary_allEqual := connector.boundary_allEqual
  reachable_from_allEqual := connector.realization.reachable_from_allEqual
  reachable_from_profile := connector.realization.reachable_from_profile
  constant := connector.constant
  other := connector.other
  validPair := connector.validPair
  boundary_constant := connector.boundary_constant
  lens01 := connector.lens01
  lens23 := connector.lens23

/-- The literal component swap retained by an all-equal connector is the
recoloring of a complete resolved normal form. -/
theorem exists_resolvedNormalForm :
    ∃ successorNormal : RotationOrderedCyclicKempeFusionChainNormalForm
        graphData minimal baseData,
      successorNormal.recoloring =
        SourceDeletionKempeRealization.coloring
          transfer connector.realization := by
  rcases GoertzelV24RecoveredAdjacentPairFusionChainNormalForm.RotationOrderedCyclicKempeFusionChainNormalForm.AllEqualFusionSuccessor.exists_resolvedNormalForm
      connector.toAllEqualFusionSuccessor with
    ⟨successorNormal, hrecoloring, _hprofileColoring⟩
  exact ⟨successorNormal, hrecoloring⟩

/-- An all-equal first-hit connector supplies a same-base fusion terminal or
certified pumping launch, with the actual component swap retained as the
normal form's recoloring. -/
theorem exists_resolvedNormalForm_and_outcome :
    ∃ successorNormal : RotationOrderedCyclicKempeFusionChainNormalForm
        graphData minimal baseData,
      successorNormal.recoloring =
          SourceDeletionKempeRealization.coloring
            transfer connector.realization ∧
        successorNormal.profile.coloring =
          SourceDeletionKempeRealization.coloring
            transfer connector.realization ∧
        (successorNormal.TerminalFusionOutcome ∨
          successorNormal.CertifiedRebasePumpingLaunch) := by
  rcases GoertzelV24RecoveredAdjacentPairFusionChainNormalForm.RotationOrderedCyclicKempeFusionChainNormalForm.AllEqualFusionSuccessor.exists_resolvedNormalForm
      connector.toAllEqualFusionSuccessor with
    ⟨successorNormal, hrecoloring, hprofileColoring⟩
  exact ⟨successorNormal, hrecoloring, hprofileColoring,
    successorNormal.terminalFusion_or_certifiedRebasePumpingLaunch⟩

/-- The resolved all-equal normal form is reached by the literal component
swap carried by the connector. -/
theorem exists_oneStep_resolvedNormalForm_and_outcome :
    ∃ successorNormal : RotationOrderedCyclicKempeFusionChainNormalForm
        graphData minimal baseData,
      successorNormal.recoloring =
          SourceDeletionKempeRealization.coloring
            transfer connector.realization ∧
      (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
          collar.sourceData.secondVertex).EdgeKempeStep
        sourceEscape.coloring successorNormal.recoloring ∧
      successorNormal.profile.coloring = successorNormal.recoloring ∧
      (successorNormal.TerminalFusionOutcome ∨
        successorNormal.CertifiedRebasePumpingLaunch) := by
  rcases GoertzelV24RecoveredAdjacentPairFusionChainNormalForm.RotationOrderedCyclicKempeFusionChainNormalForm.AllEqualFusionSuccessor.exists_resolvedNormalForm
      connector.toAllEqualFusionSuccessor with
    ⟨successorNormal, hrecoloring, hprofileColoring⟩
  refine ⟨successorNormal, hrecoloring, ?_,
    hprofileColoring.trans hrecoloring.symm,
    successorNormal.terminalFusion_or_certifiedRebasePumpingLaunch⟩
  simpa only [hrecoloring, toAllEqualFusionSuccessor] using
    connector.realization.oneStep

end SingletonCompanionTransferPath.AllEqualSourceFusionConnector

namespace FirstHitSingletonCompanionTransferPath

variable (firstHit : FirstHitSingletonCompanionTransferPath
  (collar := collar) (sourceEscape := sourceEscape))

/-- Exact first-hit outcome after resolving the all-equal branch: a resolved
fusion normal form, a one-step adjacent escape, or a transverse
companion-change branch. -/
theorem resolvedFusion_or_adjacentReentry_or_transverseChange :
    (∃ successorNormal : RotationOrderedCyclicKempeFusionChainNormalForm
        graphData minimal baseData,
      (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
          collar.sourceData.secondVertex).EdgeKempeStep
        sourceEscape.coloring successorNormal.recoloring ∧
      successorNormal.profile.coloring = successorNormal.recoloring ∧
      (successorNormal.TerminalFusionOutcome ∨
        successorNormal.CertifiedRebasePumpingLaunch)) ∨
      (∃ successor : sourceNormal.KempeOrbitAdjacentEscape,
        (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
            collar.sourceData.secondVertex).EdgeKempeStep
          sourceEscape.coloring successor.coloring) ∨
      Nonempty firstHit.TransverseCompanionChange := by
  rcases firstHit.allEqualFusionConnector_or_adjacentReentry_or_transverseChange
      with hallEqual | hadjacent | htransverse
  · rcases hallEqual with ⟨connector⟩
    rcases GoertzelV24RecoveredAdjacentPairFusionChainNormalForm.RotationOrderedCyclicKempeFusionChainNormalForm.AllEqualFusionSuccessor.exists_resolvedNormalForm
        connector.toAllEqualFusionSuccessor with
      ⟨successorNormal, hrecoloring, hprofileColoring⟩
    apply Or.inl
    refine ⟨successorNormal, ?_,
      hprofileColoring.trans hrecoloring.symm,
      successorNormal.terminalFusion_or_certifiedRebasePumpingLaunch⟩
    simpa only [hrecoloring,
      SingletonCompanionTransferPath.AllEqualSourceFusionConnector.toAllEqualFusionSuccessor]
      using connector.realization.oneStep
  · rcases hadjacent with ⟨reentry⟩
    apply Or.inr
    apply Or.inl
    refine ⟨reentry.successor, ?_⟩
    simpa only [reentry.coloring_eq] using reentry.realization.oneStep
  · exact Or.inr (Or.inr htransverse)

end FirstHitSingletonCompanionTransferPath

end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
