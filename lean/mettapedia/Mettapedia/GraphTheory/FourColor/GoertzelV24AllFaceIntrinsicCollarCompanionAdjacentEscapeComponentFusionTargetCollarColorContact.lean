import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAdjacentEscapeComponentFusionTargetCollarKempeSplice
import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCorrectionState
import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicShortCommonDiscrepancy

set_option autoImplicit false

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24CorridorPumping
open GoertzelV24FourDefectBoundary
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

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

variable {cycle :
    CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle rebaseCircuit}
  {targetEdge : G.edgeSet}
  {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
    graphData minimal baseData}
  {collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge}
  {start : sourceNormal.KempeOrbitAdjacentEscape}

namespace CompanionCrossPairFusionPrimalTrail

variable (fusion : CompanionCrossPairFusionPrimalTrail collar start)

/-- An edge which survives the target deletion and occurs on the ambient
fusion trail has an exact common-core representative.  Its source image is
still a vertex of the fused line path. -/
theorem exists_commonCoreEdge_of_targetEdge_mem_ambientTrail
    (edge : (DeletedAdjacentPairGraph G collar.targetData.firstVertex
      collar.targetData.secondVertex).edgeSet)
    (hedge : (retainedEdgeToAmbientEdge collar.targetData edge).1 ∈
      fusion.ambientTrail.edges) :
    ∃ commonEdge : collar.commonCore.edgeSet,
      collar.commonEdgeInTarget commonEdge = edge ∧
        collar.commonEdgeInSource commonEdge ∈
          fusion.lineFusion.fused.path.support := by
  let ambientEdge := retainedEdgeToAmbientEdge collar.targetData edge
  have hsource : IsRetainedAmbientEdge collar.sourceData ambientEdge := by
    apply isRetainedAmbientEdge_of_mem_retainedWalkToAmbient_edges
      collar.sourceData fusion.retainedTrail ambientEdge
    change ambientEdge.1 ∈
      (collar.sourceData.retainedWalkToAmbient fusion.retainedTrail).edges
      at hedge
    exact hedge
  have htarget : IsRetainedAmbientEdge collar.targetData ambientEdge :=
    retainedEdgeToAmbientEdge_isRetainedAmbientEdge collar.targetData edge
  have houtside : ambientEdge ∉ collar.intrinsicCollarEdgeFinset := by
    intro hmem
    rw [intrinsicCollarEdgeFinset, Finset.mem_union] at hmem
    rcases hmem with hsourceCollar | htargetCollar
    · exact ((mem_adjacentPairCollarEdgeFinset_iff
        collar.sourceData ambientEdge).1 hsourceCollar) hsource
    · exact ((mem_adjacentPairCollarEdgeFinset_iff
        collar.targetData ambientEdge).1 htargetCollar) htarget
  rcases collar.exists_commonCoreEdge_of_not_mem_intrinsicCollar
      ambientEdge houtside with ⟨commonEdge, hcommonAmbient⟩
  have hcommonAmbient' :
      commonCoreAmbientEdge collar commonEdge = ambientEdge := by
    rw [commonCoreAmbientEdge_eq_inducedEdgeEmbedding]
    exact hcommonAmbient
  have htargetEdge : collar.commonEdgeInTarget commonEdge = edge := by
    apply collar.targetData.retainedEdgeToAmbientEdge_injective
    calc
      retainedEdgeToAmbientEdge collar.targetData
          (collar.commonEdgeInTarget commonEdge) =
          retainedEdgeToAmbientEdge collar.sourceData
            (collar.commonEdgeInSource commonEdge) :=
        (collar.retainedEdgeToAmbientEdge_commonEdgeInSource_eq_target
          commonEdge).symm
      _ = commonCoreAmbientEdge collar commonEdge := rfl
      _ = ambientEdge := hcommonAmbient'
      _ = retainedEdgeToAmbientEdge collar.targetData edge := rfl
  have hsourceAmbient :
      (retainedEdgeToAmbientEdge collar.sourceData
        (collar.commonEdgeInSource commonEdge)).1 ∈
          fusion.ambientTrail.edges := by
    rw [collar.retainedEdgeToAmbientEdge_commonEdgeInSource_eq_target,
      htargetEdge]
    exact hedge
  have hsourceTrail : (collar.commonEdgeInSource commonEdge).1 ∈
      fusion.retainedTrail.edges := by
    apply (retainedEdgeToAmbientEdge_mem_retainedWalkToAmbient_edges_iff
      collar.sourceData fusion.retainedTrail
        (collar.commonEdgeInSource commonEdge)).1
    change (retainedEdgeToAmbientEdge collar.sourceData
        (collar.commonEdgeInSource commonEdge)).1 ∈
      (collar.sourceData.retainedWalkToAmbient fusion.retainedTrail).edges
      at hsourceAmbient
    exact hsourceAmbient
  rw [fusion.retainedTrail_edges_eq] at hsourceTrail
  rcases List.mem_map.mp hsourceTrail with
    ⟨lineEdge, lineEdgeMem, lineEdgeEq⟩
  have lineEdge_eq : lineEdge = collar.commonEdgeInSource commonEdge :=
    Subtype.ext lineEdgeEq
  subst lineEdge
  exact ⟨commonEdge, htargetEdge, lineEdgeMem⟩

end CompanionCrossPairFusionPrimalTrail

namespace CompanionCrossPairFusionTargetCollarTraversal

variable (traversal :
  CompanionCrossPairFusionTargetCollarTraversal collar start)

/-- After same-side Kempe surgery, every target-path edge has one of three
honest color explanations: it is selected by the target-own collar pair; it
retains one of the two source fusion-arm color pairs; or it meets the exact
nonzero source--target discrepancy on a common-core edge. -/
theorem exists_targetKempeReroutedPath_with_colorTransport_or_discrepancy_of_noncentral
    (hclass : traversal.traversalClass = .firstBoundaryPair ∨
      traversal.traversalClass = .secondBoundaryPair ∨
      traversal.traversalClass = .bothBoundaryPairs) :
    ∃ targetPath : (DeletedAdjacentPairGraph G
        collar.targetData.firstVertex collar.targetData.secondVertex).Walk
        ⟨traversal.contact.fusion.startVertex.1,
          traversal.contact.fusion.startVertex_mem_targetRetainedVertexSet⟩
        ⟨traversal.contact.fusion.endVertex.1,
          traversal.contact.fusion.endVertex_mem_targetRetainedVertexSet⟩,
      targetPath.IsPath ∧
      ∀ edge : (DeletedAdjacentPairGraph G
          collar.targetData.firstVertex collar.targetData.secondVertex).edgeSet,
        edge.1 ∈ targetPath.edges →
          edge ∈ collar.targetEscape.coloring.bicoloredSet
              collar.targetOwnFirstColor collar.targetOwnSecondColor ∨
            ∃ commonEdge : collar.commonCore.edgeSet,
              collar.commonEdgeInTarget commonEdge = edge ∧
                (edge ∈ collar.targetEscape.coloring.bicoloredSet
                    (traversal.contact.fusion.lineFusion.normal.returnData.lastOverlap.overlap.fixedColor)
                    (traversal.contact.fusion.lineFusion.normal.returnData.lastOverlap.overlap.breakOuterColor) ∨
                  edge ∈ collar.targetEscape.coloring.bicoloredSet
                    (crossFaceZeroColor
                      (traversal.contact.fusion.lineFusion.normal.step.firstHit.transfer.coordinate))
                    (traversal.contact.fusion.lineFusion.normal.step.reentry.realization.companion) ∨
                  collar.commonDiscrepancy
                    traversal.contact.fusion.lineFusion.normal.canonicalState
                      commonEdge ≠ 0) := by
  rcases traversal.exists_targetKempeReroutedPath_with_edgeOrigin_of_noncentral
      hclass with ⟨targetPath, targetPathIsPath, edgeOrigin⟩
  refine ⟨targetPath, targetPathIsPath, ?_⟩
  intro edge hedge
  rcases edgeOrigin edge hedge with hold | htargetOwn
  · let fusion := traversal.contact.fusion
    rcases fusion.exists_commonCoreEdge_of_targetEdge_mem_ambientTrail
        edge hold with ⟨commonEdge, htargetEdge, hsourceSupport⟩
    refine Or.inr ⟨commonEdge, htargetEdge, ?_⟩
    have hsourceSelected :=
      fusion.lineFusion.fused.support_selected
        (collar.commonEdgeInSource commonEdge) hsourceSupport
    by_cases hdiscrepancy : collar.commonDiscrepancy
        fusion.lineFusion.normal.canonicalState commonEdge = 0
    · have hcolorEq :
          collar.sourceCommonColoring
              fusion.lineFusion.normal.canonicalState commonEdge =
            collar.targetCommonColoring commonEdge :=
        (add_eq_zero_iff_eq _ _).mp hdiscrepancy
      rcases hsourceSelected with hreturn | hselected
      · apply Or.inl
        rw [← htargetEdge]
        change collar.targetCommonColoring commonEdge =
              fusion.lineFusion.normal.returnData.lastOverlap.overlap.fixedColor ∨
            collar.targetCommonColoring commonEdge =
              fusion.lineFusion.normal.returnData.lastOverlap.overlap.breakOuterColor
        change collar.sourceCommonColoring
              fusion.lineFusion.normal.canonicalState commonEdge =
                fusion.lineFusion.normal.returnData.lastOverlap.overlap.fixedColor ∨
            collar.sourceCommonColoring
              fusion.lineFusion.normal.canonicalState commonEdge =
                fusion.lineFusion.normal.returnData.lastOverlap.overlap.breakOuterColor
          at hreturn
        rcases hreturn with hfixed | houter
        · exact Or.inl (hcolorEq.symm.trans hfixed)
        · exact Or.inr (hcolorEq.symm.trans houter)
      · apply Or.inr
        apply Or.inl
        rw [← htargetEdge]
        change collar.targetCommonColoring commonEdge =
              crossFaceZeroColor
                fusion.lineFusion.normal.step.firstHit.transfer.coordinate ∨
            collar.targetCommonColoring commonEdge =
              fusion.lineFusion.normal.step.reentry.realization.companion
        change collar.sourceCommonColoring
              fusion.lineFusion.normal.canonicalState commonEdge =
                crossFaceZeroColor
                  fusion.lineFusion.normal.step.firstHit.transfer.coordinate ∨
            collar.sourceCommonColoring
              fusion.lineFusion.normal.canonicalState commonEdge =
                fusion.lineFusion.normal.step.reentry.realization.companion
          at hselected
        rcases hselected with hfirst | hsecond
        · exact Or.inl (hcolorEq.symm.trans hfirst)
        · exact Or.inr (hcolorEq.symm.trans hsecond)
    · exact Or.inr (Or.inr hdiscrepancy)
  · exact Or.inl htargetOwn

/-- The complete seven-class collar outcome: the three noncentral classes
carry edgewise target color transport or an exact common-core discrepancy
contact, while the four central classes retain their cross-arm obstruction. -/
theorem exists_targetKempeReroutedPath_with_colorTransport_or_discrepancy_or_crossObstruction :
    (∃ targetPath : (DeletedAdjacentPairGraph G
        collar.targetData.firstVertex collar.targetData.secondVertex).Walk
        ⟨traversal.contact.fusion.startVertex.1,
          traversal.contact.fusion.startVertex_mem_targetRetainedVertexSet⟩
        ⟨traversal.contact.fusion.endVertex.1,
          traversal.contact.fusion.endVertex_mem_targetRetainedVertexSet⟩,
      targetPath.IsPath ∧
      ∀ edge : (DeletedAdjacentPairGraph G
          collar.targetData.firstVertex collar.targetData.secondVertex).edgeSet,
        edge.1 ∈ targetPath.edges →
          edge ∈ collar.targetEscape.coloring.bicoloredSet
              collar.targetOwnFirstColor collar.targetOwnSecondColor ∨
            ∃ commonEdge : collar.commonCore.edgeSet,
              collar.commonEdgeInTarget commonEdge = edge ∧
                (edge ∈ collar.targetEscape.coloring.bicoloredSet
                    (traversal.contact.fusion.lineFusion.normal.returnData.lastOverlap.overlap.fixedColor)
                    (traversal.contact.fusion.lineFusion.normal.returnData.lastOverlap.overlap.breakOuterColor) ∨
                  edge ∈ collar.targetEscape.coloring.bicoloredSet
                    (crossFaceZeroColor
                      (traversal.contact.fusion.lineFusion.normal.step.firstHit.transfer.coordinate))
                    (traversal.contact.fusion.lineFusion.normal.step.reentry.realization.companion) ∨
                  collar.commonDiscrepancy
                    traversal.contact.fusion.lineFusion.normal.canonicalState
                      commonEdge ≠ 0)) ∨
      ∃ firstUsesOne secondUsesThree,
        traversal.traversalClass = .cross firstUsesOne secondUsesThree ∧
        ¬ collar.targetData.degreeTwoBoundaryData.KempePortsConnected
          collar.targetEscape.coloring collar.targetOwnFirstColor
            collar.targetOwnSecondColor
            (TargetCollarTraversalClass.firstCrossPort firstUsesOne)
            (TargetCollarTraversalClass.secondCrossPort secondUsesThree) := by
  cases hclass : traversal.traversalClass with
  | firstBoundaryPair =>
      exact Or.inl <|
        traversal.exists_targetKempeReroutedPath_with_colorTransport_or_discrepancy_of_noncentral
          (Or.inl hclass)
  | secondBoundaryPair =>
      exact Or.inl <|
        traversal.exists_targetKempeReroutedPath_with_colorTransport_or_discrepancy_of_noncentral
          (Or.inr (Or.inl hclass))
  | bothBoundaryPairs =>
      exact Or.inl <|
        traversal.exists_targetKempeReroutedPath_with_colorTransport_or_discrepancy_of_noncentral
          (Or.inr (Or.inr hclass))
  | cross firstUsesOne secondUsesThree =>
      exact Or.inr ⟨firstUsesOne, secondUsesThree, rfl,
        collar.not_targetOwnKempePortsConnected_cross
          firstUsesOne secondUsesThree⟩

end CompanionCrossPairFusionTargetCollarTraversal
end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
