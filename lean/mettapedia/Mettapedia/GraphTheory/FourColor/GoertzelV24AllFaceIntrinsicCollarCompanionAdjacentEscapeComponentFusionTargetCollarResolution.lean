import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAdjacentEscapeComponentFusionTargetCollarDiscrepancyRoute

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

namespace CompanionCrossPairFusionTargetCollarTraversal

variable (traversal :
  CompanionCrossPairFusionTargetCollarTraversal collar start)

/-- The nonexceptional color status of a target-path edge: target-own color
or one of the two fusion-arm color pairs transported across the common core. -/
def TargetPathEdgeTransported
    (edge : (DeletedAdjacentPairGraph G collar.targetData.firstVertex
      collar.targetData.secondVertex).edgeSet) : Prop :=
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
            (traversal.contact.fusion.lineFusion.normal.step.reentry.realization.companion))

/-- The two exceptional statuses retained at a target-path edge. -/
def TargetPathEdgeExceptional
    (edge : (DeletedAdjacentPairGraph G collar.targetData.firstVertex
      collar.targetData.secondVertex).edgeSet) : Prop :=
  ∃ commonEdge : collar.commonCore.edgeSet,
    collar.commonEdgeInTarget commonEdge = edge ∧
      ((Nonempty (CommonDiscrepancyContactRoute collar
          traversal.contact.fusion.lineFusion.normal.canonicalState
            commonEdge) ∧
        Nonempty (ResolvedChargedKempeReentry collar
          traversal.contact.fusion.lineFusion.normal.canonicalState)) ∨
      Nonempty (CommonDiscrepancyContactMonodromy collar
        traversal.contact.fusion.lineFusion.normal.canonicalState
          commonEdge))

/-- The routed edge status is exactly transported color or one of the two
exceptional recurrence/monodromy outcomes. -/
theorem targetPathEdgeColorResolution_iff
    (edge : (DeletedAdjacentPairGraph G collar.targetData.firstVertex
      collar.targetData.secondVertex).edgeSet) :
    traversal.TargetPathEdgeColorResolution edge ↔
      traversal.TargetPathEdgeTransported edge ∨
        traversal.TargetPathEdgeExceptional edge := by
  constructor
  · rintro (htargetOwn |
      ⟨commonEdge, htargetEdge,
        hreturn | hselected | hreentry | hmonodromy⟩)
    · exact Or.inl (Or.inl htargetOwn)
    · exact Or.inl (Or.inr ⟨commonEdge, htargetEdge, Or.inl hreturn⟩)
    · exact Or.inl (Or.inr ⟨commonEdge, htargetEdge, Or.inr hselected⟩)
    · exact Or.inr ⟨commonEdge, htargetEdge, Or.inl hreentry⟩
    · exact Or.inr ⟨commonEdge, htargetEdge, Or.inr hmonodromy⟩
  · rintro (htargetOwn | hexception)
    · rcases htargetOwn with htargetOwn |
        ⟨commonEdge, htargetEdge, hreturn | hselected⟩
      · exact Or.inl htargetOwn
      · exact Or.inr ⟨commonEdge, htargetEdge, Or.inl hreturn⟩
      · exact Or.inr ⟨commonEdge, htargetEdge,
          Or.inr (Or.inl hselected)⟩
    · rcases hexception with
        ⟨commonEdge, htargetEdge, hreentry | hmonodromy⟩
      · exact Or.inr ⟨commonEdge, htargetEdge,
          Or.inr (Or.inr (Or.inl hreentry))⟩
      · exact Or.inr ⟨commonEdge, htargetEdge,
          Or.inr (Or.inr (Or.inr hmonodromy))⟩

/-- A nontransported edge already gives a certified adjacent-escape endpoint
or an exact contact monodromy, retaining its common-core representative. -/
def TargetPathEdgeExceptionalOutcome
    (edge : (DeletedAdjacentPairGraph G collar.targetData.firstVertex
      collar.targetData.secondVertex).edgeSet) : Prop :=
  CertifiedAdjacentEscapeTerminal collar
      traversal.contact.fusion.lineFusion.normal.canonicalState ∨
    ∃ commonEdge : collar.commonCore.edgeSet,
      collar.commonEdgeInTarget commonEdge = edge ∧
        Nonempty (CommonDiscrepancyContactMonodromy collar
          traversal.contact.fusion.lineFusion.normal.canonicalState
            commonEdge)

theorem targetPathEdgeExceptionalOutcome_of_exceptional
    {edge : (DeletedAdjacentPairGraph G collar.targetData.firstVertex
      collar.targetData.secondVertex).edgeSet}
    (hexceptional : traversal.TargetPathEdgeExceptional edge) :
    traversal.TargetPathEdgeExceptionalOutcome edge := by
  rcases hexceptional with
    ⟨commonEdge, htargetEdge, hreentry | hmonodromy⟩
  · rcases hreentry.2 with ⟨resolution⟩
    exact Or.inl (.chargedReentry resolution)
  · exact Or.inr ⟨commonEdge, htargetEdge, hmonodromy⟩

/-- In every noncentral class, either the whole rerouted path has transported
color status, or an exact edge of that path already supplies a certified
recurrence endpoint or contact monodromy. -/
theorem exists_targetKempeReroutedPath_with_allTransported_or_exception
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
        ((∀ edge : (DeletedAdjacentPairGraph G
              collar.targetData.firstVertex
                collar.targetData.secondVertex).edgeSet,
            edge.1 ∈ targetPath.edges →
              traversal.TargetPathEdgeTransported edge) ∨
          ∃ edge : (DeletedAdjacentPairGraph G
              collar.targetData.firstVertex
                collar.targetData.secondVertex).edgeSet,
            edge.1 ∈ targetPath.edges ∧
              traversal.TargetPathEdgeExceptionalOutcome edge) := by
  classical
  rcases traversal.exists_targetKempeReroutedPath_with_colorResolution_of_noncentral
      hclass with ⟨targetPath, targetPathIsPath, edgeResolution⟩
  refine ⟨targetPath, targetPathIsPath, ?_⟩
  by_cases hall : ∀ edge : (DeletedAdjacentPairGraph G
        collar.targetData.firstVertex collar.targetData.secondVertex).edgeSet,
      edge.1 ∈ targetPath.edges →
        traversal.TargetPathEdgeTransported edge
  · exact Or.inl hall
  · push Not at hall
    rcases hall with ⟨edge, hedge, hnotTransported⟩
    have hresolved :=
      (traversal.targetPathEdgeColorResolution_iff edge).1
        (edgeResolution edge hedge)
    rcases hresolved with htransported | hexceptional
    · exact (hnotTransported htransported).elim
    · exact Or.inr ⟨edge, hedge,
        traversal.targetPathEdgeExceptionalOutcome_of_exceptional
          hexceptional⟩

/-- Complete seven-class collapse: pure transported target path, an exact
exceptional edge on such a path, or one of the four central cross-arm
obstructions. -/
theorem exists_allTransportedTargetPath_or_exception_or_crossObstruction :
    (∃ targetPath : (DeletedAdjacentPairGraph G
        collar.targetData.firstVertex collar.targetData.secondVertex).Walk
        ⟨traversal.contact.fusion.startVertex.1,
          traversal.contact.fusion.startVertex_mem_targetRetainedVertexSet⟩
        ⟨traversal.contact.fusion.endVertex.1,
          traversal.contact.fusion.endVertex_mem_targetRetainedVertexSet⟩,
      targetPath.IsPath ∧
        ∀ edge : (DeletedAdjacentPairGraph G collar.targetData.firstVertex
          collar.targetData.secondVertex).edgeSet,
          edge.1 ∈ targetPath.edges →
            traversal.TargetPathEdgeTransported edge) ∨
      (∃ targetPath : (DeletedAdjacentPairGraph G
          collar.targetData.firstVertex collar.targetData.secondVertex).Walk
          ⟨traversal.contact.fusion.startVertex.1,
            traversal.contact.fusion.startVertex_mem_targetRetainedVertexSet⟩
          ⟨traversal.contact.fusion.endVertex.1,
            traversal.contact.fusion.endVertex_mem_targetRetainedVertexSet⟩,
        targetPath.IsPath ∧
          ∃ edge : (DeletedAdjacentPairGraph G collar.targetData.firstVertex
            collar.targetData.secondVertex).edgeSet,
            edge.1 ∈ targetPath.edges ∧
              traversal.TargetPathEdgeExceptionalOutcome edge) ∨
        ∃ firstUsesOne secondUsesThree,
          traversal.traversalClass = .cross firstUsesOne secondUsesThree ∧
          ¬ collar.targetData.degreeTwoBoundaryData.KempePortsConnected
            collar.targetEscape.coloring collar.targetOwnFirstColor
              collar.targetOwnSecondColor
              (TargetCollarTraversalClass.firstCrossPort firstUsesOne)
              (TargetCollarTraversalClass.secondCrossPort
                secondUsesThree) := by
  cases hclass : traversal.traversalClass with
  | firstBoundaryPair =>
      rcases traversal.exists_targetKempeReroutedPath_with_allTransported_or_exception
          (Or.inl hclass) with ⟨targetPath, targetPathIsPath, hall | hexception⟩
      · exact Or.inl ⟨targetPath, targetPathIsPath, hall⟩
      · exact Or.inr (Or.inl
          ⟨targetPath, targetPathIsPath, hexception⟩)
  | secondBoundaryPair =>
      rcases traversal.exists_targetKempeReroutedPath_with_allTransported_or_exception
          (Or.inr (Or.inl hclass)) with
        ⟨targetPath, targetPathIsPath, hall | hexception⟩
      · exact Or.inl ⟨targetPath, targetPathIsPath, hall⟩
      · exact Or.inr (Or.inl
          ⟨targetPath, targetPathIsPath, hexception⟩)
  | bothBoundaryPairs =>
      rcases traversal.exists_targetKempeReroutedPath_with_allTransported_or_exception
          (Or.inr (Or.inr hclass)) with
        ⟨targetPath, targetPathIsPath, hall | hexception⟩
      · exact Or.inl ⟨targetPath, targetPathIsPath, hall⟩
      · exact Or.inr (Or.inl
          ⟨targetPath, targetPathIsPath, hexception⟩)
  | cross firstUsesOne secondUsesThree =>
      exact Or.inr (Or.inr ⟨firstUsesOne, secondUsesThree, rfl,
        collar.not_targetOwnKempePortsConnected_cross
          firstUsesOne secondUsesThree⟩)

end CompanionCrossPairFusionTargetCollarTraversal
end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
