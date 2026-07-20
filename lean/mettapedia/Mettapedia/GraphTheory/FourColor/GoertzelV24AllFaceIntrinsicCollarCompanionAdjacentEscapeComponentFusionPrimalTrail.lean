import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAdjacentEscapeComponentFusionPath
import Mettapedia.GraphTheory.FourColor.GoertzelV24LineGraphCanonicalPrimalLift
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionAmbientTrailFaceCutTransport

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

/-- A coherent cross-pair line path together with its exact edge-simple
primal lift in the deleted adjacent-pair graph. -/
structure CompanionCrossPairFusionPrimalTrail
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (start : sourceNormal.KempeOrbitAdjacentEscape) where
  lineFusion : CompanionCrossPairFusionLinePath collar start
  startVertex : retainedVertexSet collar.sourceData.firstVertex
    collar.sourceData.secondVertex
  endVertex : retainedVertexSet collar.sourceData.firstVertex
    collar.sourceData.secondVertex
  retainedTrail :
    (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
      collar.sourceData.secondVertex).Walk startVertex endVertex
  retainedTrail_isTrail : retainedTrail.IsTrail
  retainedTrail_positive : 0 < retainedTrail.length
  retainedTrail_edges_eq : retainedTrail.edges =
    lineFusion.fused.path.support.map Subtype.val

namespace CompanionCrossPairFusionPrimalTrail

variable (fusion : CompanionCrossPairFusionPrimalTrail collar start)

/-- The retained fusion trail has terminal darts. -/
theorem retainedTrail_not_nil : ¬fusion.retainedTrail.Nil := by
  exact SimpleGraph.Walk.not_nil_iff_lt_length.mpr
    fusion.retainedTrail_positive

/-- The retained fusion trail enters through the return-root edge. -/
theorem retainedTrail_firstDart_edge :
    (fusion.retainedTrail.firstDart fusion.retainedTrail_not_nil).edge =
      fusion.lineFusion.normal.rootEdge.1 := by
  let trail := fusion.retainedTrail
  let linePath := fusion.lineFusion.fused.path
  have hmapNonempty : linePath.support.map Subtype.val ≠ [] := by
    intro hnil
    exact linePath.support_ne_nil (List.map_eq_nil_iff.mp hnil)
  calc
    (trail.firstDart fusion.retainedTrail_not_nil).edge =
        trail.edges.head
          (SimpleGraph.Walk.edges_eq_nil.not.mpr
            fusion.retainedTrail_not_nil) :=
      (trail.edge_firstDart fusion.retainedTrail_not_nil).trans
        (trail.mk_start_snd_eq_head_edges fusion.retainedTrail_not_nil)
    _ = (linePath.support.map Subtype.val).head hmapNonempty := by
      dsimp only [trail, linePath]
      simp only [fusion.retainedTrail_edges_eq]
    _ = (linePath.support.head linePath.support_ne_nil).1 := List.head_map _
    _ = fusion.lineFusion.normal.rootEdge.1 := by
      rw [List.head_eq_getElem_zero linePath.support_ne_nil]
      exact congrArg Subtype.val linePath.support_getElem_zero

/-- The retained fusion trail leaves through the selected launch edge. -/
theorem retainedTrail_lastDart_edge :
    (fusion.retainedTrail.lastDart fusion.retainedTrail_not_nil).edge =
      fusion.lineFusion.normal.launchEdge.1 := by
  let trail := fusion.retainedTrail
  let linePath := fusion.lineFusion.fused.path
  have hmapNonempty : linePath.support.map Subtype.val ≠ [] := by
    intro hnil
    exact linePath.support_ne_nil (List.map_eq_nil_iff.mp hnil)
  calc
    (trail.lastDart fusion.retainedTrail_not_nil).edge =
        trail.edges.getLast
          (SimpleGraph.Walk.edges_eq_nil.not.mpr
            fusion.retainedTrail_not_nil) :=
      (trail.edge_lastDart fusion.retainedTrail_not_nil).trans
        (trail.mk_penultimate_end_eq_getLast_edges
          fusion.retainedTrail_not_nil)
    _ = (linePath.support.map Subtype.val).getLast hmapNonempty := by
      dsimp only [trail, linePath]
      simp only [fusion.retainedTrail_edges_eq]
    _ = (linePath.support.getLast linePath.support_ne_nil).1 :=
      List.getLast_map _
    _ = fusion.lineFusion.normal.launchEdge.1 := by
      rw [linePath.getLast_support]

/-- Include the retained fusion trail back into the original graph. -/
noncomputable def ambientTrail :
    G.Walk fusion.startVertex.1 fusion.endVertex.1 :=
  collar.sourceData.retainedWalkToAmbient fusion.retainedTrail

/-- Retained-vertex inclusion preserves edge-simple trailhood. -/
theorem ambientTrail_isTrail : fusion.ambientTrail.IsTrail := by
  exact collar.sourceData.retainedWalkToAmbient_isTrail
    fusion.retainedTrail_isTrail

/-- Retained-vertex inclusion preserves nontriviality. -/
theorem ambientTrail_positive : 0 < fusion.ambientTrail.length := by
  apply SimpleGraph.Walk.not_nil_iff_lt_length.mp
  apply retainedWalkToAmbient_not_nil collar.sourceData fusion.retainedTrail
  exact SimpleGraph.Walk.not_nil_iff_lt_length.mpr
    fusion.retainedTrail_positive

/-- The ambient fusion trail has terminal darts. -/
theorem ambientTrail_not_nil : ¬fusion.ambientTrail.Nil := by
  exact SimpleGraph.Walk.not_nil_iff_lt_length.mpr
    fusion.ambientTrail_positive

/-- Inclusion identifies the incoming ambient edge exactly. -/
theorem ambientTrail_firstDart_edge :
    (fusion.ambientTrail.firstDart fusion.ambientTrail_not_nil).edge =
      (retainedEdgeToAmbientEdge collar.sourceData
        fusion.lineFusion.normal.rootEdge).1 := by
  calc
    (fusion.ambientTrail.firstDart fusion.ambientTrail_not_nil).edge =
        (retainedDartToAmbientDart collar.sourceData
          (fusion.retainedTrail.firstDart
            fusion.retainedTrail_not_nil)).edge :=
      congrArg SimpleGraph.Dart.edge
        (retainedWalkToAmbient_firstDart collar.sourceData
          fusion.retainedTrail fusion.retainedTrail_not_nil
          fusion.ambientTrail_not_nil)
    _ = (fusion.retainedTrail.firstDart
          fusion.retainedTrail_not_nil).edge.map Subtype.val := by
      rw [retainedDartToAmbientDart_edge]
    _ = fusion.lineFusion.normal.rootEdge.1.map Subtype.val := by
      rw [fusion.retainedTrail_firstDart_edge]
    _ = (retainedEdgeToAmbientEdge collar.sourceData
          fusion.lineFusion.normal.rootEdge).1 := by
      rw [retainedEdgeToAmbientEdge_val]

/-- Inclusion identifies the outgoing ambient edge exactly. -/
theorem ambientTrail_lastDart_edge :
    (fusion.ambientTrail.lastDart fusion.ambientTrail_not_nil).edge =
      (retainedEdgeToAmbientEdge collar.sourceData
        fusion.lineFusion.normal.launchEdge).1 := by
  calc
    (fusion.ambientTrail.lastDart fusion.ambientTrail_not_nil).edge =
        (retainedDartToAmbientDart collar.sourceData
          (fusion.retainedTrail.lastDart
            fusion.retainedTrail_not_nil)).edge :=
      congrArg SimpleGraph.Dart.edge
        (retainedWalkToAmbient_lastDart collar.sourceData
          fusion.retainedTrail fusion.retainedTrail_not_nil
          fusion.ambientTrail_not_nil)
    _ = (fusion.retainedTrail.lastDart
          fusion.retainedTrail_not_nil).edge.map Subtype.val := by
      rw [retainedDartToAmbientDart_edge]
    _ = fusion.lineFusion.normal.launchEdge.1.map Subtype.val := by
      rw [fusion.retainedTrail_lastDart_edge]
    _ = (retainedEdgeToAmbientEdge collar.sourceData
          fusion.lineFusion.normal.launchEdge).1 := by
      rw [retainedEdgeToAmbientEdge_val]

/-- The incoming edge is the same common-core edge in the target deletion. -/
theorem ambientTrail_firstDart_edge_eq_target :
    (fusion.ambientTrail.firstDart fusion.ambientTrail_not_nil).edge =
      (retainedEdgeToAmbientEdge collar.targetData
        (collar.commonEdgeInTarget
          fusion.lineFusion.normal.returnData.lastOverlap.overlap.commonEdge)).1 := by
  rw [fusion.ambientTrail_firstDart_edge]
  change
    (retainedEdgeToAmbientEdge collar.sourceData
      (collar.commonEdgeInSource
        fusion.lineFusion.normal.returnData.lastOverlap.overlap.commonEdge)).1 = _
  exact congrArg Subtype.val
    (collar.retainedEdgeToAmbientEdge_commonEdgeInSource_eq_target
      fusion.lineFusion.normal.returnData.lastOverlap.overlap.commonEdge)

/-- The outgoing edge is likewise canonically represented in the target
deletion. -/
theorem ambientTrail_lastDart_edge_eq_target :
    (fusion.ambientTrail.lastDart fusion.ambientTrail_not_nil).edge =
      (retainedEdgeToAmbientEdge collar.targetData
        (collar.commonEdgeInTarget
          fusion.lineFusion.normal.launchSupportEdge.1)).1 := by
  rw [fusion.ambientTrail_lastDart_edge]
  change
    (retainedEdgeToAmbientEdge collar.sourceData
      (collar.commonEdgeInSource
        fusion.lineFusion.normal.launchSupportEdge.1)).1 = _
  exact congrArg Subtype.val
    (collar.retainedEdgeToAmbientEdge_commonEdgeInSource_eq_target
      fusion.lineFusion.normal.launchSupportEdge.1)

end CompanionCrossPairFusionPrimalTrail

/-- Canonically cap and lift the coherent line path. The lifted trail uses
exactly the primal edges represented by the line path. -/
theorem CompanionCrossPairFusionLinePath.nonempty_primalTrail
    (lineFusion : CompanionCrossPairFusionLinePath collar start) :
    Nonempty (CompanionCrossPairFusionPrimalTrail collar start) := by
  let linePath := lineFusion.fused.path
  let retainedTrail := linePath.canonicalCappedPrimalLift
    lineFusion.fused.positive lineFusion.fused.isPrimalCoherent
  refine ⟨{
    lineFusion := lineFusion
    startVertex := linePath.oppositeFirstJunctionVertex
      lineFusion.fused.positive
    endVertex := linePath.oppositeLastJunctionVertex
      lineFusion.fused.positive
    retainedTrail := retainedTrail
    retainedTrail_isTrail := ?_
    retainedTrail_positive := ?_
    retainedTrail_edges_eq := ?_ }⟩
  · exact linePath.canonicalCappedPrimalLift_isTrail_of_isPath
      lineFusion.fused.positive lineFusion.fused.isPrimalCoherent
      lineFusion.fused.isPath
  · exact linePath.canonicalCappedPrimalLift_length_pos
      lineFusion.fused.positive lineFusion.fused.isPrimalCoherent
  · exact linePath.canonicalCappedPrimalLift_edges_eq_map_support
      lineFusion.fused.positive lineFusion.fused.isPrimalCoherent

/-- A normalized junction therefore supplies an exact retained primal
trail and its edge-simple ambient inclusion. -/
theorem CompanionCrossPairJunctionNormalForm.nonempty_fusionPrimalTrail
    (normal : CompanionCrossPairJunctionNormalForm collar start) :
    Nonempty (CompanionCrossPairFusionPrimalTrail collar start) := by
  rcases normal.nonempty_crossPairFusionLinePath with ⟨lineFusion⟩
  exact lineFusion.nonempty_primalTrail

/-- The cross-pair branch of a closed companion circuit now terminates in
an actual edge-simple primal trail. -/
theorem closedCircuit_exists_localCancellation_or_fusionPrimalTrail_or_edgePivot_or_threePairMonodromy
    (closed : Relation.TransGen
      (CompanionAdjacentEscapeTransition collar) start start) :
    Nonempty (CompanionCanonicalComponentDisjointClosure collar start) ∨
      Nonempty (CompanionCrossPairFusionPrimalTrail collar start) ∨
        Nonempty (CompanionSameOuterTargetAvoidingEdgePivot collar start) ∨
          Nonempty (CompanionThreePairMonodromy collar start) := by
  rcases
      closedCircuit_exists_localCancellation_or_fusionLinePath_or_edgePivot_or_threePairMonodromy
        closed with cancellation | lineFusion | pivot | monodromy
  · exact Or.inl cancellation
  · rcases lineFusion with ⟨fusion⟩
    exact Or.inr (Or.inl fusion.nonempty_primalTrail)
  · exact Or.inr (Or.inr (Or.inl pivot))
  · exact Or.inr (Or.inr (Or.inr monodromy))

end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
