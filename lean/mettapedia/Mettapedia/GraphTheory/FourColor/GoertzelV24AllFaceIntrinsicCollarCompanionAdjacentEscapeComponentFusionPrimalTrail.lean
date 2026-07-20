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
