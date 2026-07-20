import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAdjacentEscapeOutcome

/-!
# Direct adjacent-pair endgame

For a finite cubic graph, a Tait coloring of a one-edge deletion already
extends across the deleted edge by the global `F₂ × F₂` incidence sum.  Thus
the nontrivial minimality input is a Tait coloring of a two-adjacent-vertex
deletion, not a further completion theorem for an already colored
two-defect graph.  The four boundary requests of that deletion give the
exact interface: leaving the two-same-side sector supplies a two-vertex
bridge extension and hence an ambient Tait coloring.  This formulation keeps
the rotation-system, fusion, and all-face reentry data attached directly to
the graph-level contradiction they must produce.
-/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24DeletedEdgeTrail
open GoertzelV24FramedTrail
open GoertzelV24FourDefectBoundary
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoDefectParity
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

attribute [local instance]
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.fusionFaceNetworkGraphEdgeSetDecidableEq
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.fusionFaceNetworkRetainedVertexFintype
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.fusionFaceNetworkRetainedVertexDecidableEq

namespace GoertzelV24DirectAdjacentPairEndgame

/-- A Tait coloring of a one-edge deletion is already complete at the
starting coloring, and the common missing color restores the ambient graph.
No Kempe step is required. -/
theorem deletedEdgeColoring_completable_and_extends_without_step
    {u v : V} (huv : G.Adj u v)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedEdgeGraph G u v).EdgeColoring Color)
    (hC : IsTaitEdgeColoring (DeletedEdgeGraph G u v) C) :
    FramedTangleCompletable (unrestrictedDeletedEdgeFrame G u v) C ∧
      ∃ ambientColoring : G.EdgeColoring Color,
        IsTaitEdgeColoring G ambientColoring := by
  have hwell := unrestrictedDeletedEdgeFrame_wellFormed huv hcubic
  exact ⟨
    FramedTrailData.framedTangleCompletable_of_wellFormed
      (unrestrictedDeletedEdgeFrame G u v) hwell C hC,
    exists_taitColoring_of_deletedEdgeColoring huv hcubic C hC⟩

/-- Every Tait coloring of an adjacent-pair deletion in a graph-backed
vertex-minimal counterexample remains in the exact two-same-side boundary
sector. -/
theorem deletedAdjacentPairColoring_sameSidePairs_of_minimal
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C) :
    data.degreeTwoBoundaryData.colorWord C 0 =
        data.degreeTwoBoundaryData.colorWord C 1 ∧
      data.degreeTwoBoundaryData.colorWord C 2 =
        data.degreeTwoBoundaryData.colorWord C 3 := by
  exact
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.sameSidePairs_of_not_taitColorable
      data
    (incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic)
    (graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
      graphData minimal)
    C hC

/-- Exact direct contradiction contract for the adjacent-pair machine.  It
suffices to produce one Tait coloring of the standard two-vertex deletion
whose boundary requests leave the same-side sector. -/
theorem false_of_deletedAdjacentPairColoring_not_sameSide
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (hescape : ¬ (data.degreeTwoBoundaryData.colorWord C 0 =
          data.degreeTwoBoundaryData.colorWord C 1 ∧
        data.degreeTwoBoundaryData.colorWord C 2 =
          data.degreeTwoBoundaryData.colorWord C 3)) :
    False := by
  exact hescape
    (deletedAdjacentPairColoring_sameSidePairs_of_minimal
      graphData minimal data C hC)

/-- Bridge-extension form of the same direct contradiction contract. -/
theorem false_of_deletedAdjacentPair_bridgeExtension
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (bridge : Color)
    (hbridge : IsTwoVertexBridgeExtension
      (data.degreeTwoBoundaryData.colorWord C) bridge) :
    False := by
  exact
    (graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
      graphData minimal)
      (GoertzelV24AdjacentPairInsertion.AdjacentPairData.exists_taitColoring_of_deletedAdjacentPair_bridgeExtension
        data
        (incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
          graphData minimal.spherical.cubic)
        C hC bridge hbridge)

end GoertzelV24DirectAdjacentPairEndgame

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

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

/-- The direct same-side switch makes the fixed-collar companion recurrence
terminate at its initial state. -/
theorem exists_reachable_certifiedAdjacentEscapeTerminal
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (start : sourceNormal.KempeOrbitAdjacentEscape) :
    ∃ finish,
      Relation.ReflTransGen (CompanionAdjacentEscapeTransition collar)
          start finish ∧
        CertifiedAdjacentEscapeTerminal collar finish := by
  exact ⟨start, Relation.ReflTransGen.refl,
    collar.certifiedAdjacentEscapeTerminal_resolvedFusion start⟩

end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
