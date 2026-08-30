import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairInsertion
import Mettapedia.GraphTheory.FourColor.GoertzelV24CircuitKempeComponentPrimalCycle
import Mettapedia.GraphTheory.FourColor.GoertzelV24PrimalCycleFacialBond

/-!
# Facial bonds from circuit Kempe components in an adjacent-pair deletion

The circuit horn of a confined adjacent-pair Kempe lift is not merely a
line-graph annotation.  Its primal cycle maps injectively from the induced
deletion into the original graph.  In a graph-backed spherical map, the
existing primal circuit--facial bond theorem then supplies the exact two
connected face shores bounded by that cycle.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AdjacentPairCircuitKempeFacialBond

open SimpleGraph
open SimpleGraphDartRotation
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24CircuitKempeComponentPrimalCycle
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedTrail
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PrimalCycleFacialBond
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24TwoEdgeCutMinimality

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

/-- Map a closed walk in an adjacent-pair deletion back into the original
graph by the canonical retained-vertex embedding. -/
def deletedCycleToAmbient (data : AdjacentPairData G)
    {start : retainedVertexSet data.firstVertex data.secondVertex}
    (cycle : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk start start) :
    G.Walk start.1 start.1 :=
  (cycle.map
    (GoertzelV24AdjacentPairInsertion.AdjacentPairData.retainedGraphEmbedding
      data).toHom).copy rfl rfl

/-- Injectivity of retained-vertex inclusion preserves simple cycles. -/
theorem deletedCycleToAmbient_isCycle (data : AdjacentPairData G)
    {start : retainedVertexSet data.firstVertex data.secondVertex}
    {cycle : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk start start} (hcycle : cycle.IsCycle) :
    (deletedCycleToAmbient data cycle).IsCycle := by
  simpa only [deletedCycleToAmbient, SimpleGraph.Walk.isCycle_copy] using
    hcycle.map
      (GoertzelV24AdjacentPairInsertion.AdjacentPairData.retainedGraphEmbedding
        data).injective

/-- The circuit horn in an adjacent-pair deletion yields an ambient simple
cycle whose exact facial sides are both connected. -/
theorem exists_ambientPrimalCycle_faceSetBond_of_deleted_isCircuitKempeComponent
    (graphData : Data G)
    (hclass : BridgelessSphericalCubicMapData
      graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (data : AdjacentPairData G)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    {a b : Color}
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (hcircuit : IsCircuitKempeComponent C a b K) :
    ∃ (start : V) (cycle : G.Walk start start),
      cycle.IsCycle ∧
        ∃ faces : Finset (OrbitFace graphData.toRotationSystem),
          (∀ dart : graphData.toRotationSystem.D,
            (graphData.toRotationSystem.edgeOf dart).1 ∈ cycle.edges ↔
              ((dartOrbitFace graphData.toRotationSystem dart ∈ faces ∧
                  dartOrbitFace graphData.toRotationSystem
                    (graphData.toRotationSystem.alpha dart) ∉ faces) ∨
                (dartOrbitFace graphData.toRotationSystem dart ∉ faces ∧
                  dartOrbitFace graphData.toRotationSystem
                    (graphData.toRotationSystem.alpha dart) ∈ faces))) ∧
          ((orbitFaceDualGraph graphData).induce
            {face | face ∈ faces}).Connected ∧
          ((orbitFaceDualGraph graphData).induce
            {face | face ∉ faces}).Connected := by
  rcases exists_primalCycle_of_isCircuitKempeComponent C K hcircuit with
    ⟨deletedStart, deletedCycle, hdeletedCycle, _hcomponent⟩
  let ambientCycle := deletedCycleToAmbient data deletedCycle
  have hambientCycle : ambientCycle.IsCycle :=
    deletedCycleToAmbient_isCycle data hdeletedCycle
  rcases exists_faceSet_bond_of_isCycle
      graphData hclass htwoSided ambientCycle hambientCycle with
    ⟨faces, hseparator, hselectedConnected, hcomplementConnected⟩
  exact ⟨deletedStart.1, ambientCycle, hambientCycle, faces,
    hseparator, hselectedConnected, hcomplementConnected⟩

end

end GoertzelV24AdjacentPairCircuitKempeFacialBond

end Mettapedia.GraphTheory.FourColor
