import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairOppositePortCircuit
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionTerminalTurns
import Mettapedia.GraphTheory.FourColor.GoertzelV24WalkFaceCut
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24WalkCycleParity
open GoertzelV24WalkFaceCut
open SimpleGraph
open SimpleGraphDartRotation

namespace GoertzelV24WalkFaceCut

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance walkFaceCutGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Every closed trail in a graph-backed vertex-minimal counterexample has an
exact binary face cut. The connected facial dual and facial spanning
hypotheses are discharged from the minimal spherical map. -/
theorem exists_orbitFaceLabeling_ne_alpha_iff_mem_edges_of_minimal
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {vertex : V} (walk : G.Walk vertex vertex)
    (htrail : walk.IsTrail) :
    ∃ labels : OrbitFace graphData.toRotationSystem → F2,
      orbitFaceBoundaryLinearMap graphData.toRotationSystem labels =
          walkEdgeParity walk ∧
        ∀ dart : graphData.toRotationSystem.D,
          labels (dartOrbitFace graphData.toRotationSystem dart) ≠
              labels (dartOrbitFace graphData.toRotationSystem
                (graphData.toRotationSystem.alpha dart)) ↔
            (graphData.toRotationSystem.edgeOf dart).1 ∈ walk.edges := by
  have hconnected : G.Connected := by
    rw [← GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
      G graphData]
    exact minimal.primalConnected
  have hdual := orbitFaceInteriorDual_connected
    graphData.toRotationSystem minimal.spherical.cubic
      minimal.primalConnected minimal.vertexRotationCyclic
  exact exists_orbitFaceLabeling_ne_alpha_iff_mem_edges_of_isTrail
    graphData minimal.facesTwoSided hdual hconnected minimal.spherical
      walk htrail

end

end GoertzelV24WalkFaceCut

namespace GoertzelV24AdjacentPairBoundary.AdjacentPairData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance oppositePortFaceCutGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The oriented central dart used to read the two local sides of an
opposite-port closure. -/
def oppositePortCentralDart (data : AdjacentPairData G) : G.Dart :=
  ⟨(data.firstVertex, data.secondVertex), data.centralAdjacent⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem oppositePortCentralDart_edge
    (data : AdjacentPairData G) :
    data.oppositePortCentralDart.edge =
      GoertzelV24AdjacentPairInsertion.AdjacentPairData.centralEdgeValue data :=
  rfl

/-- An opposite-port path in a graph-backed vertex-minimal counterexample
closes to an exact face cut. In particular, the two quotient faces on the
central edge receive different labels. -/
theorem exists_oppositePortClosure_exactFaceCut_of_minimal
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (hpath : path.IsPath) :
    ∃ labels : OrbitFace graphData.toRotationSystem → F2,
      orbitFaceBoundaryLinearMap graphData.toRotationSystem labels =
          walkEdgeParity (data.oppositePortClosure path) ∧
        (∀ dart : graphData.toRotationSystem.D,
          labels (dartOrbitFace graphData.toRotationSystem dart) ≠
              labels (dartOrbitFace graphData.toRotationSystem
                (graphData.toRotationSystem.alpha dart)) ↔
            (graphData.toRotationSystem.edgeOf dart).1 ∈
              (data.oppositePortClosure path).edges) ∧
        (∀ port : Fin 4,
          labels (dartOrbitFace graphData.toRotationSystem
              (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
                data port)) ≠
                labels (dartOrbitFace graphData.toRotationSystem
                  (graphData.toRotationSystem.alpha
                    (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
                      data port))) ↔
            port = 0 ∨ port = 2) ∧
        labels (dartOrbitFace graphData.toRotationSystem
            data.oppositePortCentralDart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha
              data.oppositePortCentralDart)) := by
  have hcycle := data.oppositePortClosure_isCycle path hpath
  rcases exists_orbitFaceLabeling_ne_alpha_iff_mem_edges_of_minimal
      graphData minimal (data.oppositePortClosure path) hcycle.isTrail with
    ⟨labels, hlabels, hexact⟩
  refine ⟨labels, hlabels, hexact, ?_, ?_⟩
  · intro port
    rw [hexact
      (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryPortDart
        data port)]
    simpa using data.boundaryEdgeValue_mem_oppositePortClosure_edges_iff
      path port
  apply (hexact data.oppositePortCentralDart).2
  simpa using data.centralEdgeValue_mem_oppositePortClosure_edges path

end

end GoertzelV24AdjacentPairBoundary.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
