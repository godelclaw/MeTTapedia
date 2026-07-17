import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFacePlanarBond
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceWalk

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24MinimalFaceIntersections
open GoertzelV24OrbitFaceWalk
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

/-- A face containing a retained edge and avoiding all five restored cut
edges supplies a simple bypass of that edge entirely inside the retained
deletion. Every edge of the bypass remains on the same quotient face. -/
theorem exists_retainedFaceBypass
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (face : OrbitFace graphData.toRotationSystem)
    (hcross : retainedEdgeToAmbientEdge data cross ∈
      orbitFaceBoundary graphData.toRotationSystem face)
    (hcentral : centralEdge data ∉
      orbitFaceBoundary graphData.toRotationSystem face)
    (hboundary : ∀ port : Fin 4, boundaryEdge data port ∉
      orbitFaceBoundary graphData.toRotationSystem face) :
    ∃ (root : G.Dart)
        (hrootFst : root.fst ∈
          retainedVertexSet data.firstVertex data.secondVertex)
        (hrootSnd : root.snd ∈
          retainedVertexSet data.firstVertex data.secondVertex)
        (path : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk ⟨root.snd, hrootSnd⟩
            ⟨root.fst, hrootFst⟩),
      root.edge = (retainedEdgeToAmbientEdge data cross).1 ∧
        dartOrbitFace graphData.toRotationSystem root = face ∧
        path.IsPath ∧
        (cross : Sym2 (retainedVertexSet data.firstVertex
          data.secondVertex)) ∉ path.edges ∧
        ∀ edge : (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).edgeSet,
          (edge : Sym2 (retainedVertexSet data.firstVertex
            data.secondVertex)) ∈ path.edges →
            retainedEdgeToAmbientEdge data edge ∈
              orbitFaceBoundary graphData.toRotationSystem face := by
  rcases (mem_orbitFaceBoundary_iff graphData.toRotationSystem face
      (retainedEdgeToAmbientEdge data cross)).1 hcross with
    ⟨root, hrootMem, hrootEdgeOf⟩
  change G.Dart at root
  have hrootFace : dartOrbitFace graphData.toRotationSystem root = face :=
    (mem_orbitFaceDarts_iff graphData.toRotationSystem face root).1 hrootMem
  have hrootEdge : root.edge = (retainedEdgeToAmbientEdge data cross).1 :=
    congrArg Subtype.val hrootEdgeOf
  have hsourceRetained :
      IsRetainedAmbientEdge data (retainedEdgeToAmbientEdge data cross) :=
    isRetainedAmbientEdge_of_ne data
      (retainedEdgeToAmbientEdge data cross)
      (by
        intro hvalue
        exact retainedEdgeToAmbientEdge_ne_centralEdge data cross
          (Subtype.ext hvalue))
      (by
        intro hvalue
        exact retainedEdgeToAmbientEdge_ne_boundaryEdge data cross 0
          (Subtype.ext hvalue))
      (by
        intro hvalue
        exact retainedEdgeToAmbientEdge_ne_boundaryEdge data cross 1
          (Subtype.ext hvalue))
      (by
        intro hvalue
        exact retainedEdgeToAmbientEdge_ne_boundaryEdge data cross 2
          (Subtype.ext hvalue))
      (by
        intro hvalue
        exact retainedEdgeToAmbientEdge_ne_boundaryEdge data cross 3
          (Subtype.ext hvalue))
  have hrootFstInSource : root.fst ∈
      ((retainedEdgeToAmbientEdge data cross).1 : Sym2 V) := by
    rw [← hrootEdge]
    simp [SimpleGraph.Dart.edge]
  have hrootSndInSource : root.snd ∈
      ((retainedEdgeToAmbientEdge data cross).1 : Sym2 V) := by
    rw [← hrootEdge]
    simp [SimpleGraph.Dart.edge]
  have hrootFst : root.fst ∈
      retainedVertexSet data.firstVertex data.secondVertex :=
    endpoints_mem_retainedVertexSet data
      (retainedEdgeToAmbientEdge data cross) hsourceRetained root.fst
        hrootFstInSource
  have hrootSnd : root.snd ∈
      retainedVertexSet data.firstVertex data.secondVertex :=
    endpoints_mem_retainedVertexSet data
      (retainedEdgeToAmbientEdge data cross) hsourceRetained root.snd
        hrootSndInSource
  rcases exists_rootedFaceBypass graphData minimal.facesTwoSided root with
    ⟨bypass, hbypassTrail, hrootNotMem, hbypassFace⟩
  have hbypassRetained : ∀ (edgeValue : Sym2 V)
      (hedge : edgeValue ∈ bypass.edges),
      IsRetainedAmbientEdge data
        ⟨edgeValue, bypass.edges_subset_edgeSet hedge⟩ := by
    intro edgeValue hedge
    let edge : G.edgeSet :=
      ⟨edgeValue, bypass.edges_subset_edgeSet hedge⟩
    have hfaceEdge : edge ∈
        orbitFaceBoundary graphData.toRotationSystem face := by
      rw [← hrootFace]
      exact hbypassFace edge hedge
    by_contra hnotRetained
    rcases (not_isRetainedAmbientEdge_iff data edge).1 hnotRetained with
      hcentralEdge | ⟨port, hboundaryEdge⟩
    · apply hcentral
      have hedgeEq : edge = centralEdge data := Subtype.ext hcentralEdge
      exact hedgeEq ▸ hfaceEdge
    · apply hboundary port
      have hedgeEq : edge = boundaryEdge data port :=
        Subtype.ext hboundaryEdge
      exact hedgeEq ▸ hfaceEdge
  have hbypassNotNil : ¬bypass.Nil :=
    SimpleGraph.Walk.not_nil_of_ne root.adj.ne.symm
  have hsupport : ∀ vertex ∈ bypass.support,
      vertex ∈ retainedVertexSet data.firstVertex data.secondVertex := by
    intro vertex hvertex
    rcases (bypass.mem_support_iff_exists_mem_edges_of_not_nil
        hbypassNotNil).1 hvertex with
      ⟨edgeValue, hedge, hvertexEdge⟩
    let edge : G.edgeSet :=
      ⟨edgeValue, bypass.edges_subset_edgeSet hedge⟩
    exact endpoints_mem_retainedVertexSet data edge
      (hbypassRetained edgeValue hedge) vertex hvertexEdge
  let induced := bypass.induce
    (retainedVertexSet data.firstVertex data.secondVertex) hsupport
  let retainedBypass : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk ⟨root.snd, hrootSnd⟩
        ⟨root.fst, hrootFst⟩ :=
    induced.copy (Subtype.ext rfl) (Subtype.ext rfl)
  have hambient : data.retainedWalkToAmbient retainedBypass = bypass := by
    change retainedBypass.map
      (SimpleGraph.Embedding.induce
        (retainedVertexSet data.firstVertex data.secondVertex)).toHom = bypass
    simpa [retainedBypass, induced] using
      (SimpleGraph.Walk.map_induce bypass hsupport)
  let path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk ⟨root.snd, hrootSnd⟩
        ⟨root.fst, hrootFst⟩ := retainedBypass.toPath
  have hpath : path.IsPath := by
    exact SimpleGraph.Path.isPath retainedBypass.toPath
  have hpathEdges : path.edges ⊆ retainedBypass.edges := by
    exact retainedBypass.edges_toPath_subset_edges
  have hcrossNotMem :
      (cross : Sym2 (retainedVertexSet data.firstVertex
        data.secondVertex)) ∉ path.edges := by
    intro hcrossPath
    have hcrossRetained := hpathEdges hcrossPath
    have hcrossAmbient :=
      (retainedEdgeToAmbientEdge_mem_retainedWalkToAmbient_edges_iff
        data retainedBypass cross).2 hcrossRetained
    rw [hambient] at hcrossAmbient
    apply hrootNotMem
    rw [hrootEdge]
    exact hcrossAmbient
  refine ⟨root, hrootFst, hrootSnd, path, hrootEdge, hrootFace,
    hpath, hcrossNotMem, ?_⟩
  intro edge hedge
  have hretained := hpathEdges hedge
  have hambientMem :=
    (retainedEdgeToAmbientEdge_mem_retainedWalkToAmbient_edges_iff
      data retainedBypass edge).2 hretained
  rw [hambient] at hambientMem
  rw [← hrootFace]
  exact hbypassFace (retainedEdgeToAmbientEdge data edge) hambientMem

/-- In rotation order, every exact cross-side closure whose compensated
transfer is nontrivial carries a second, facial bypass of the rejected cross.
The bypass lies wholly in the retained deletion and on the selected remote
face. -/
theorem CrossCentralExactFaceCutPair.exists_exactCrossSideClosedTransfer_remoteFaceBypass
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : GoertzelV24AdjacentPairBoundary.AdjacentPairData G)
    {cross : (DeletedAdjacentPairGraph G baseData.firstVertex
      baseData.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) cross) :
    ∃ (coordinate : Bool) (firstIndex secondIndex : Fin 2)
        (path : (DeletedAdjacentPairGraph G baseData.firstVertex
          baseData.secondVertex).Walk
            ((baseData.rotationOrderedData graphData minimal.spherical.cubic
              minimal.vertexRotationCyclic).retainedPort
                (firstSidePort firstIndex))
            ((baseData.rotationOrderedData graphData minimal.spherical.cubic
              minimal.vertexRotationCyclic).retainedPort
                (secondSidePort secondIndex))),
      path.IsPath ∧
        (cross : Sym2 (retainedVertexSet baseData.firstVertex
          baseData.secondVertex)) ∉ path.edges ∧
        ((baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic).crossSidePortClosure
            firstIndex secondIndex path).IsCycle ∧
        pair.centralReturnCoordinateParity coordinate
            firstIndex secondIndex = 1 ∧
        retainedEdgeToAmbientEdge
            (baseData.rotationOrderedData graphData minimal.spherical.cubic
              minimal.vertexRotationCyclic) cross ∈
          orbitFaceBoundary graphData.toRotationSystem
            (edgeCrossFaceCoordinateOrbitFace graphData
              (retainedEdgeToAmbientEdge
                (baseData.rotationOrderedData graphData minimal.spherical.cubic
                  minimal.vertexRotationCyclic) cross) coordinate) ∧
        centralEdge (baseData.rotationOrderedData graphData
            minimal.spherical.cubic minimal.vertexRotationCyclic) ∉
          orbitFaceBoundary graphData.toRotationSystem
            (edgeCrossFaceCoordinateOrbitFace graphData
              (retainedEdgeToAmbientEdge
                (baseData.rotationOrderedData graphData minimal.spherical.cubic
                  minimal.vertexRotationCyclic) cross) coordinate) ∧
        (rejectedCrossCentralReturnClosedTransfer firstIndex secondIndex ≠
              Equiv.refl (Bool × Bool) →
          ∃ (root : G.Dart)
              (hrootFst : root.fst ∈
                retainedVertexSet baseData.firstVertex baseData.secondVertex)
              (hrootSnd : root.snd ∈
                retainedVertexSet baseData.firstVertex baseData.secondVertex)
              (facePath : (DeletedAdjacentPairGraph G baseData.firstVertex
                baseData.secondVertex).Walk
                  ⟨root.snd, hrootSnd⟩ ⟨root.fst, hrootFst⟩),
            root.edge =
                (retainedEdgeToAmbientEdge
                  (baseData.rotationOrderedData graphData
                    minimal.spherical.cubic minimal.vertexRotationCyclic)
                      cross).1 ∧
              dartOrbitFace graphData.toRotationSystem root =
                edgeCrossFaceCoordinateOrbitFace graphData
                  (retainedEdgeToAmbientEdge
                    (baseData.rotationOrderedData graphData
                      minimal.spherical.cubic minimal.vertexRotationCyclic)
                        cross) coordinate ∧
              facePath.IsPath ∧
              (cross : Sym2 (retainedVertexSet baseData.firstVertex
                baseData.secondVertex)) ∉ facePath.edges ∧
              ∀ edge : (DeletedAdjacentPairGraph G baseData.firstVertex
                  baseData.secondVertex).edgeSet,
                (edge : Sym2 (retainedVertexSet baseData.firstVertex
                  baseData.secondVertex)) ∈ facePath.edges →
                  retainedEdgeToAmbientEdge
                      (baseData.rotationOrderedData graphData
                        minimal.spherical.cubic minimal.vertexRotationCyclic)
                        edge ∈
                    orbitFaceBoundary graphData.toRotationSystem
                      (edgeCrossFaceCoordinateOrbitFace graphData
                        (retainedEdgeToAmbientEdge
                          (baseData.rotationOrderedData graphData
                            minimal.spherical.cubic
                              minimal.vertexRotationCyclic) cross)
                        coordinate)) := by
  rcases pair.exists_exactCrossSideClosedTransfer_remoteFaceNormalForm
      minimal baseData with
    ⟨coordinate, firstIndex, secondIndex, path, hpath, hcross,
      hcycle, hparity, hsource, hnotCentral, hsignature⟩
  refine ⟨coordinate, firstIndex, secondIndex, path, hpath, hcross,
    hcycle, hparity, hsource, hnotCentral, ?_⟩
  intro hnontrivial
  have havoids := hsignature.1 hnontrivial
  have hboundary : ∀ port : Fin 4,
      boundaryEdge (baseData.rotationOrderedData graphData
          minimal.spherical.cubic minimal.vertexRotationCyclic) port ∉
        orbitFaceBoundary graphData.toRotationSystem
          (edgeCrossFaceCoordinateOrbitFace graphData
            (retainedEdgeToAmbientEdge
              (baseData.rotationOrderedData graphData minimal.spherical.cubic
                minimal.vertexRotationCyclic) cross) coordinate) := by
    intro port
    fin_cases port
    · simpa using havoids.1 (0 : Fin 2)
    · simpa using havoids.1 (1 : Fin 2)
    · simpa using havoids.2 (0 : Fin 2)
    · simpa using havoids.2 (1 : Fin 2)
  exact exists_retainedFaceBypass minimal
    (baseData.rotationOrderedData graphData minimal.spherical.cubic
      minimal.vertexRotationCyclic) cross
      (edgeCrossFaceCoordinateOrbitFace graphData
        (retainedEdgeToAmbientEdge
          (baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic) cross) coordinate)
      hsource hnotCentral hboundary

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
