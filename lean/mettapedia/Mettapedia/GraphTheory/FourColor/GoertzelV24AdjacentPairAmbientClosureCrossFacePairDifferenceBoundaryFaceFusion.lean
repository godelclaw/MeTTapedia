import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceBypass
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelAmbientClosureCycleIntersection

namespace SimpleGraph.Walk

universe u

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- Removing a prescribed dart edge from a simple cycle leaves the
complementary simple path between the dart endpoints, with an exact edge
decomposition of the original cycle. -/
theorem IsCycle.exists_complementaryPath_at_dart
    {base : V} {cycle : G.Walk base base}
    (hcycle : cycle.IsCycle) (root : G.Dart)
    (hroot : root.edge ∈ cycle.edges) :
    ∃ complement : G.Walk root.snd root.fst,
      complement.IsPath ∧
        root.edge ∉ complement.edges ∧
        ∀ edge : Sym2 V,
          edge ∈ cycle.edges ↔
            edge = root.edge ∨ edge ∈ complement.edges := by
  have hrootValue : s(root.fst, root.snd) ∈ cycle.edges := by
    simpa [SimpleGraph.Dart.edge] using hroot
  rcases hcycle.exists_oriented_at_edge hrootValue with
    ⟨oriented, horientedCycle, horientedSnd, horientedEdges⟩
  let complement : G.Walk root.snd root.fst :=
    oriented.tail.copy horientedSnd rfl
  have hcomplementPath : complement.IsPath := by
    simpa [complement] using horientedCycle.isPath_tail
  have horientedNotNil : ¬oriented.Nil := horientedCycle.not_nil
  have horientedEdgesNe : oriented.edges ≠ [] :=
    SimpleGraph.Walk.edges_eq_nil.not.mpr horientedNotNil
  have hheadEdge : oriented.edges.head horientedEdgesNe = root.edge := by
    simp [SimpleGraph.Dart.edge, horientedSnd,
      oriented.head_edges_eq_mk_start_snd horientedEdgesNe]
  have hcomplementEdges : complement.edges = oriented.edges.tail := by
    simp [complement, SimpleGraph.Walk.tail,
      SimpleGraph.Walk.edges_drop]
  have hdecomposition : root.edge :: complement.edges = oriented.edges := by
    rw [hcomplementEdges, ← hheadEdge]
    exact List.cons_head_tail horientedEdgesNe
  have hrootNotMem : root.edge ∉ complement.edges := by
    have hnodup := horientedCycle.edges_nodup
    rw [← hdecomposition, List.nodup_cons] at hnodup
    exact hnodup.1
  refine ⟨complement, hcomplementPath, hrootNotMem, ?_⟩
  intro edge
  rw [← horientedEdges edge, ← hdecomposition]
  simp

/-- A second simple path between the endpoints of a cycle edge fuses with
the complementary cycle path. If a witness edge occurs only on the cycle,
the two paths are distinct, so they contain subpaths forming a new simple
cycle. The prescribed edge is absent from the fused cycle. -/
theorem IsCycle.exists_bypassFusionCycle
    {base : V} {cycle : G.Walk base base}
    (hcycle : cycle.IsCycle) (root : G.Dart)
    (hrootCycle : root.edge ∈ cycle.edges)
    (bypass : G.Walk root.snd root.fst)
    (hbypass : bypass.IsPath)
    (hrootBypass : root.edge ∉ bypass.edges)
    (witness : Sym2 V)
    (hwitnessCycle : witness ∈ cycle.edges)
    (hwitnessRoot : witness ≠ root.edge)
    (hwitnessBypass : witness ∉ bypass.edges) :
    ∃ (fusionRoot : V) (fusion : G.Walk fusionRoot fusionRoot),
      fusion.IsCycle ∧
        root.edge ∉ fusion.edges ∧
        ∀ edge : Sym2 V, edge ∈ fusion.edges →
          edge ∈ cycle.edges ∨ edge ∈ bypass.edges := by
  rcases hcycle.exists_complementaryPath_at_dart root hrootCycle with
    ⟨complement, hcomplement, hrootComplement, hexact⟩
  have hwitnessComplement : witness ∈ complement.edges := by
    rcases (hexact witness).1 hwitnessCycle with hroot | hcomplementMem
    · exact False.elim (hwitnessRoot hroot)
    · exact hcomplementMem
  have hpathsNe : complement ≠ bypass := by
    intro hpaths
    apply hwitnessBypass
    rw [← hpaths]
    exact hwitnessComplement
  rcases hcomplement.exists_isCycle_of_ne hbypass hpathsNe with
    ⟨left, _right, cyclePart, bypassPart,
      hcyclePart, hbypassPart, hfusion⟩
  refine ⟨left, cyclePart.append bypassPart.reverse, hfusion, ?_, ?_⟩
  · intro hedge
    rw [SimpleGraph.Walk.edges_append,
      SimpleGraph.Walk.edges_reverse, List.mem_append,
      List.mem_reverse] at hedge
    rcases hedge with hcycleEdge | hbypassEdge
    · exact hrootComplement (hcyclePart.edges_subset hcycleEdge)
    · exact hrootBypass (hbypassPart.edges_subset hbypassEdge)
  · intro edge hedge
    rw [SimpleGraph.Walk.edges_append,
      SimpleGraph.Walk.edges_reverse, List.mem_append,
      List.mem_reverse] at hedge
    rcases hedge with hcycleEdge | hbypassEdge
    · exact Or.inl ((hexact edge).2
        (Or.inr (hcyclePart.edges_subset hcycleEdge)))
    · exact Or.inr (hbypassPart.edges_subset hbypassEdge)

end SimpleGraph.Walk

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
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

/-- If every edge of a retained walk maps into one ambient face boundary,
then every edge of the mapped ambient walk belongs to that boundary. -/
theorem retainedWalkToAmbient_edge_mem_orbitFaceBoundary
    {graphData : Data G} (data : AdjacentPairData G)
    {left right : retainedVertexSet data.firstVertex data.secondVertex}
    (walk : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk left right)
    (face : OrbitFace graphData.toRotationSystem)
    (hface : ∀ edge : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).edgeSet,
      edge.1 ∈ walk.edges →
        retainedEdgeToAmbientEdge data edge ∈
          orbitFaceBoundary graphData.toRotationSystem face)
    (edge : G.edgeSet)
    (hedge : edge.1 ∈ (data.retainedWalkToAmbient walk).edges) :
    edge ∈ orbitFaceBoundary graphData.toRotationSystem face := by
  rw [GoertzelV24AdjacentPairBoundary.AdjacentPairData.retainedWalkToAmbient,
    SimpleGraph.Walk.edges_map] at hedge
  rcases List.mem_map.mp hedge with
    ⟨retainedValue, hretainedMem, hmapped⟩
  let retainedEdge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet :=
    ⟨retainedValue, walk.edges_subset_edgeSet hretainedMem⟩
  have hretainedFace := hface retainedEdge hretainedMem
  have hedgeEq : retainedEdgeToAmbientEdge data retainedEdge = edge := by
    apply Subtype.ext
    change retainedValue.map Subtype.val = edge.1 at hmapped
    simpa [retainedEdge] using hmapped
  exact hedgeEq ▸ hretainedFace

/-- A retained simple bypass of the exact common cross edge fuses with each
irreducible ambient closure. The resulting two simple cycles avoid the cross,
and each uses edges only from its original closure or the bypass. -/
theorem CrossCentralExactFaceCutPair.exists_fusionCyclePair_of_retainedBypass
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (hprefixCycle :
      (data.oppositePortClosure pair.prefixTrail).IsCycle)
    (hsuffixCycle :
      (data.alternateOppositePortClosure pair.suffixTrail).IsCycle)
    (root : G.Dart)
    (hrootEdge : root.edge = (retainedEdgeToAmbientEdge data cross).1)
    (hrootFst : root.fst ∈
      retainedVertexSet data.firstVertex data.secondVertex)
    (hrootSnd : root.snd ∈
      retainedVertexSet data.firstVertex data.secondVertex)
    (bypass : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk
        ⟨root.snd, hrootSnd⟩ ⟨root.fst, hrootFst⟩)
    (hbypass : bypass.IsPath)
    (hcrossBypass :
      (cross : Sym2 (retainedVertexSet data.firstVertex
        data.secondVertex)) ∉ bypass.edges) :
    ∃ (firstRoot : V) (firstFusion : G.Walk firstRoot firstRoot)
        (secondRoot : V) (secondFusion : G.Walk secondRoot secondRoot),
      firstFusion.IsCycle ∧
        (retainedEdgeToAmbientEdge data cross).1 ∉ firstFusion.edges ∧
        (∀ edge : Sym2 V, edge ∈ firstFusion.edges →
          edge ∈ (data.oppositePortClosure pair.prefixTrail).edges ∨
            edge ∈ (data.retainedWalkToAmbient bypass).edges) ∧
        secondFusion.IsCycle ∧
        (retainedEdgeToAmbientEdge data cross).1 ∉ secondFusion.edges ∧
        (∀ edge : Sym2 V, edge ∈ secondFusion.edges →
          edge ∈
              (data.alternateOppositePortClosure pair.suffixTrail).edges ∨
            edge ∈ (data.retainedWalkToAmbient bypass).edges) := by
  let ambientBypass : G.Walk root.snd root.fst :=
    data.retainedWalkToAmbient bypass
  have hambientBypass : ambientBypass.IsPath :=
    data.retainedWalkToAmbient_isPath hbypass
  have hrootBypass : root.edge ∉ ambientBypass.edges := by
    rw [hrootEdge]
    intro hmem
    apply hcrossBypass
    exact
      (retainedEdgeToAmbientEdge_mem_retainedWalkToAmbient_edges_iff
        data bypass cross).1 hmem
  have hcentralBypass : centralEdgeValue data ∉ ambientBypass.edges :=
    data.centralEdgeValue_not_mem_retainedWalkToAmbient_edges bypass
  have hrootPrefix : root.edge ∈
      (data.oppositePortClosure pair.prefixTrail).edges := by
    rw [hrootEdge]
    exact pair.cross_mem_oppositePortClosure
  have hcrossSuffixTrail : cross.1 ∈ pair.suffixTrail.edges :=
    ((pair.retainedIntersectionExact cross.1).2 rfl).2
  have hcrossSuffix : (retainedEdgeToAmbientEdge data cross).1 ∈
      (data.alternateOppositePortClosure pair.suffixTrail).edges :=
    (retainedEdgeToAmbientEdge_mem_alternateOppositePortClosure_edges_iff
      pair.suffixTrail cross).2 hcrossSuffixTrail
  have hrootSuffix : root.edge ∈
      (data.alternateOppositePortClosure pair.suffixTrail).edges := by
    rw [hrootEdge]
    exact hcrossSuffix
  have hcentralRoot : centralEdgeValue data ≠ root.edge := by
    rw [hrootEdge]
    exact pair.edgesDistinct.symm
  rcases hprefixCycle.exists_bypassFusionCycle root hrootPrefix
      ambientBypass hambientBypass hrootBypass (centralEdgeValue data)
      (data.centralEdgeValue_mem_oppositePortClosure_edges pair.prefixTrail)
      hcentralRoot hcentralBypass with
    ⟨firstRoot, firstFusion, hfirstCycle, hfirstCross,
      hfirstSupport⟩
  rcases hsuffixCycle.exists_bypassFusionCycle root hrootSuffix
      ambientBypass hambientBypass hrootBypass (centralEdgeValue data)
      (data.centralEdgeValue_mem_alternateOppositePortClosure_edges
        pair.suffixTrail) hcentralRoot hcentralBypass with
    ⟨secondRoot, secondFusion, hsecondCycle, hsecondCross,
      hsecondSupport⟩
  exact ⟨firstRoot, firstFusion, secondRoot, secondFusion,
    hfirstCycle, by simpa [hrootEdge] using hfirstCross,
    hfirstSupport, hsecondCycle,
    by simpa [hrootEdge] using hsecondCross, hsecondSupport⟩

/-- On the irreducible exact-cycle branch, nontrivial compensated transfer
forces two cross-free fusion cycles. Each new cycle is supported by one old
exact closure together with edges of the selected remote face. -/
theorem CrossCentralExactFaceCutPair.exists_exactCrossSideClosedTransfer_remoteFaceFusion
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : GoertzelV24AdjacentPairBoundary.AdjacentPairData G)
    {cross : (DeletedAdjacentPairGraph G baseData.firstVertex
      baseData.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) cross)
    (hprefixCycle :
      ((baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).oppositePortClosure
          pair.prefixTrail).IsCycle)
    (hsuffixCycle :
      ((baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).alternateOppositePortClosure
          pair.suffixTrail).IsCycle) :
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
          (∀ port : Fin 4,
            boundaryEdge (baseData.rotationOrderedData graphData
                minimal.spherical.cubic minimal.vertexRotationCyclic) port ∉
              orbitFaceBoundary graphData.toRotationSystem
                (edgeCrossFaceCoordinateOrbitFace graphData
                  (retainedEdgeToAmbientEdge
                    (baseData.rotationOrderedData graphData
                      minimal.spherical.cubic minimal.vertexRotationCyclic)
                        cross) coordinate)) ∧
          ∃ (firstRoot : V) (firstFusion : G.Walk firstRoot firstRoot)
              (secondRoot : V) (secondFusion : G.Walk secondRoot secondRoot),
            firstFusion.IsCycle ∧
              (retainedEdgeToAmbientEdge
                (baseData.rotationOrderedData graphData
                  minimal.spherical.cubic minimal.vertexRotationCyclic)
                    cross).1 ∉ firstFusion.edges ∧
              (∀ edge : G.edgeSet, edge.1 ∈ firstFusion.edges →
                edge.1 ∈
                    ((baseData.rotationOrderedData graphData
                      minimal.spherical.cubic minimal.vertexRotationCyclic).oppositePortClosure
                        pair.prefixTrail).edges ∨
                  edge ∈ orbitFaceBoundary graphData.toRotationSystem
                    (edgeCrossFaceCoordinateOrbitFace graphData
                      (retainedEdgeToAmbientEdge
                        (baseData.rotationOrderedData graphData
                          minimal.spherical.cubic
                            minimal.vertexRotationCyclic) cross) coordinate)) ∧
              secondFusion.IsCycle ∧
              (retainedEdgeToAmbientEdge
                (baseData.rotationOrderedData graphData
                  minimal.spherical.cubic minimal.vertexRotationCyclic)
                    cross).1 ∉ secondFusion.edges ∧
              ∀ edge : G.edgeSet, edge.1 ∈ secondFusion.edges →
                edge.1 ∈
                    ((baseData.rotationOrderedData graphData
                      minimal.spherical.cubic minimal.vertexRotationCyclic).alternateOppositePortClosure
                        pair.suffixTrail).edges ∨
                  edge ∈ orbitFaceBoundary graphData.toRotationSystem
                    (edgeCrossFaceCoordinateOrbitFace graphData
                      (retainedEdgeToAmbientEdge
                        (baseData.rotationOrderedData graphData
                          minimal.spherical.cubic
                            minimal.vertexRotationCyclic) cross) coordinate)) := by
  rcases pair.exists_exactCrossSideClosedTransfer_remoteFaceBypass
      minimal baseData with
    ⟨coordinate, firstIndex, secondIndex, path, hpath, hcross,
      hcycle, hparity, hsource, hnotCentral, hremoteBypass⟩
  refine ⟨coordinate, firstIndex, secondIndex, path, hpath, hcross,
    hcycle, hparity, hsource, hnotCentral, ?_⟩
  intro hnontrivial
  rcases hremoteBypass hnontrivial with
    ⟨hboundary, root, hrootFst, hrootSnd, facePath, hrootEdge,
      _hrootFace, hfacePath, hcrossFacePath, hfaceEdges⟩
  rcases pair.exists_fusionCyclePair_of_retainedBypass
      hprefixCycle hsuffixCycle root hrootEdge hrootFst hrootSnd
        facePath hfacePath hcrossFacePath with
    ⟨firstRoot, firstFusion, secondRoot, secondFusion,
      hfirstCycle, hfirstCross, hfirstSupport,
      hsecondCycle, hsecondCross, hsecondSupport⟩
  refine ⟨hboundary, firstRoot, firstFusion, secondRoot, secondFusion,
    hfirstCycle, hfirstCross, ?_, hsecondCycle, hsecondCross, ?_⟩
  · intro edge hedge
    rcases hfirstSupport edge.1 hedge with hclosure | hbypass
    · exact Or.inl hclosure
    · exact Or.inr
        (retainedWalkToAmbient_edge_mem_orbitFaceBoundary
          (baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic) facePath
          (edgeCrossFaceCoordinateOrbitFace graphData
            (retainedEdgeToAmbientEdge
              (baseData.rotationOrderedData graphData minimal.spherical.cubic
                minimal.vertexRotationCyclic) cross) coordinate)
          hfaceEdges edge hbypass)
  · intro edge hedge
    rcases hsecondSupport edge.1 hedge with hclosure | hbypass
    · exact Or.inl hclosure
    · exact Or.inr
        (retainedWalkToAmbient_edge_mem_orbitFaceBoundary
          (baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic) facePath
          (edgeCrossFaceCoordinateOrbitFace graphData
            (retainedEdgeToAmbientEdge
              (baseData.rotationOrderedData graphData minimal.spherical.cubic
                minimal.vertexRotationCyclic) cross) coordinate)
          hfaceEdges edge hbypass)

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
