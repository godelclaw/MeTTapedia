import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSourceProjectionCore
import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSourceRoute

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

theorem
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      projectedKempeClosureGeneratorSubspace emb C0 = planarBoundaryZeroSubmodule emb := by
  rcases
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
      (admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
        hG)
      C0 hC0 with
    ⟨emb, _data, hspan⟩
  exact ⟨emb, hspan⟩

theorem
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C0) =
        planarBoundaryZeroSubmodule emb := by
  rcases
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
      (admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
        hG)
      C0 hC0 with
    ⟨emb, _data, hspan⟩
  exact ⟨emb, hspan⟩

theorem
    exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
            (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
              (∀ f : AmbientFace emb.faces,
                ((emb.faceBoundary f.1).filter
                    (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                  (1 : ℕ)) ∧
                ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                  e ∈ emb.faceBoundary f.1 →
                    e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                    e ∈
                      boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                        boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary := by
  rcases hG with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, fallbackEdge, hfallback,
      hatMost, hboundaryRest⟩
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact ⟨emb, source, fallbackEdge, hfallback, hatMost, by
    intro f e he hi
    simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
      PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
      hboundaryRest f he hi⟩

theorem
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
            (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
              (∀ f : AmbientFace emb.faces,
                ((emb.faceBoundary f.1).filter
                    (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                  (1 : ℕ)) ∧
                ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                  e ∈ emb.faceBoundary f.1 →
                    e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                    e ∈
                      boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                        boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      projectedKempeClosureGeneratorSubspace emb C0 = planarBoundaryZeroSubmodule emb := by
  exact
    exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
      (exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace
        hG)
      C0 hC0

theorem
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
            (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
              (∀ f : AmbientFace emb.faces,
                ((emb.faceBoundary f.1).filter
                    (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                  (1 : ℕ)) ∧
                ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                  e ∈ emb.faceBoundary f.1 →
                    e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                    e ∈
                      boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                        boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C0) =
        planarBoundaryZeroSubmodule emb := by
  exact
    exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
      (exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace
        hG)
      C0 hC0

theorem
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
              (terms : Set (G.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary C0 ∧
                coeff.support ⊆ terms ∧
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                      (∑ y ∈ terms, coeff y • y) = z := by
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
      (admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
        hG)
      C0 hC0 verticesOf

theorem
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
            (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
              (∀ f : AmbientFace emb.faces,
                ((emb.faceBoundary f.1).filter
                    (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                  (1 : ℕ)) ∧
                ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                  e ∈ emb.faceBoundary f.1 →
                    e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                    e ∈
                      boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                        boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
              (terms : Set (G.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary C0 ∧
                coeff.support ⊆ terms ∧
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                      (∑ y ∈ terms, coeff y • y) = z := by
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
      (exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace
        hG)
      C0 hC0 verticesOf

theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) ⊓
            (chainDotBilinForm G.edgeSet).orthogonal
              (projectedKempeClosureGeneratorSubspace emb C0) =
          ⊥ := by
  exact
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
      (admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
        hG)
      C0 hC0 verticesOf

theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
            (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
              (∀ f : AmbientFace emb.faces,
                ((emb.faceBoundary f.1).filter
                    (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                  (1 : ℕ)) ∧
                ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                  e ∈ emb.faceBoundary f.1 →
                    e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                    e ∈
                      boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                        boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) ⊓
            (chainDotBilinForm G.edgeSet).orthogonal
              (projectedKempeClosureGeneratorSubspace emb C0) =
          ⊥ := by
  exact
    exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
      (exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace
        hG)
      C0 hC0 verticesOf

theorem
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          z ≠ 0 →
            ∃ p ∈ projectedKempeClosureGeneratorSubspace emb C0,
              chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) ≠ 0 := by
  exact
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
      (admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
        hG)
      C0 hC0 verticesOf

theorem
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
            (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
              (∀ f : AmbientFace emb.faces,
                ((emb.faceBoundary f.1).filter
                    (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                  (1 : ℕ)) ∧
                ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                  e ∈ emb.faceBoundary f.1 →
                    e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                    e ∈
                      boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                        boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          z ≠ 0 →
            ∃ p ∈ projectedKempeClosureGeneratorSubspace emb C0,
              chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) ≠ 0 := by
  exact
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
      (exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace
        hG)
      C0 hC0 verticesOf

theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C0,
            chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
            z = 0 := by
  exact
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
      (admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
        hG)
      C0 hC0 verticesOf

theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
            (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
              (∀ f : AmbientFace emb.faces,
                ((emb.faceBoundary f.1).filter
                    (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                  (1 : ℕ)) ∧
                ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                  e ∈ emb.faceBoundary f.1 →
                    e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                    e ∈
                      boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                        boundaryData.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C0,
            chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
            z = 0 := by
  exact
    exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_heightOrdered_direct
      (exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace
        hG)
      C0 hC0 verticesOf

end Mettapedia.GraphTheory.FourColor
