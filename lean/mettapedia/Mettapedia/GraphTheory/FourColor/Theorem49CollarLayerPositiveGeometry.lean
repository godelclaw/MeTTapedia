import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSourceProjectionCore

/-!
# Height-ordered and collar-layer positive geometry surfaces

This module contains the fixed-embedding positive geometry predicates used by
the live closed-walk shell route, without the heavier replacement/audit
consequences.
-/

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Fixed-embedding replacement positive package using height-ordered witness-cover data. -/
def Theorem49HeightOrderedPositiveProjectedGeometryOn {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) : Prop :=
  ∃ _data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
    (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

/-- If an embedding has no height-ordered witness-cover data at all, it cannot carry the
height-ordered replacement package. -/
theorem not_heightOrderedPositiveProjectedGeometryOn_of_not_nonempty_heightOrderedFacePeelWitnessData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hData : ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb)) :
    ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  rintro ⟨data, _hCarrier⟩
  exact hData ⟨data⟩

/-- The height-ordered replacement package gives the nonempty projected synthesis endpoint on the
same embedding. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_heightOrderedPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49HeightOrderedPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases geom with ⟨data, hCarrier⟩
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryHeightOrderedFacePeelWitnessData
      data C0 hC0 hCarrier

/-- The height-ordered replacement package gives the route-facing raw quotient/error conclusion
at the same embedding, by first reaching the nonempty projected synthesis endpoint. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_heightOrderedPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49HeightOrderedPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_heightOrderedPositiveProjectedGeometryOn
      geom C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Graph-level replacement package using height-ordered witness-cover data and a nonempty
purified selected-boundary carrier on the same embedding. -/
structure Theorem49HeightOrderedPositiveProjectedGeometry (G : SimpleGraph V) where
  emb : PlaneEmbeddingWithBoundary G
  data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb
  carrier_nonempty : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

namespace Theorem49HeightOrderedPositiveProjectedGeometry

/-- Forget the graph-level height-ordered replacement package to its fixed-embedding predicate. -/
theorem on
    {G : SimpleGraph V} (geom : Theorem49HeightOrderedPositiveProjectedGeometry G) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn geom.emb := by
  exact ⟨geom.data, geom.carrier_nonempty⟩

/-- The graph-level height-ordered package is exactly existence of the fixed-embedding predicate. -/
theorem nonempty_iff_exists_on
    {G : SimpleGraph V} :
    Nonempty (Theorem49HeightOrderedPositiveProjectedGeometry G) ↔
      ∃ emb : PlaneEmbeddingWithBoundary G,
        Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  constructor
  · rintro ⟨geom⟩
    exact ⟨geom.emb, geom.on⟩
  · rintro ⟨emb, data, hCarrier⟩
    exact
      ⟨{ emb := emb,
          data := data,
          carrier_nonempty := hCarrier }⟩

/-- The height-ordered replacement package reaches the current nonempty projected synthesis
endpoint. -/
theorem exists_nonemptyProjectedSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49HeightOrderedPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 :=
  ⟨geom.emb,
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_heightOrderedPositiveProjectedGeometryOn
      geom.on C0 hC0⟩

/-- Graph-level height-ordered replacement package consuming the raw quotient/error endpoint on
its own embedding. -/
theorem rawQuotientErrorPackage
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49HeightOrderedPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices geom.emb)) :
    Theorem49BoundaryRawQuotientErrorPackage geom.emb C0 x := by
  exact
    theorem49BoundaryRawQuotientErrorPackage_of_heightOrderedPositiveProjectedGeometryOn
      geom.on C0 hC0 hx

/-- The graph-level height-ordered replacement package already reaches the full theorem-4.9
synthesis endpoint on its own embedding. -/
theorem boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49HeightOrderedPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis geom.emb C0 :=
  theorem49BoundaryRootSynthesis_of_planarBoundaryHeightOrderedFacePeelWitnessData
    geom.data C0 hC0

/-- The graph-level height-ordered replacement package also gives the graph-level full
theorem-4.9 synthesis endpoint. -/
theorem exists_boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49HeightOrderedPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 :=
  ⟨geom.emb, geom.boundaryRootSynthesis C0 hC0⟩

end Theorem49HeightOrderedPositiveProjectedGeometry

/-- Fixed-embedding replacement positive package using finite collar-layer witness-cover data. -/
def Theorem49CollarLayerPositiveProjectedGeometryOn {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) : Prop :=
  ∃ _data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
    (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

/-- If an embedding has no collar-layer witness-cover data at all, it cannot carry the finite
collar-layer replacement package. -/
theorem not_collarLayerPositiveProjectedGeometryOn_of_not_nonempty_collarLayerFacePeelWitnessData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hData : ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb)) :
    ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  rintro ⟨data, _hCarrier⟩
  exact hData ⟨data⟩

/-- The finite collar-layer replacement package gives the nonempty projected synthesis endpoint
on the same embedding. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_collarLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49CollarLayerPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases geom with ⟨data, hCarrier⟩
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryCollarLayerFacePeelWitnessData
      data C0 hC0 hCarrier

/-- The finite collar-layer replacement package gives the route-facing raw quotient/error
conclusion at the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_collarLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49CollarLayerPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_collarLayerPositiveProjectedGeometryOn
      geom C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- The finite collar-layer replacement package already reaches the full theorem-4.9 synthesis
endpoint on the same embedding. -/
theorem theorem49BoundaryRootSynthesis_of_collarLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49CollarLayerPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis emb C0 := by
  rcases geom with ⟨data, _hCarrier⟩
  exact theorem49BoundaryRootSynthesis_of_planarBoundaryCollarLayerFacePeelWitnessData data C0 hC0

/-- The height-ordered and finite collar-layer replacement packages are equivalent on a fixed
embedding.  The conversion from height to collars groups peeled faces by height; the reverse
conversion uses layer index as height. -/
theorem heightOrderedPositiveProjectedGeometryOn_iff_collarLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb ↔
      Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  constructor
  · rintro ⟨data, hCarrier⟩
    exact
      ⟨planarBoundaryCollarLayerFacePeelWitnessData_of_heightOrderedFacePeelWitnessData data,
        hCarrier⟩
  · rintro ⟨data, hCarrier⟩
    exact ⟨data.toHeightOrderedFacePeelWitnessData, hCarrier⟩

/-- A well-founded parent witness-cover package plus a local unblocked endpoint gives the
height-ordered replacement source by ranking parents with the canonical well-founded height. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    ⟨data.toPlanarBoundaryHeightOrderedFacePeelWitnessData,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint⟩

/-- The same well-founded parent witness-cover package also gives the finite-collar replacement
source by grouping the induced height-ordered data into collar layers. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  exact
    heightOrderedPositiveProjectedGeometryOn_iff_collarLayerPositiveProjectedGeometryOn.1
      (theorem49HeightOrderedPositiveProjectedGeometryOn_of_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
        data hEndpoint)

/-- A geometry-facing annulus collar package, together with the purified nonempty carrier on the
same embedding, is already a fixed-embedding finite-collar replacement positive source. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_annulusCollarGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  exact ⟨data.toPlanarBoundaryCollarLayerFacePeelWitnessData, hCarrier⟩

/-- The same annulus collar package also gives the height-ordered replacement source by forgetting
the finite layer index to its induced height order. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_annulusCollarGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact ⟨data.toPlanarBoundaryHeightOrderedFacePeelWitnessData, hCarrier⟩

/-- Annulus collar geometry plus a local unblocked interior endpoint gives the finite-collar
replacement package without separately repackaging carrier nonemptiness. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  exact
    theorem49CollarLayerPositiveProjectedGeometryOn_of_annulusCollarGeometry data
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint)

/-- Annulus collar geometry plus a local unblocked interior endpoint gives the height-ordered
replacement package directly. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_annulusCollarGeometry data
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint)

end Mettapedia.GraphTheory.FourColor
