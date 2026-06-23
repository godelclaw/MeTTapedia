import Mettapedia.GraphTheory.FourColor.Theorem49SynthesisNonempty
import Mettapedia.GraphTheory.FourColor.Theorem49BoundaryProjection

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Positive same-embedding endpoint for the constructive source route.  It packages the
non-vacuous theorem-4.9 synthesis together with the corrected projected Definition 4.8 spanning
statements on the same boundary-aware embedding. -/
structure Theorem49BoundaryRootNonemptyProjectedSynthesis {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (C0 : G.EdgeColoring Color) : Prop where
  nonemptySynthesis : Theorem49BoundaryRootNonemptySynthesis emb C0
  projectedSubspace_eq_planarBoundaryZeroSubmodule :
    projectedKempeClosureGeneratorSubspace emb C0 = planarBoundaryZeroSubmodule emb
  projectedFamilySpan_eq_planarBoundaryZeroSubmodule :
    Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C0) =
      planarBoundaryZeroSubmodule emb

/-- Route-facing package for the raw Definition 4.8 quotient/error conclusion at a fixed
boundary-aware embedding.  It combines a Kirchhoff-valid raw finite-generator representative
with a decomposition of the original Kirchhoff chain by a boundary-kernel error. -/
abbrev Theorem49BoundaryRawQuotientErrorPackage {G : SimpleGraph V}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (C0 : G.EdgeColoring Color)
    (x : G.edgeSet → Color) : Prop :=
  (∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
    (terms : Set (G.edgeSet → Color)) ⊆
        kempeClosureGeneratorFamily emb.faceBoundary C0 ∧
      coeff.support ⊆ terms ∧
        (∑ y ∈ terms, coeff y • y) ∈
            kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) ∧
          boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
              (∑ y ∈ terms, coeff y • y) =
            boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x) ∧
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color))
        (boundaryError : G.edgeSet → Color),
      (terms : Set (G.edgeSet → Color)) ⊆
          kempeClosureGeneratorFamily emb.faceBoundary C0 ∧
        coeff.support ⊆ terms ∧
          (∑ y ∈ terms, coeff y • y) ∈
              kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) ∧
            boundaryError ∈
                kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) ⊓
                  LinearMap.ker
                    (boundaryZeroProjection
                      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
              (∑ y ∈ terms, coeff y • y) + boundaryError = x ∧
                boundaryZeroProjection
                  (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                    (∑ y ∈ terms, coeff y • y) =
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x

/-- The positive projected synthesis endpoint still carries the raw Kirchhoff representative and
boundary-kernel error decomposition supplied by the underlying theorem-4.9 synthesis package.
This is the route-facing access point for downstream geometric source arguments, so they need not
reach back into the raw projection layer. -/
theorem
    Theorem49BoundaryRootNonemptyProjectedSynthesis.rawKirchhoffRepresentative_and_boundaryKernelDecomposition
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C0 : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    ⟨h.nonemptySynthesis.synthesis.rawKirchhoffRepresentative hx,
      h.nonemptySynthesis.synthesis.rawBoundaryKernelDecomposition hx⟩

/-- Height-ordered witness-cover data gives the positive same-embedding endpoint as soon as the
selected-boundary-purified carrier is nonempty. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  refine
    { nonemptySynthesis := ?_
      projectedSubspace_eq_planarBoundaryZeroSubmodule :=
        projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_planarBoundaryHeightOrderedFacePeelWitnessData
          emb data C0 hC0
      projectedFamilySpan_eq_planarBoundaryZeroSubmodule :=
        span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_planarBoundaryHeightOrderedFacePeelWitnessData
          emb data C0 hC0 }
  exact
    { synthesis :=
        theorem49BoundaryRootSynthesis_of_planarBoundaryHeightOrderedFacePeelWitnessData
          (G := G) data C0 hC0
      carrier_nonempty := hCarrier }

/-- Height-ordered witness-cover data also give the route-facing raw quotient/error conclusion as
soon as the selected-boundary-purified carrier is nonempty. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_planarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryHeightOrderedFacePeelWitnessData
      data C0 hC0 hCarrier).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Finite collar-layer witness-cover data gives the positive same-embedding endpoint as soon as
the selected-boundary-purified carrier is nonempty. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  refine
    { nonemptySynthesis := ?_
      projectedSubspace_eq_planarBoundaryZeroSubmodule :=
        projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_planarBoundaryCollarLayerFacePeelWitnessData
          emb data C0 hC0
      projectedFamilySpan_eq_planarBoundaryZeroSubmodule :=
        span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_planarBoundaryCollarLayerFacePeelWitnessData
          emb data C0 hC0 }
  exact
    { synthesis :=
        theorem49BoundaryRootSynthesis_of_planarBoundaryCollarLayerFacePeelWitnessData
          (G := G) data C0 hC0
      carrier_nonempty := hCarrier }

/-- Finite collar-layer witness-cover data also give the route-facing raw quotient/error
conclusion as soon as the selected-boundary-purified carrier is nonempty. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_planarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryCollarLayerFacePeelWitnessData
      data C0 hC0 hCarrier).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Canonical-parent boundary-root interior-dual data gives the positive projected endpoint on
the same embedding. The construction passes through the height-ordered witness surface induced by
the parent package, keeping the selected-boundary carrier hypothesis explicit. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryInteriorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryInteriorDualBoundaryRootParentPeelData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryHeightOrderedFacePeelWitnessData
      (G := G)
      (planarBoundaryHeightOrderedFacePeelWitnessData_of_interiorDualHeightParentPeelData
        data.toInteriorDualHeightParentPeelData)
      C0 hC0 hCarrier

/-- Canonical-parent boundary-root interior-dual data also give the route-facing raw quotient/
error conclusion once the purified carrier is nonempty. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_planarBoundaryInteriorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryInteriorDualBoundaryRootParentPeelData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryInteriorDualBoundaryRootParentPeelData
      data C0 hC0 hCarrier).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Two-sided annulus-root parent data gives the same positive projected endpoint on the same
embedding.  The annulus boundary split is retained in the input surface, but the proved endpoint
still depends only on the induced interior parent payload together with a nonempty purified
carrier. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryInteriorDualBoundaryRootParentPeelData
      (G := G) data.interiorData C0 hC0 hCarrier

/-- Two-sided annulus-root parent data also give the route-facing raw quotient/error conclusion
once the purified carrier is nonempty. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_planarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusRootParentPeelData
      data C0 hC0 hCarrier).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

end Mettapedia.GraphTheory.FourColor
