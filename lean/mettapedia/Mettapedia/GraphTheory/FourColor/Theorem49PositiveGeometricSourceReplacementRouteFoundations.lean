import Mettapedia.GraphTheory.FourColor.Theorem49PositiveGeometricSourceReplacement
import Mettapedia.GraphTheory.FourColor.Theorem49PositiveGeometricSourceImpossibility

/-!
# Route-facing replacement positive geometric source packages for Theorem 4.9

The direct replacement surface in `Theorem49PositiveGeometricSourceReplacement` is formulated in
terms of annulus collar geometry plus a surviving purified selected-boundary carrier.  This file
connects that surface back to the honest closed-walk source shell and to the successor-cycle
boundary-order source shell used earlier in the route.  No one-collar or canonical-choice
condition is introduced here.
-/

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Fixed-embedding route-facing replacement package: honest closed-walk source data,
same-embedding annulus collar geometry, and a nonempty purified selected-boundary carrier. -/
def Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) : Prop :=
  ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
    ∃ _data : PlanarBoundaryAnnulusCollarGeometry emb,
      (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

/-- The route-facing positive closed-walk package cannot live in the facewise at-most-one
branch: its surviving purified carrier forces some face boundary to contain two distinct
interior edges.  The annulus collar data is retained in the package for the theorem-4.9 route,
but the obstruction itself only uses the honest closed-walk source and the live carrier. -/
theorem exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkAnnulusCollarPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb) :
    ∃ f : AmbientFace emb.faces,
      ∃ e₁ : G.edgeSet,
        e₁ ∈ emb.faceBoundary f.1 ∧
          e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
            ∃ e₂ : G.edgeSet,
              e₂ ∈ emb.faceBoundary f.1 ∧
                e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧ e₁ ≠ e₂ := by
  rcases geom with ⟨source, _data, hCarrier⟩
  exact
    exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkEmbeddingData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
      emb source.closedWalks hCarrier

/-- The route-facing closed-walk annulus-collar package is incompatible with the facewise
at-most-one interior-edge condition, since that condition forces the purified selected-boundary
interior carrier to be empty. -/
theorem not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_of_facewiseAtMostOneInteriorEdge
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) :
    ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb := by
  intro geom
  rcases geom with ⟨source, _data, hCarrier⟩
  have hEmpty :
      selectedBoundaryInteriorEdgeEndpointVertices emb = ∅ :=
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_of_closedWalkEmbeddingData_and_facewiseAtMostOneInteriorEdge
      emb source.closedWalks h_at_most_one_interior
  simp [hEmpty] at hCarrier

/-- The route-facing closed-walk annulus package gives the fixed-embedding finite-collar
replacement source. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusCollarPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  rcases geom with ⟨_source, data, hCarrier⟩
  exact theorem49CollarLayerPositiveProjectedGeometryOn_of_annulusCollarGeometry data hCarrier

/-- The route-facing closed-walk annulus package also gives the fixed-embedding height-ordered
replacement source. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusCollarPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  rcases geom with ⟨_source, data, hCarrier⟩
  exact theorem49HeightOrderedPositiveProjectedGeometryOn_of_annulusCollarGeometry data hCarrier

/-- The route-facing closed-walk annulus package reaches the current nonempty projected
synthesis endpoint through the direct annulus-collar bridge. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusCollarPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases geom with ⟨_source, data, hCarrier⟩
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_annulusCollarGeometry
      data hCarrier C0 hC0

/-- The route-facing closed-walk annulus package also reaches the route-facing raw Definition 4.8
quotient/error endpoint on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusCollarPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusCollarPositiveProjectedGeometryOn
      geom C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- The route-facing closed-walk annulus package already reaches the full theorem-4.9 synthesis
endpoint on the same embedding. -/
theorem theorem49BoundaryRootSynthesis_of_closedWalkAnnulusCollarPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis emb C0 := by
  exact
    theorem49BoundaryRootSynthesis_of_collarLayerPositiveProjectedGeometryOn
      (theorem49CollarLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusCollarPositiveProjectedGeometryOn
        geom)
      C0 hC0

/-- Honest closed-walk source data, annulus collar geometry, and a local unblocked endpoint
package the fixed-embedding route-facing replacement source. -/
theorem theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb := by
  exact
    ⟨source, data,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint⟩

/-- Honest closed-walk source data, annulus collar geometry, a local unblocked endpoint, and a
Tait coloring reach the nonempty projected theorem-4.9 synthesis endpoint directly. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusCollarPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
        source data hEndpoint)
      C0 hC0

/-- Honest closed-walk source data, annulus collar geometry, a local unblocked endpoint, and a
Tait coloring already reach the full theorem-4.9 synthesis endpoint on the same embedding. -/
theorem theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis emb C0 := by
  exact
    theorem49BoundaryRootSynthesis_of_closedWalkAnnulusCollarPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
        source data hEndpoint)
      C0 hC0

/-- Honest closed-walk source data, annulus collar geometry, a local unblocked endpoint, and a
Tait coloring also reach the route-facing raw Definition 4.8 quotient/error package for every
Kirchhoff chain on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      source data hEndpoint C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition
      hx

/-- Honest closed-walk source data, repaired previous-boundary witness geometry, and a local
unblocked endpoint package the fixed-embedding route-facing replacement source. -/
theorem theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_annulusPreviousBoundaryWitnessGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb := by
  exact
    theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      source data.toPlanarBoundaryAnnulusCollarGeometry hEndpoint

/-- Honest closed-walk source data, repaired previous-boundary witness geometry, a local
unblocked endpoint, and a Tait coloring reach the nonempty projected theorem-4.9 synthesis
endpoint directly. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusPreviousBoundaryWitnessGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusCollarPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_annulusPreviousBoundaryWitnessGeometry_and_hasUnblockedInteriorEndpoint
        source data hEndpoint)
      C0 hC0

/-- Honest closed-walk source data, repaired previous-boundary witness geometry, a local
unblocked endpoint, and a Tait coloring already reach the full theorem-4.9 synthesis endpoint on
the same embedding. -/
theorem theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusPreviousBoundaryWitnessGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis emb C0 := by
  exact
    theorem49BoundaryRootSynthesis_of_closedWalkAnnulusCollarPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_annulusPreviousBoundaryWitnessGeometry_and_hasUnblockedInteriorEndpoint
        source data hEndpoint)
      C0 hC0

/-- Honest closed-walk source data, repaired previous-boundary witness geometry, a local
unblocked endpoint, and a Tait coloring also reach the route-facing raw Definition 4.8
quotient/error package for every Kirchhoff chain on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_annulusPreviousBoundaryWitnessGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusPreviousBoundaryWitnessGeometry_and_hasUnblockedInteriorEndpoint
      source data hEndpoint C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition
      hx

/-- Honest closed-walk source data, explicit well-founded parent witness-cover data, a local
unblocked endpoint, and a Tait coloring reach the nonempty projected theorem-4.9 synthesis
endpoint directly.  The source is retained in the statement for route traceability, while the
positive geometric burden is carried by the acyclic witness-cover data. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (_source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      data hEndpoint C0 hC0

/-- Honest closed-walk source data, explicit well-founded parent witness-cover data, a local
unblocked endpoint, and a Tait coloring already reach the full theorem-4.9 synthesis endpoint
directly. -/
theorem theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (_source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (_hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis emb C0 := by
  exact
    theorem49BoundaryRootSynthesis_of_planarBoundaryHeightOrderedFacePeelWitnessData
      data.toPlanarBoundaryHeightOrderedFacePeelWitnessData C0 hC0

/-- Honest closed-walk source data, explicit well-founded parent witness-cover data, a local
unblocked endpoint, and a Tait coloring also reach the route-facing raw Definition 4.8
quotient/error package for every Kirchhoff chain on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      source data hEndpoint C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition
      hx

/-- Honest closed-walk source data, the stronger construction-side face-layer shell, a local
unblocked endpoint, and a Tait coloring reach the nonempty projected theorem-4.9 synthesis
endpoint directly.  Once this shell and the live endpoint survive on the same embedding, no
additional replacement-side lowering is needed. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (_source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusConstructionFaceLayerData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusConstructionFaceLayerData
      data
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint)
      C0 hC0

/-- Honest closed-walk source data, the stronger construction-side face-layer shell, a local
unblocked endpoint, and a Tait coloring also reach the route-facing raw Definition 4.8
quotient/error package for every Kirchhoff chain on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusConstructionFaceLayerData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
      source data hEndpoint C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition
      hx

/-- Honest closed-walk source data, the stronger selected-boundary-contact construction shell,
a local unblocked endpoint, and a Tait coloring reach the nonempty projected theorem-4.9
synthesis endpoint directly. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (_source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusConstructionBoundarySupportFaceData
      data
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint)
      C0 hC0

/-- Honest closed-walk source data, the stronger selected-boundary-contact construction shell,
a local unblocked endpoint, and a Tait coloring also reach the route-facing raw Definition 4.8
quotient/error package for every Kirchhoff chain on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
      source data hEndpoint C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition
      hx

/-- Existential honest closed-walk source data plus same-embedding well-founded parent
witness-cover data and a local unblocked endpoint reaches the current nonempty projected
theorem-4.9 synthesis endpoint. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
        HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with ⟨emb, source, data, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
        source data hEndpoint C0 hC0⟩

/-- Existential honest closed-walk source data plus same-embedding well-founded parent
witness-cover data and a local unblocked endpoint already reach the full theorem-4.9 synthesis
endpoint directly. -/
theorem exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
        HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 := by
  rcases h with ⟨emb, source, data, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
        source data hEndpoint C0 hC0⟩

/-- Honest closed-walk source data, explicit well-founded parent witness-cover data,
endpoint-support separation, a nonempty raw interior-edge endpoint carrier, and a Tait coloring
reach the nonempty projected theorem-4.9 synthesis endpoint directly.  This is the positive
replacement source surface that avoids deriving root-distance interior-dual data. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      source data
      (hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
        hEndpointDisjoint hRawCarrier)
      C0 hC0

/-- Honest closed-walk source data, explicit well-founded parent witness-cover data,
endpoint-support separation, a nonempty raw interior-edge endpoint carrier, and a Tait coloring
already reach the full theorem-4.9 synthesis endpoint directly. -/
theorem theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis emb C0 := by
  exact
    theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      source data
      (hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
        hEndpointDisjoint hRawCarrier)
      C0 hC0

/-- Honest closed-walk source data, explicit well-founded parent witness-cover data,
endpoint-support separation, a nonempty raw interior-edge endpoint carrier, and a Tait coloring
also reach the route-facing raw Definition 4.8 quotient/error package for every Kirchhoff chain
on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
      source data hEndpointDisjoint hRawCarrier C0 hC0)
      |>.rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Honest closed-walk source data, explicit well-founded parent witness-cover data,
endpoint-support separation, a nonempty interior edge, and a Tait coloring reach the nonempty
projected theorem-4.9 synthesis endpoint directly. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hInteriorCarrier : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
      source data hEndpointDisjoint
      (interiorEdgeEndpointSupport_nonempty_of_interiorEdgeSupport_nonempty
        (G := G) (emb := emb) hInteriorCarrier)
      C0 hC0

/-- Honest closed-walk source data, explicit well-founded parent witness-cover data,
endpoint-support separation, a nonempty interior edge, and a Tait coloring also reach the
route-facing raw Definition 4.8 quotient/error package for every Kirchhoff chain on the same
embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hInteriorCarrier : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeSupport
      source data hEndpointDisjoint hInteriorCarrier C0 hC0)
      |>.rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Existential honest closed-walk source data plus same-embedding well-founded parent
witness-cover data, endpoint-support separation, and a nonempty raw interior-edge endpoint carrier
reaches the current nonempty projected theorem-4.9 synthesis endpoint. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_with_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
          (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with ⟨emb, source, data, hEndpointDisjoint, hRawCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
        source data hEndpointDisjoint hRawCarrier C0 hC0⟩

/-- Existential honest closed-walk source data plus same-embedding well-founded parent
witness-cover data, endpoint-support separation, and a nonempty raw interior-edge endpoint
carrier already reach the full theorem-4.9 synthesis endpoint directly. -/
theorem exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_with_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
          (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 := by
  rcases h with ⟨emb, source, data, hEndpointDisjoint, hRawCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
        source data hEndpointDisjoint hRawCarrier C0 hC0⟩

/-- Successor-cycle source data, explicit well-founded parent witness-cover data, a local
unblocked endpoint, and a Tait coloring reach the nonempty projected theorem-4.9 synthesis
endpoint through the induced honest closed-walk source. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      source data hEndpoint C0 hC0

/-- Successor-cycle source data, explicit well-founded parent witness-cover data, a local
unblocked endpoint, and a Tait coloring already reach the full theorem-4.9 synthesis endpoint
through the induced honest closed-walk source. -/
theorem theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis emb C0 := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      source data hEndpoint C0 hC0

/-- Successor-cycle source data, explicit well-founded parent witness-cover data, a local
unblocked endpoint, and a Tait coloring also reach the route-facing raw Definition 4.8
quotient/error package through the induced honest closed-walk source. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      boundaryData dartCycles hboundaryArc data hEndpoint C0 hC0)
      |>.rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Successor-cycle source data, the stronger construction-side face-layer shell, a local
unblocked endpoint, and a Tait coloring reach the nonempty projected theorem-4.9 synthesis
endpoint through the induced honest closed-walk source. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : PlanarBoundaryAnnulusConstructionFaceLayerData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
      source data hEndpoint C0 hC0

/-- Successor-cycle source data, the stronger construction-side face-layer shell, a local
unblocked endpoint, and a Tait coloring also reach the route-facing raw Definition 4.8
quotient/error package through the induced honest closed-walk source. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : PlanarBoundaryAnnulusConstructionFaceLayerData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
      boundaryData dartCycles hboundaryArc data hEndpoint C0 hC0)
      |>.rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Successor-cycle source data, the stronger selected-boundary-contact construction shell,
a local unblocked endpoint, and a Tait coloring reach the nonempty projected theorem-4.9
synthesis endpoint through the induced honest closed-walk source. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
      source data hEndpoint C0 hC0

/-- Successor-cycle source data, the stronger selected-boundary-contact construction shell,
a local unblocked endpoint, and a Tait coloring also reach the route-facing raw Definition 4.8
quotient/error package through the induced honest closed-walk source. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
      boundaryData dartCycles hboundaryArc data hEndpoint C0 hC0)
      |>.rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Fixed-embedding route-facing replacement package: honest closed-walk source data, the
selected-boundary-contact construction shell, and a nonempty purified selected-boundary
carrier. -/
def Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) : Prop :=
  ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
    ∃ _data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb,
      (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

/-- Honest closed-walk source data, the selected-boundary-contact construction shell, and a
local unblocked endpoint package the fixed-embedding route-facing construction-shell replacement
source. -/
theorem theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb := by
  exact
    ⟨source, data,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint⟩

/-- The route-facing closed-walk selected-boundary-contact construction shell still cannot live
in the facewise at-most-one branch: its surviving purified carrier already forces some ambient
face boundary to contain two distinct interior edges. -/
theorem exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb) :
    ∃ f : AmbientFace emb.faces,
      ∃ e₁ : G.edgeSet,
        e₁ ∈ emb.faceBoundary f.1 ∧
          e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
            ∃ e₂ : G.edgeSet,
              e₂ ∈ emb.faceBoundary f.1 ∧
                e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧ e₁ ≠ e₂ := by
  rcases geom with ⟨source, _data, hCarrier⟩
  exact
    exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkEmbeddingData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
      emb source.closedWalks hCarrier

/-- The route-facing closed-walk selected-boundary-contact construction shell is incompatible
with the facewise at-most-one interior-edge condition, since that condition forces the purified
selected-boundary interior carrier to be empty. -/
theorem not_theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn_of_facewiseAtMostOneInteriorEdge
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) :
    ¬ Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb := by
  intro geom
  rcases geom with ⟨source, _data, hCarrier⟩
  have hEmpty :
      selectedBoundaryInteriorEdgeEndpointVertices emb = ∅ :=
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_of_closedWalkEmbeddingData_and_facewiseAtMostOneInteriorEdge
      emb source.closedWalks h_at_most_one_interior
  simp [hEmpty] at hCarrier

/-- The route-facing closed-walk selected-boundary-contact construction shell gives the
fixed-embedding height-ordered replacement source. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  rcases geom with ⟨_source, data, hCarrier⟩
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_planarBoundaryAnnulusConstructionBoundarySupportFaceData
      data hCarrier

/-- The route-facing closed-walk selected-boundary-contact construction shell also gives the
fixed-embedding finite-collar replacement source. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  exact
    heightOrderedPositiveProjectedGeometryOn_iff_collarLayerPositiveProjectedGeometryOn.1
      (theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
        geom)

/-- The route-facing closed-walk selected-boundary-contact construction shell reaches the
nonempty projected theorem-4.9 synthesis endpoint. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases geom with ⟨source, data, hCarrier⟩
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
      source data
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).2 hCarrier)
      C0 hC0

/-- The route-facing closed-walk selected-boundary-contact construction shell also reaches the
route-facing raw quotient/error endpoint on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
      geom C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Graph-level route-facing replacement package for honest closed-walk source data with the
same-embedding selected-boundary-contact construction shell and a surviving purified carrier. -/
structure Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry
    (G : SimpleGraph V) where
  emb : PlaneEmbeddingWithBoundary G
  source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb
  data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb
  carrier_nonempty : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

namespace Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry

/-- Forget the graph-level closed-walk selected-boundary-contact construction package to its
fixed-embedding predicate. -/
theorem on
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry G) :
    Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn geom.emb := by
  exact ⟨geom.source, geom.data, geom.carrier_nonempty⟩

/-- The graph-level closed-walk selected-boundary-contact construction package is exactly
existence of the fixed-embedding predicate. -/
theorem nonempty_iff_exists_on
    {G : SimpleGraph V} :
    Nonempty (Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry G) ↔
      ∃ emb : PlaneEmbeddingWithBoundary G,
        Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb := by
  constructor
  · rintro ⟨geom⟩
    exact ⟨geom.emb, geom.on⟩
  · rintro ⟨emb, source, data, hCarrier⟩
    exact
      ⟨{ emb := emb,
          source := source,
          data := data,
          carrier_nonempty := hCarrier }⟩

/-- Route-facing closed-walk selected-boundary-contact construction data canonically yields the
graph-level height-ordered replacement package. -/
noncomputable def toHeightOrderedPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry G) :
    Theorem49HeightOrderedPositiveProjectedGeometry G where
  emb := geom.emb
  data := geom.data.construction.toPlanarBoundaryHeightOrderedFacePeelWitnessData
  carrier_nonempty := geom.carrier_nonempty

/-- Route-facing closed-walk selected-boundary-contact construction data canonically yields the
graph-level finite-collar replacement package. -/
noncomputable def toCollarLayerPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry G) :
    Theorem49CollarLayerPositiveProjectedGeometry G :=
  geom.toHeightOrderedPositiveProjectedGeometry.toCollarLayerPositiveProjectedGeometry

/-- The route-facing closed-walk selected-boundary-contact construction package reaches the
nonempty projected synthesis endpoint. -/
theorem exists_nonemptyProjectedSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 :=
  ⟨geom.emb,
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
      geom.on C0 hC0⟩

/-- The route-facing closed-walk selected-boundary-contact construction package also consumes
the raw quotient/error endpoint on its own embedding. -/
theorem rawQuotientErrorPackage
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices geom.emb)) :
    Theorem49BoundaryRawQuotientErrorPackage geom.emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
      geom.on C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Once the route-facing closed-walk selected-boundary-contact construction package already
carries witness ownership on the induced annulus decomposition, it reaches the full theorem-4.9
synthesis endpoint on the same embedding. -/
theorem boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hwitness :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          (geom.data.toPlanarBoundaryAnnulusFaceLayerData.toPlanarBoundaryAnnulusDecomposition))) :
    Theorem49BoundaryRootSynthesis geom.emb C0 := by
  rcases hwitness with ⟨witnessData⟩
  exact theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusWitnessAssignment witnessData C0 hC0

/-- The route-facing closed-walk selected-boundary-contact construction package also reaches
the graph-level full theorem-4.9 synthesis endpoint once the induced annulus decomposition
carries witness ownership. -/
theorem exists_boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hwitness :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          (geom.data.toPlanarBoundaryAnnulusFaceLayerData.toPlanarBoundaryAnnulusDecomposition))) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 :=
  ⟨geom.emb, geom.boundaryRootSynthesis C0 hC0 hwitness⟩

end Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry

/-- Existential honest closed-walk source data plus same-embedding selected-boundary-contact
construction data and a surviving purified carrier package into the graph-level closed-walk
selected-boundary-contact replacement source. -/
theorem nonempty_theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, source, data, hCarrier⟩
  exact
    ⟨{ emb := emb,
        source := source,
        data := data,
        carrier_nonempty := hCarrier }⟩

/-- Existential honest closed-walk source data plus same-embedding selected-boundary-contact
construction data and a local unblocked endpoint package into the graph-level closed-walk
selected-boundary-contact replacement source. -/
theorem nonempty_theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb,
        HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, source, data, hEndpoint⟩
  exact
    ⟨{ emb := emb,
        source := source,
        data := data,
        carrier_nonempty :=
          (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
            emb).1 hEndpoint }⟩

/-- Fixed-embedding route-facing replacement package: successor-cycle boundary-order source data,
the selected-boundary-contact construction shell, selected-boundary arcs, and a nonempty
purified selected-boundary carrier. -/
def Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) : Prop :=
  ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
    ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

/-- The route-facing successor-cycle selected-boundary-contact construction package lowers to
the closed-walk selected-boundary-contact construction package on the same embedding. -/
theorem theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn_of_successorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb) :
    Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb := by
  rcases geom with ⟨boundaryData, dartCycles, data, hselected, hCarrier⟩
  exact
    ⟨PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hselected,
      data, hCarrier⟩

/-- The route-facing successor-cycle selected-boundary-contact construction shell likewise
forces some ambient face boundary to contain two distinct interior edges, by lowering to the
corresponding honest closed-walk package on the same embedding. -/
theorem exists_two_distinct_interior_edges_on_faceBoundary_of_successorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb) :
    ∃ f : AmbientFace emb.faces,
      ∃ e₁ : G.edgeSet,
        e₁ ∈ emb.faceBoundary f.1 ∧
          e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
            ∃ e₂ : G.edgeSet,
              e₂ ∈ emb.faceBoundary f.1 ∧
                e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧ e₁ ≠ e₂ := by
  exact
    exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn_of_successorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
        geom)

/-- The route-facing successor-cycle selected-boundary-contact construction shell is likewise
incompatible with the facewise at-most-one interior-edge condition. -/
theorem not_theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn_of_facewiseAtMostOneInteriorEdge
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) :
    ¬ Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb := by
  intro geom
  rcases geom with ⟨_boundaryData, dartCycles, _data, _hselected, hCarrier⟩
  have hEmpty :
      selectedBoundaryInteriorEdgeEndpointVertices emb = ∅ :=
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_of_dartSuccessorCycleEmbeddingData_and_facewiseAtMostOneInteriorEdge
      emb dartCycles h_at_most_one_interior
  simp [hEmpty] at hCarrier

/-- Successor-cycle source data, the selected-boundary-contact construction shell,
selected-boundary arcs, and a local unblocked endpoint package the fixed-embedding route-facing
successor-cycle construction-shell replacement source. -/
theorem theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb := by
  exact
    ⟨boundaryData, dartCycles, data, hboundaryArc,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint⟩

/-- The route-facing successor-cycle selected-boundary-contact construction shell gives the
fixed-embedding height-ordered replacement source. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_successorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn_of_successorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
        geom)

/-- The route-facing successor-cycle selected-boundary-contact construction shell also gives the
fixed-embedding finite-collar replacement source. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_successorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  exact
    theorem49CollarLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn_of_successorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
        geom)

/-- The route-facing successor-cycle selected-boundary-contact construction shell reaches the
nonempty projected theorem-4.9 synthesis endpoint. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn_of_successorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
        geom)
      C0 hC0

/-- The route-facing successor-cycle selected-boundary-contact construction shell also reaches
the route-facing raw quotient/error endpoint on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_successorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
      geom C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Graph-level route-facing replacement package for successor-cycle source data with the
same-embedding selected-boundary-contact construction shell and a surviving purified carrier. -/
structure Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry
    (G : SimpleGraph V) where
  emb : PlaneEmbeddingWithBoundary G
  boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb
  dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb
  data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb
  selectedBoundaryArc : ∀ f : AmbientFace emb.faces,
    (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
      |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f
  carrier_nonempty : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

namespace Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry

/-- Forget the graph-level successor-cycle selected-boundary-contact construction package to its
fixed-embedding predicate. -/
theorem on
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry G) :
    Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn geom.emb := by
  exact
    ⟨geom.boundaryData, geom.dartCycles, geom.data, geom.selectedBoundaryArc,
      geom.carrier_nonempty⟩

/-- The graph-level successor-cycle selected-boundary-contact construction package is exactly
existence of the fixed-embedding predicate. -/
theorem nonempty_iff_exists_on
    {G : SimpleGraph V} :
    Nonempty (Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry G) ↔
      ∃ emb : PlaneEmbeddingWithBoundary G,
        Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn emb := by
  constructor
  · rintro ⟨geom⟩
    exact ⟨geom.emb, geom.on⟩
  · rintro ⟨emb, boundaryData, dartCycles, data, hselected, hCarrier⟩
    exact
      ⟨{ emb := emb,
          boundaryData := boundaryData,
          dartCycles := dartCycles,
          data := data,
          selectedBoundaryArc := hselected,
          carrier_nonempty := hCarrier }⟩

/-- Lower the route-facing successor-cycle selected-boundary-contact construction package to
the honest closed-walk selected-boundary-contact construction shell. -/
noncomputable def toClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry G) :
    Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry G where
  emb := geom.emb
  source := PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
    geom.boundaryData geom.dartCycles geom.selectedBoundaryArc
  data := geom.data
  carrier_nonempty := geom.carrier_nonempty

/-- Route-facing successor-cycle selected-boundary-contact construction data canonically yields
the graph-level height-ordered replacement package. -/
noncomputable def toHeightOrderedPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry G) :
    Theorem49HeightOrderedPositiveProjectedGeometry G :=
  geom.toClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry.toHeightOrderedPositiveProjectedGeometry

/-- Route-facing successor-cycle selected-boundary-contact construction data canonically yields
the graph-level finite-collar replacement package. -/
noncomputable def toCollarLayerPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry G) :
    Theorem49CollarLayerPositiveProjectedGeometry G :=
  geom.toClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry.toCollarLayerPositiveProjectedGeometry

/-- The route-facing successor-cycle selected-boundary-contact construction package reaches the
nonempty projected synthesis endpoint. -/
theorem exists_nonemptyProjectedSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 :=
  ⟨geom.emb,
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
      geom.on C0 hC0⟩

/-- The route-facing successor-cycle selected-boundary-contact construction package also
consumes the raw quotient/error endpoint on its own embedding. -/
theorem rawQuotientErrorPackage
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices geom.emb)) :
    Theorem49BoundaryRawQuotientErrorPackage geom.emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn
      geom.on C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Once the route-facing successor-cycle selected-boundary-contact construction package already
carries witness ownership on the induced annulus decomposition, it reaches the full theorem-4.9
synthesis endpoint on the same embedding. -/
theorem boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hwitness :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          (geom.data.toPlanarBoundaryAnnulusFaceLayerData.toPlanarBoundaryAnnulusDecomposition))) :
    Theorem49BoundaryRootSynthesis geom.emb C0 := by
  rcases hwitness with ⟨witnessData⟩
  exact theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusWitnessAssignment witnessData C0 hC0

/-- The route-facing successor-cycle selected-boundary-contact construction package also reaches
the graph-level full theorem-4.9 synthesis endpoint once the induced annulus decomposition
carries witness ownership. -/
theorem exists_boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hwitness :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          (geom.data.toPlanarBoundaryAnnulusFaceLayerData.toPlanarBoundaryAnnulusDecomposition))) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 :=
  ⟨geom.emb, geom.boundaryRootSynthesis C0 hC0 hwitness⟩

end Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry

/-- Existential route-facing successor-cycle selected-boundary-contact construction data and a
surviving purified carrier package into the graph-level successor-cycle selected-boundary-contact
replacement source. -/
theorem nonempty_theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, boundaryData, dartCycles, data, hselected, hCarrier⟩
  exact
    ⟨{ emb := emb,
        boundaryData := boundaryData,
        dartCycles := dartCycles,
        data := data,
        selectedBoundaryArc := hselected,
        carrier_nonempty := hCarrier }⟩

/-- Existential route-facing successor-cycle selected-boundary-contact construction data and a
local unblocked endpoint package into the graph-level successor-cycle selected-boundary-contact
replacement source. -/
theorem nonempty_theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, boundaryData, dartCycles, data, hselected, hEndpoint⟩
  exact
    ⟨{ emb := emb,
        boundaryData := boundaryData,
        dartCycles := dartCycles,
        data := data,
        selectedBoundaryArc := hselected,
        carrier_nonempty :=
          (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
            emb).1 hEndpoint }⟩

/-- Fixed-embedding route-facing replacement package: honest closed-walk source data, the
construction-side face-layer shell, and a nonempty purified selected-boundary carrier. -/
def Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) : Prop :=
  ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
    ∃ _data : PlanarBoundaryAnnulusConstructionFaceLayerData emb,
      (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

/-- The route-facing closed-walk construction-face-layer package still cannot live in the
facewise at-most-one branch: its surviving purified carrier already forces some ambient face
boundary to contain two distinct interior edges. -/
theorem exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb) :
    ∃ f : AmbientFace emb.faces,
      ∃ e₁ : G.edgeSet,
        e₁ ∈ emb.faceBoundary f.1 ∧
          e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
            ∃ e₂ : G.edgeSet,
              e₂ ∈ emb.faceBoundary f.1 ∧
                e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧ e₁ ≠ e₂ := by
  rcases geom with ⟨source, _data, hCarrier⟩
  exact
    exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkEmbeddingData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
      emb source.closedWalks hCarrier

/-- The route-facing closed-walk construction-face-layer package is incompatible with the
facewise at-most-one interior-edge condition, since that condition forces the purified selected-
boundary interior carrier to be empty. -/
theorem not_theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn_of_facewiseAtMostOneInteriorEdge
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) :
    ¬ Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb := by
  intro geom
  rcases geom with ⟨source, _data, hCarrier⟩
  have hEmpty :
      selectedBoundaryInteriorEdgeEndpointVertices emb = ∅ :=
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_of_closedWalkEmbeddingData_and_facewiseAtMostOneInteriorEdge
      emb source.closedWalks h_at_most_one_interior
  simp [hEmpty] at hCarrier

/-- Honest closed-walk source data, the construction-side face-layer shell, and a local
unblocked endpoint package the fixed-embedding route-facing construction-shell replacement
source. -/
theorem theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusConstructionFaceLayerData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb := by
  exact
    ⟨source, data,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint⟩

/-- The stronger selected-boundary-contact construction shell lowers directly to the
route-facing closed-walk construction-face-layer package on the same embedding. -/
theorem theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb := by
  exact
    theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
      source data.toPlanarBoundaryAnnulusConstructionFaceLayerData hEndpoint

/-- The route-facing closed-walk construction-face-layer package gives the fixed-embedding
height-ordered replacement source. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  rcases geom with ⟨_source, data, hCarrier⟩
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_planarBoundaryAnnulusConstructionFaceLayerData
      data hCarrier

/-- The route-facing closed-walk construction-face-layer package also gives the fixed-embedding
finite-collar replacement source. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  exact
    heightOrderedPositiveProjectedGeometryOn_iff_collarLayerPositiveProjectedGeometryOn.1
      (theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
        geom)

/-- The route-facing closed-walk construction-face-layer package reaches the nonempty projected
theorem-4.9 synthesis endpoint. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases geom with ⟨source, data, hCarrier⟩
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
      source data
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).2 hCarrier)
      C0 hC0

/-- The route-facing closed-walk construction-face-layer package also reaches the route-facing
raw quotient/error endpoint on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
      geom C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Graph-level route-facing replacement package for honest closed-walk source data with the
same-embedding construction-face-layer shell and a surviving purified carrier. -/
structure Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry
    (G : SimpleGraph V) where
  emb : PlaneEmbeddingWithBoundary G
  source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb
  data : PlanarBoundaryAnnulusConstructionFaceLayerData emb
  carrier_nonempty : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

namespace Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry

/-- Forget the graph-level closed-walk construction-face-layer package to its fixed-embedding
predicate. -/
theorem on
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry G) :
    Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn geom.emb := by
  exact ⟨geom.source, geom.data, geom.carrier_nonempty⟩

/-- The graph-level closed-walk construction-face-layer package is exactly existence of the
fixed-embedding predicate. -/
theorem nonempty_iff_exists_on
    {G : SimpleGraph V} :
    Nonempty (Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry G) ↔
      ∃ emb : PlaneEmbeddingWithBoundary G,
        Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb := by
  constructor
  · rintro ⟨geom⟩
    exact ⟨geom.emb, geom.on⟩
  · rintro ⟨emb, source, data, hCarrier⟩
    exact
      ⟨{ emb := emb,
          source := source,
          data := data,
          carrier_nonempty := hCarrier }⟩

/-- Route-facing closed-walk construction-face-layer data canonically yields the graph-level
height-ordered replacement package. -/
noncomputable def toHeightOrderedPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry G) :
    Theorem49HeightOrderedPositiveProjectedGeometry G where
  emb := geom.emb
  data := geom.data.construction.toPlanarBoundaryHeightOrderedFacePeelWitnessData
  carrier_nonempty := geom.carrier_nonempty

/-- Route-facing closed-walk construction-face-layer data canonically yields the graph-level
finite-collar replacement package. -/
noncomputable def toCollarLayerPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry G) :
    Theorem49CollarLayerPositiveProjectedGeometry G :=
  geom.toHeightOrderedPositiveProjectedGeometry.toCollarLayerPositiveProjectedGeometry

/-- The route-facing closed-walk construction-face-layer package reaches the nonempty projected
synthesis endpoint. -/
theorem exists_nonemptyProjectedSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 :=
  ⟨geom.emb,
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
      geom.on C0 hC0⟩

/-- The route-facing closed-walk construction-face-layer package also consumes the raw
quotient/error endpoint on its own embedding. -/
theorem rawQuotientErrorPackage
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices geom.emb)) :
    Theorem49BoundaryRawQuotientErrorPackage geom.emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
      geom.on C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Once the route-facing closed-walk construction-face-layer package already carries witness
ownership on the resulting annulus decomposition, it reaches the full theorem-4.9 synthesis
endpoint on the same embedding. -/
theorem boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hwitness :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          geom.data.toPlanarBoundaryAnnulusFaceLayerData.toPlanarBoundaryAnnulusDecomposition)) :
    Theorem49BoundaryRootSynthesis geom.emb C0 := by
  rcases hwitness with ⟨witnessData⟩
  exact theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusWitnessAssignment witnessData C0 hC0

/-- The route-facing closed-walk construction-face-layer package also reaches the graph-level
full theorem-4.9 synthesis endpoint once the resulting annulus decomposition carries witness
ownership. -/
theorem exists_boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hwitness :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          geom.data.toPlanarBoundaryAnnulusFaceLayerData.toPlanarBoundaryAnnulusDecomposition)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 :=
  ⟨geom.emb, geom.boundaryRootSynthesis C0 hC0 hwitness⟩

end Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry

/-- Existential honest closed-walk source data plus same-embedding construction-face-layer data
and a surviving purified carrier package into the graph-level closed-walk
construction-face-layer replacement source. -/
theorem nonempty_theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionFaceLayerData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryAnnulusConstructionFaceLayerData emb,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, source, data, hCarrier⟩
  exact
    ⟨{ emb := emb,
        source := source,
        data := data,
        carrier_nonempty := hCarrier }⟩

/-- Existential honest closed-walk source data plus same-embedding construction-face-layer data
and a local unblocked endpoint package into the graph-level closed-walk
construction-face-layer replacement source. -/
theorem nonempty_theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryAnnulusConstructionFaceLayerData emb,
        HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, source, data, hEndpoint⟩
  exact
    ⟨{ emb := emb,
        source := source,
        data := data,
        carrier_nonempty :=
          (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
            emb).1 hEndpoint }⟩

/-- Existential honest closed-walk source data plus the stronger selected-boundary-contact
construction shell and a local unblocked endpoint also package into the graph-level
closed-walk construction-face-layer replacement source. -/
theorem nonempty_theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb,
        HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, source, data, hEndpoint⟩
  exact
    nonempty_theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
      ⟨emb, source, data.toPlanarBoundaryAnnulusConstructionFaceLayerData, hEndpoint⟩

/-- Fixed-embedding route-facing replacement package: successor-cycle boundary-order source data,
the construction-side face-layer shell, selected-boundary arcs, and a nonempty purified
selected-boundary carrier. -/
def Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) : Prop :=
  ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
    ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _data : PlanarBoundaryAnnulusConstructionFaceLayerData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

/-- The route-facing successor-cycle construction-face-layer package lowers to the closed-walk
construction-face-layer package on the same embedding. -/
theorem theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn_of_successorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb) :
    Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb := by
  rcases geom with ⟨boundaryData, dartCycles, data, hselected, hCarrier⟩
  exact
    ⟨PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hselected,
      data, hCarrier⟩

/-- The route-facing successor-cycle construction-face-layer package likewise forces some
ambient face boundary to contain two distinct interior edges, by lowering to the corresponding
honest closed-walk package on the same embedding. -/
theorem exists_two_distinct_interior_edges_on_faceBoundary_of_successorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb) :
    ∃ f : AmbientFace emb.faces,
      ∃ e₁ : G.edgeSet,
        e₁ ∈ emb.faceBoundary f.1 ∧
          e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
            ∃ e₂ : G.edgeSet,
              e₂ ∈ emb.faceBoundary f.1 ∧
                e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧ e₁ ≠ e₂ := by
  exact
    exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn_of_successorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
        geom)

/-- The route-facing successor-cycle construction-face-layer package is likewise incompatible
with the facewise at-most-one interior-edge condition. -/
theorem not_theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn_of_facewiseAtMostOneInteriorEdge
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) :
    ¬ Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb := by
  intro geom
  rcases geom with ⟨_boundaryData, dartCycles, _data, _hselected, hCarrier⟩
  have hEmpty :
      selectedBoundaryInteriorEdgeEndpointVertices emb = ∅ :=
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_of_dartSuccessorCycleEmbeddingData_and_facewiseAtMostOneInteriorEdge
      emb dartCycles h_at_most_one_interior
  simp [hEmpty] at hCarrier

/-- Successor-cycle source data, the construction-side face-layer shell, selected-boundary arcs,
and a local unblocked endpoint package the fixed-embedding route-facing successor-cycle
construction-shell replacement source. -/
theorem theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : PlanarBoundaryAnnulusConstructionFaceLayerData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb := by
  exact
    ⟨boundaryData, dartCycles, data, hboundaryArc,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint⟩

/-- The stronger selected-boundary-contact construction shell lowers directly to the
route-facing successor-cycle construction-face-layer package on the same embedding. -/
theorem theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb := by
  exact
    theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
      boundaryData dartCycles hboundaryArc
      data.toPlanarBoundaryAnnulusConstructionFaceLayerData hEndpoint

/-- The route-facing successor-cycle construction-face-layer package gives the fixed-embedding
height-ordered replacement source. -/
theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_successorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn_of_successorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
        geom)

/-- The route-facing successor-cycle construction-face-layer package also gives the
fixed-embedding finite-collar replacement source. -/
theorem theorem49CollarLayerPositiveProjectedGeometryOn_of_successorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb) :
    Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  exact
    theorem49CollarLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn_of_successorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
        geom)

/-- The route-facing successor-cycle construction-face-layer package reaches the nonempty
projected theorem-4.9 synthesis endpoint. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
      (theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn_of_successorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
        geom)
      C0 hC0

/-- The route-facing successor-cycle construction-face-layer package also reaches the
route-facing raw quotient/error endpoint on the same embedding. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_successorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
      geom C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Graph-level route-facing replacement package for successor-cycle source data with the
same-embedding construction-face-layer shell and a surviving purified carrier. -/
structure Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry
    (G : SimpleGraph V) where
  emb : PlaneEmbeddingWithBoundary G
  boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb
  dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb
  data : PlanarBoundaryAnnulusConstructionFaceLayerData emb
  selectedBoundaryArc :
    ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f
  carrier_nonempty : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

namespace Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry

/-- Forget the graph-level successor-cycle construction-face-layer package to its
fixed-embedding predicate. -/
theorem on
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry G) :
    Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn geom.emb := by
  exact
    ⟨geom.boundaryData, geom.dartCycles, geom.data, geom.selectedBoundaryArc,
      geom.carrier_nonempty⟩

/-- The graph-level successor-cycle construction-face-layer package is exactly existence of the
fixed-embedding predicate. -/
theorem nonempty_iff_exists_on
    {G : SimpleGraph V} :
    Nonempty (Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry G) ↔
      ∃ emb : PlaneEmbeddingWithBoundary G,
        Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn emb := by
  constructor
  · rintro ⟨geom⟩
    exact ⟨geom.emb, geom.on⟩
  · rintro ⟨emb, boundaryData, dartCycles, data, hselected, hCarrier⟩
    exact
      ⟨{ emb := emb,
          boundaryData := boundaryData,
          dartCycles := dartCycles,
          data := data,
          selectedBoundaryArc := hselected,
          carrier_nonempty := hCarrier }⟩

/-- Lower the route-facing successor-cycle construction-face-layer package to the honest
closed-walk source shell. -/
def toClosedWalkAnnulusBoundarySource
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry G) :
    PlanarBoundaryClosedWalkAnnulusBoundarySource geom.emb :=
  PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
    geom.boundaryData geom.dartCycles geom.selectedBoundaryArc

/-- Route-facing successor-cycle construction-face-layer data canonically yields the graph-level
closed-walk construction-face-layer replacement package. -/
def toClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry G) :
    Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry G where
  emb := geom.emb
  source := geom.toClosedWalkAnnulusBoundarySource
  data := geom.data
  carrier_nonempty := geom.carrier_nonempty

/-- Route-facing successor-cycle construction-face-layer data canonically yields the graph-level
height-ordered replacement package. -/
noncomputable def toHeightOrderedPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry G) :
    Theorem49HeightOrderedPositiveProjectedGeometry G :=
  geom.toClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry.toHeightOrderedPositiveProjectedGeometry

/-- Route-facing successor-cycle construction-face-layer data canonically yields the graph-level
finite-collar replacement package. -/
noncomputable def toCollarLayerPositiveProjectedGeometry
    {G : SimpleGraph V}
    (geom : Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry G) :
    Theorem49CollarLayerPositiveProjectedGeometry G :=
  geom.toClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry.toCollarLayerPositiveProjectedGeometry

/-- The route-facing successor-cycle construction-face-layer package reaches the nonempty
projected synthesis endpoint. -/
theorem exists_nonemptyProjectedSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 :=
  ⟨geom.emb,
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
      geom.on C0 hC0⟩

/-- The route-facing successor-cycle construction-face-layer package also consumes the raw
quotient/error endpoint on its own embedding. -/
theorem rawQuotientErrorPackage
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices geom.emb)) :
    Theorem49BoundaryRawQuotientErrorPackage geom.emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_successorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn
      geom.on C0 hC0).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Once the route-facing successor-cycle construction-face-layer package already carries
witness ownership on the resulting annulus decomposition, it reaches the full theorem-4.9
synthesis endpoint on the same embedding. -/
theorem boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hwitness :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          geom.data.toPlanarBoundaryAnnulusFaceLayerData.toPlanarBoundaryAnnulusDecomposition)) :
    Theorem49BoundaryRootSynthesis geom.emb C0 :=
  geom.toClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry.boundaryRootSynthesis
    C0 hC0 hwitness

/-- The route-facing successor-cycle construction-face-layer package also reaches the graph-level
full theorem-4.9 synthesis endpoint once the resulting annulus decomposition carries witness
ownership. -/
theorem exists_boundaryRootSynthesis
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (geom : Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hwitness :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          geom.data.toPlanarBoundaryAnnulusFaceLayerData.toPlanarBoundaryAnnulusDecomposition)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 :=
  ⟨geom.emb, geom.boundaryRootSynthesis C0 hC0 hwitness⟩

end Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry

/-- Existential successor-cycle construction-face-layer data with a surviving purified carrier
package into the graph-level successor-cycle construction-face-layer replacement source. -/
theorem nonempty_theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionFaceLayerData_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ _data : PlanarBoundaryAnnulusConstructionFaceLayerData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Nonempty (Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, boundaryData, data, dartCycles, hselected, hCarrier⟩
  exact
    ⟨{ emb := emb,
        boundaryData := boundaryData,
        dartCycles := dartCycles,
        data := data,
        selectedBoundaryArc := hselected,
        carrier_nonempty := hCarrier }⟩

/-- Existential successor-cycle construction-face-layer data with a local unblocked endpoint
package into the graph-level successor-cycle construction-face-layer replacement source. -/
theorem nonempty_theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ _data : PlanarBoundaryAnnulusConstructionFaceLayerData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, boundaryData, data, dartCycles, hselected, hEndpoint⟩
  exact
    ⟨{ emb := emb,
        boundaryData := boundaryData,
        dartCycles := dartCycles,
        data := data,
        selectedBoundaryArc := hselected,
        carrier_nonempty :=
          (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
            emb).1 hEndpoint }⟩

/-- Existential successor-cycle data plus the stronger selected-boundary-contact construction
shell and a local unblocked endpoint also package into the graph-level successor-cycle
construction-face-layer replacement source. -/
theorem nonempty_theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ _data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          HasUnblockedInteriorEndpoint emb) :
    Nonempty (Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry G) := by
  rcases h with ⟨emb, boundaryData, data, dartCycles, hselected, hEndpoint⟩
  exact
    nonempty_theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusConstructionFaceLayerData_and_hasUnblockedInteriorEndpoint
      ⟨emb, boundaryData, data.toPlanarBoundaryAnnulusConstructionFaceLayerData, dartCycles,
        hselected, hEndpoint⟩

/-- Existential successor-cycle source data plus same-embedding well-founded parent witness-cover
data and a local unblocked endpoint reaches the current nonempty projected theorem-4.9 synthesis
endpoint. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with ⟨emb, boundaryData, data, dartCycles, hboundaryArc, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hboundaryArc data hEndpoint C0 hC0⟩

/-- Existential successor-cycle source data plus same-embedding well-founded parent witness-cover
data and a local unblocked endpoint already reach the full theorem-4.9 synthesis endpoint
directly. -/
theorem exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 := by
  rcases h with ⟨emb, boundaryData, data, dartCycles, hboundaryArc, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
        boundaryData dartCycles hboundaryArc data hEndpoint C0 hC0⟩

/-- Successor-cycle source data, explicit well-founded parent witness-cover data,
endpoint-support separation, a nonempty raw interior-edge endpoint carrier, and a Tait coloring
reach the nonempty projected theorem-4.9 synthesis endpoint through the induced honest
closed-walk source. -/
theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
      source data hEndpointDisjoint hRawCarrier C0 hC0

/-- Successor-cycle source data, explicit well-founded parent witness-cover data,
endpoint-support separation, a nonempty raw interior-edge endpoint carrier, and a Tait coloring
already reach the full theorem-4.9 synthesis endpoint through the induced honest closed-walk
source. -/
theorem theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis emb C0 := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
      source data hEndpointDisjoint hRawCarrier C0 hC0

/-- Successor-cycle source data, explicit well-founded parent witness-cover data,
endpoint-support separation, a nonempty raw interior-edge endpoint carrier, and a Tait coloring
also reach the route-facing raw Definition 4.8 quotient/error package through the induced honest
closed-walk source. -/
theorem theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
      boundaryData dartCycles hboundaryArc data hEndpointDisjoint hRawCarrier C0 hC0)
      |>.rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

/-- Existential successor-cycle source data plus same-embedding well-founded parent witness-cover
data, endpoint-support separation, and a nonempty raw interior-edge endpoint carrier reaches the
current nonempty projected theorem-4.9 synthesis endpoint. -/
theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_with_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Disjoint (interiorEdgeEndpointSupport emb)
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
            (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  rcases h with
    ⟨emb, boundaryData, data, dartCycles, hboundaryArc, hEndpointDisjoint, hRawCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
        boundaryData dartCycles hboundaryArc data hEndpointDisjoint hRawCarrier C0 hC0⟩

/-- Existential successor-cycle source data plus same-embedding well-founded parent witness-cover
data, endpoint-support separation, and a nonempty raw interior-edge endpoint carrier already
reach the full theorem-4.9 synthesis endpoint directly. -/
theorem exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_with_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_direct
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ _data : PlanarBoundaryWellFoundedFacePeelWitnessData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          Disjoint (interiorEdgeEndpointSupport emb)
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
          (interiorEdgeEndpointSupport emb).Nonempty)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C0 := by
  rcases h with ⟨emb, boundaryData, data, dartCycles, hboundaryArc, hEndpointDisjoint,
    hRawCarrier⟩
  exact
    ⟨emb,
      theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_wellFoundedFacePeelWitnessData_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
        boundaryData dartCycles hboundaryArc data hEndpointDisjoint hRawCarrier C0 hC0⟩


end Mettapedia.GraphTheory.FourColor
