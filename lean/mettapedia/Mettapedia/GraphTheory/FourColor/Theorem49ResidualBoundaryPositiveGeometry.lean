import Mettapedia.GraphTheory.FourColor.Theorem49PlanarCollarPeeling
import Mettapedia.GraphTheory.FourColor.Theorem49SynthesisPeelBridge

/-!
# Lightweight residual-boundary positive geometry surface

This module exposes the residual/current-boundary positive package and its
direct theorem-4.9 synthesis bridge without importing the selector and
benchmark-heavy residual route files.
-/

namespace Mettapedia.GraphTheory.FourColor

variable {V F : Type*} [DecidableEq V] [DecidableEq F]

/-- Residual/current-boundary peeling data. The present implementation is intentionally thin: it
reuses the already formalized local explicit-remainder collar package. -/
abbrev ResidualBoundaryLayerFacePeelWitnessData {G : SimpleGraph V}
    (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet) :=
  LocalRemainderBoundaryCollarLayerFacePeelWitnessData allFaces faceBoundary

/-- Embedding-facing residual/current-boundary witness data. -/
abbrev PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) :=
  ResidualBoundaryLayerFacePeelWitnessData emb.faces.attach
    (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)

theorem theorem49BoundaryRootSynthesis_of_residualBoundaryLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootSynthesis_of_planarBoundaryCollarLayerFacePeelWitnessData
      (planarBoundaryCollarLayerFacePeelWitnessData_of_genericLocalRemainderBoundaryCollarLayerFacePeelWitnessData
        data)
      C₀ hC₀

/-- Fixed-embedding positive route using residual/current-boundary witness data
and a surviving purified endpoint carrier. -/
def Theorem49ResidualBoundaryPositiveProjectedGeometryOn {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) : Prop :=
  ∃ _data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb,
    (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

theorem theorem49BoundaryRootSynthesis_of_residualBoundaryPositiveProjectedGeometryOn
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases geom with ⟨data, _hCarrier⟩
  exact theorem49BoundaryRootSynthesis_of_residualBoundaryLayerFacePeelWitnessData data C₀ hC₀

end Mettapedia.GraphTheory.FourColor
