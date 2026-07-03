import Mathlib.Data.List.TakeWhile
import Mettapedia.GraphTheory.FourColor.Theorem49ForcingInteriorEdgeObstruction
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryPeeling
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryDegenerateCertificate
import Mettapedia.GraphTheory.FourColor.Theorem49ResidualBoundaryRoute
import Mettapedia.GraphTheory.FourColor.Theorem49PositiveGeometricSourceReplacementRoute
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusHonestGeometryRegression
import Mettapedia.GraphTheory.FourColor.Theorem49WheelWithInnerTriangleBenchmark

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

namespace Theorem49ForcingInteriorEdgeObstructionRegression

open Theorem49InteriorVerticesEndpointObstruction
open Theorem49ForcingInteriorEdgeObstruction
open Theorem49PlanarBoundaryAnnulusHonestGeometryRegression
open Theorem49PlanarBoundaryAnnulusWheelWitnessRegression

/-- The diamond-with-triangle calibration of the abstract forcing-edge witness. -/
def diamondWithTriangleForcingInteriorEdgeWitness :
    ForcingInteriorEdgeWitness diamondWithTriangleEmbedding where
  edge := dt12
  heInterior := dt12_mem_interiorEdgeSupport
  hforcing := by
    intro f hf
    exact exists_selectedBoundarySupport_of_dt12_mem_faceBoundary_diamondWithTriangle hf

/-- The named positive non-forcing condition fails on the diamond-with-triangle model. -/
theorem not_everyInteriorEdgeHasBoundaryFreeIncidentFace_diamondWithTriangle :
    ¬ EveryInteriorEdgeHasBoundaryFreeIncidentFace diamondWithTriangleEmbedding := by
  intro hfree
  exact
    not_nonempty_forcingInteriorEdgeWitness_of_everyInteriorEdgeHasBoundaryFreeIncidentFace
      hfree ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩

/-- The diamond-with-triangle model also cannot carry the selector form of the positive
non-forcing condition. -/
theorem not_nonempty_boundaryFreeIncidentFaceSelector_diamondWithTriangle :
    ¬ Nonempty (BoundaryFreeIncidentFaceSelector diamondWithTriangleEmbedding) := by
  exact
    (not_nonempty_boundaryFreeIncidentFaceSelector_iff_nonempty_forcingInteriorEdgeWitness).2
      ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩

/-- The diamond-with-triangle embedding satisfies the exact face-local hypothesis used by the
failed forcing-edge exclusion attempt: each face has at most one interior boundary edge. -/
theorem diamondWithTriangle_atMostOneInteriorEdgePerFace :
    ∀ f : AmbientFace diamondWithTriangleEmbedding.faces,
      ((diamondWithTriangleEmbedding.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport diamondWithTriangleEmbedding.faceBoundary
            diamondWithTriangleEmbedding.faces)).card ≤ 1 := by
  intro f
  rw [diamondWithTriangle_interiorEdgeSupport_eq_singleton]
  refine Finset.card_le_one_iff.2 ?_
  intro e e' he he'
  have he12 : e = dt12 := by
    simpa using (Finset.mem_filter.1 he).2
  have he'12 : e' = dt12 := by
    simpa using (Finset.mem_filter.1 he').2
  exact he12.trans he'12.symm

/-- The diamond-with-triangle embedding carries boundary reachability, honest closed walks, the
at-most-one-interior-edge-per-face condition, and a forcing interior-edge witness on the same
embedding. -/
theorem
    exists_embedding_reachability_and_closedWalkEmbedding_and_atMostOneInteriorEdge_and_forcingInteriorEdgeWitness_diamondWithTriangleGraph :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      ∃ _ : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ _ : PlanarBoundaryClosedWalkEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            ((emb.faceBoundary f.1).filter
                (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) ∧
            Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    ⟨diamondWithTriangleEmbedding,
      diamondWithTriangleAnnulusBoundaryReachabilityData,
      diamondWithTriangleClosedWalkEmbeddingData,
      diamondWithTriangle_atMostOneInteriorEdgePerFace,
      ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

/-- Consequently, the proposed universal forcing-edge exclusion theorem with reachability,
closed-walk embedding data, and at-most-one interior edge per face is false. -/
theorem
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_reachability_and_closedWalkEmbedding_and_atMostOneInteriorEdge_diamondWithTriangle :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph},
        PlanarBoundaryAnnulusBoundaryReachabilityData emb →
          PlanarBoundaryClosedWalkEmbeddingData emb →
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) →
              ¬ Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_exists_embedding_reachability_and_closedWalkEmbedding_and_atMostOneInteriorEdge_and_forcingInteriorEdgeWitness
      (G := diamondWithTriangleGraph)
      exists_embedding_reachability_and_closedWalkEmbedding_and_atMostOneInteriorEdge_and_forcingInteriorEdgeWitness_diamondWithTriangleGraph

/-- The chained-diamonds benchmark has genuine interior support: the two diamond diagonals
`cdt12` and `cdt45` are both interior edges. -/
theorem chainedDiamondsWithTriangle_interiorEdgeSupport_nonempty :
    (interiorEdgeSupport chainedDiamondsWithTriangleEmbedding.faceBoundary
      chainedDiamondsWithTriangleEmbedding.faces).Nonempty := by
  exact ⟨cdt12, cdt12_mem_interiorEdgeSupport⟩

theorem exists_selectedBoundarySupport_of_cdt12_mem_faceBoundary_chainedDiamondsWithTriangle
    {f : AmbientFace chainedDiamondsWithTriangleEmbedding.faces}
    (hf : cdt12 ∈ chainedDiamondsWithTriangleEmbedding.faceBoundary f.1) :
    ∃ b ∈ chainedDiamondsWithTriangleEmbedding.faceBoundary f.1,
      b ∈ selectedBoundarySupport chainedDiamondsWithTriangleEmbedding.faceBoundary
        chainedDiamondsWithTriangleEmbedding.faces chainedDiamondsWithTriangleEmbedding.faces := by
  obtain ⟨⟨i, hi⟩, hfmem⟩ := f
  interval_cases i
  · refine ⟨cdt02, ?_, cdt02_mem_selectedBoundarySupport⟩
    simp [chainedDiamondsWithTriangleEmbedding,
      chainedDiamondsWithTriangleFaceBoundary]
  · refine ⟨cdt13, ?_, cdt13_mem_selectedBoundarySupport⟩
    simp [chainedDiamondsWithTriangleEmbedding,
      chainedDiamondsWithTriangleFaceBoundary]
  · exfalso
    simp [chainedDiamondsWithTriangleEmbedding,
      chainedDiamondsWithTriangleFaceBoundary, cdt12, cdt35, cdt34, cdt45] at hf
  · exfalso
    simp [chainedDiamondsWithTriangleEmbedding,
      chainedDiamondsWithTriangleFaceBoundary, cdt12, cdt56, cdt46, cdt45] at hf
  · exfalso
    simp [chainedDiamondsWithTriangleEmbedding,
      chainedDiamondsWithTriangleFaceBoundary, cdt12, cdt78, cdt89, cdt97] at hf

/-- The first chained-diamond interior edge is forcing: every face incident to it already
contains selected-boundary support. -/
def chainedDiamondsWithTriangleForcingInteriorEdgeWitness :
    ForcingInteriorEdgeWitness chainedDiamondsWithTriangleEmbedding where
  edge := cdt12
  heInterior := cdt12_mem_interiorEdgeSupport
  hforcing := by
    intro f hf
    exact exists_selectedBoundarySupport_of_cdt12_mem_faceBoundary_chainedDiamondsWithTriangle hf

/-- Direct exercise of the source-fixed raw-cover parent constructor on a nondegenerate honest
benchmark.  If the canonical closed-walk source on the chained-diamonds graph satisfied the raw
canonical-parent cover premises, the constructor would produce parent peel data; the concrete
forcing interior edge `cdt12` rules that data out. -/
theorem false_of_chainedDiamondsClosedWalkSourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
    (peelFaces : Finset (AmbientFace chainedDiamondsWithTriangleEmbedding.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges
      chainedDiamondsWithTriangleEmbedding.faceBoundary
      chainedDiamondsWithTriangleEmbedding.faces)
    (hcoverRoots : RootSetCovers
      (interiorDualGraph chainedDiamondsWithTriangleEmbedding.faceBoundary
        chainedDiamondsWithTriangleEmbedding.faces)
      chainedDiamondsClosedWalkAnnulusBoundarySource.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated
      (interiorDualGraph chainedDiamondsWithTriangleEmbedding.faceBoundary
        chainedDiamondsWithTriangleEmbedding.faces)
      chainedDiamondsClosedWalkAnnulusBoundarySource.boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (chainedDiamondsWithTriangleEmbedding.faceBoundary f.1)
        (selectedBoundarySupport chainedDiamondsWithTriangleEmbedding.faceBoundary
          chainedDiamondsWithTriangleEmbedding.faces
          chainedDiamondsWithTriangleEmbedding.faces))
    (hcover : interiorEdgeSupport chainedDiamondsWithTriangleEmbedding.faceBoundary
        chainedDiamondsWithTriangleEmbedding.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique
        chainedDiamondsWithTriangleEmbedding.faceBoundary
        chainedDiamondsWithTriangleEmbedding.faces hunique
        (interiorDualSpanningForestRoot chainedDiamondsWithTriangleEmbedding.faceBoundary
          chainedDiamondsWithTriangleEmbedding.faces
          chainedDiamondsClosedWalkAnnulusBoundarySource.boundaryFaceRoots
          hcoverRoots hsepRoots)
        chainedDiamondsClosedWalkAnnulusBoundarySource.fallbackEdge)) :
    False := by
  let data :=
    interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
      chainedDiamondsClosedWalkAnnulusBoundarySource peelFaces hunique hcoverRoots
      hsepRoots hpeelInterior hcover
  exact
    false_of_interiorDualBoundaryRootParentPeelData data
      chainedDiamondsWithTriangleForcingInteriorEdgeWitness

/-- The nondegenerate chained-diamonds source cannot instantiate the source-fixed raw-cover
canonical-parent constructor. -/
theorem not_exists_chainedDiamondsClosedWalkSourceBoundaryFaceRootsCanonicalParentSharedEdgeCover :
    ¬ ∃ peelFaces : Finset (AmbientFace chainedDiamondsWithTriangleEmbedding.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges
        chainedDiamondsWithTriangleEmbedding.faceBoundary
        chainedDiamondsWithTriangleEmbedding.faces,
      ∃ hcoverRoots : RootSetCovers
        (interiorDualGraph chainedDiamondsWithTriangleEmbedding.faceBoundary
          chainedDiamondsWithTriangleEmbedding.faces)
        chainedDiamondsClosedWalkAnnulusBoundarySource.boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated
        (interiorDualGraph chainedDiamondsWithTriangleEmbedding.faceBoundary
          chainedDiamondsWithTriangleEmbedding.faces)
        chainedDiamondsClosedWalkAnnulusBoundarySource.boundaryFaceRoots,
        (∀ f ∈ peelFaces,
          Disjoint (chainedDiamondsWithTriangleEmbedding.faceBoundary f.1)
            (selectedBoundarySupport chainedDiamondsWithTriangleEmbedding.faceBoundary
              chainedDiamondsWithTriangleEmbedding.faces
              chainedDiamondsWithTriangleEmbedding.faces)) ∧
        interiorEdgeSupport chainedDiamondsWithTriangleEmbedding.faceBoundary
            chainedDiamondsWithTriangleEmbedding.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique
            chainedDiamondsWithTriangleEmbedding.faceBoundary
            chainedDiamondsWithTriangleEmbedding.faces hunique
            (interiorDualSpanningForestRoot chainedDiamondsWithTriangleEmbedding.faceBoundary
              chainedDiamondsWithTriangleEmbedding.faces
              chainedDiamondsClosedWalkAnnulusBoundarySource.boundaryFaceRoots
              hcoverRoots hsepRoots)
            chainedDiamondsClosedWalkAnnulusBoundarySource.fallbackEdge) := by
  rintro ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover⟩
  exact
    false_of_chainedDiamondsClosedWalkSourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
      peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover

/-- The same forcing edge on the chained-diamonds honest-source benchmark already blocks the
generic boundary-root adjacency-distance interior-dual package itself. -/
theorem not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_chainedDiamondsWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
      chainedDiamondsWithTriangleEmbedding.faces
      chainedDiamondsWithTriangleEmbedding.faceBoundary) := by
  exact
    not_nonempty_interiorDualBoundaryRootAdjDistancePeelData
      (emb := chainedDiamondsWithTriangleEmbedding)
      chainedDiamondsWithTriangleForcingInteriorEdgeWitness

/-- So the chained-diamonds honest closed-walk source inhabits the stronger local at-most-one
source package, but still does not force generic boundary-root adjacency-distance data. -/
theorem
    exists_closedWalkSource_with_atMostOneInteriorEdgePerFace_without_interiorDualBoundaryRootAdjDistancePeelData_chainedDiamondsWithTriangleGraph :
    (∃ emb : PlaneEmbeddingWithBoundary chainedDiamondsWithTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces →
            chainedDiamondsWithTriangleGraph.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : chainedDiamondsWithTriangleGraph.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) ∧
      ¬ Nonempty
        (InteriorDualBoundaryRootAdjDistancePeelData
          chainedDiamondsWithTriangleEmbedding.faces
          chainedDiamondsWithTriangleEmbedding.faceBoundary) := by
  exact
    ⟨exists_closedWalkSource_with_atMostOneInteriorEdgePerFace_chainedDiamondsWithTriangleGraph,
      not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_chainedDiamondsWithTriangle_via_forcingInteriorEdgeWitness⟩

/-- There is no theorem deriving generic boundary-root adjacency-distance interior-dual data
from the stronger honest closed-walk source plus at-most-one-interior-edge local package, even
on the fixed chained-diamonds benchmark. -/
theorem
    not_forall_nonempty_interiorDualBoundaryRootAdjDistancePeelData_of_closedWalkSource_with_atMostOneInteriorEdgePerFace_chainedDiamondsWithTriangleGraph :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary chainedDiamondsWithTriangleGraph,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∀ fallbackEdge : AmbientFace emb.faces → chainedDiamondsWithTriangleGraph.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) →
          (∀ f : AmbientFace emb.faces,
            ((emb.faceBoundary f.1).filter
                (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
              (1 : ℕ)) →
          (∀ (f : AmbientFace emb.faces) {e : chainedDiamondsWithTriangleGraph.edgeSet},
            e ∈ emb.faceBoundary f.1 →
              e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
              e ∈
                source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                  source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) →
          Nonempty
            (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) := by
  intro h
  exact
    not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_chainedDiamondsWithTriangle_via_forcingInteriorEdgeWitness
      (h chainedDiamondsWithTriangleEmbedding
        chainedDiamondsClosedWalkAnnulusBoundarySource
        chainedDiamondsCanonicalWitnessEdge
        chainedDiamondsCanonicalWitnessEdge_mem
        chainedDiamondsWithTriangle_atMostOneInteriorEdgePerFace
        chainedDiamonds_nonInteriorOnAmbient)

/-- The same forcing edge on the chained-diamonds honest-source benchmark also blocks the current
source-facing parent-oriented annulus-root package. -/
theorem not_nonempty_planarBoundaryAnnulusRootParentPeelData_chainedDiamondsWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData chainedDiamondsWithTriangleEmbedding) := by
  exact
    not_nonempty_planarBoundaryAnnulusRootParentPeelData
      (emb := chainedDiamondsWithTriangleEmbedding)
      chainedDiamondsWithTriangleForcingInteriorEdgeWitness

/-- So even the stronger chained-diamonds honest-source local package does not force the current
parent-oriented annulus-root target on the same embedding. -/
theorem
    exists_closedWalkSource_with_atMostOneInteriorEdgePerFace_without_planarBoundaryAnnulusRootParentPeelData_chainedDiamondsWithTriangleGraph :
    ∃ emb : PlaneEmbeddingWithBoundary chainedDiamondsWithTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces →
            chainedDiamondsWithTriangleGraph.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              (∀ (f : AmbientFace emb.faces) {e : chainedDiamondsWithTriangleGraph.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) ∧
              ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  refine
    ⟨chainedDiamondsWithTriangleEmbedding, chainedDiamondsClosedWalkAnnulusBoundarySource,
      chainedDiamondsCanonicalWitnessEdge, ?_⟩
  exact
    ⟨chainedDiamondsCanonicalWitnessEdge_mem,
      chainedDiamondsWithTriangle_atMostOneInteriorEdgePerFace,
      chainedDiamonds_nonInteriorOnAmbient,
      not_nonempty_planarBoundaryAnnulusRootParentPeelData_chainedDiamondsWithTriangle_via_forcingInteriorEdgeWitness⟩

/-- There is no theorem deriving the current parent-oriented annulus-root target from the stronger
honest closed-walk source plus at-most-one-interior-edge local package, even on the fixed
chained-diamonds benchmark. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_closedWalkSource_with_atMostOneInteriorEdgePerFace_chainedDiamondsWithTriangleGraph :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary chainedDiamondsWithTriangleGraph,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∀ fallbackEdge : AmbientFace emb.faces → chainedDiamondsWithTriangleGraph.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) →
          (∀ f : AmbientFace emb.faces,
            ((emb.faceBoundary f.1).filter
                (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
              (1 : ℕ)) →
          (∀ (f : AmbientFace emb.faces) {e : chainedDiamondsWithTriangleGraph.edgeSet},
            e ∈ emb.faceBoundary f.1 →
              e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
              e ∈
                source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                  source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) →
          Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  intro h
  exact
    not_nonempty_planarBoundaryAnnulusRootParentPeelData_chainedDiamondsWithTriangle_via_forcingInteriorEdgeWitness
      (h chainedDiamondsWithTriangleEmbedding
        chainedDiamondsClosedWalkAnnulusBoundarySource
        chainedDiamondsCanonicalWitnessEdge
        chainedDiamondsCanonicalWitnessEdge_mem
        chainedDiamondsWithTriangle_atMostOneInteriorEdgePerFace
        chainedDiamonds_nonInteriorOnAmbient)

theorem not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
      diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) := by
  exact
    not_nonempty_interiorDualBoundaryRootAdjDistancePeelData
      (emb := diamondWithTriangleEmbedding)
      diamondWithTriangleForcingInteriorEdgeWitness

theorem not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData
      diamondWithTriangleEmbedding) := by
  exact
    not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData
      (emb := diamondWithTriangleEmbedding)
      diamondWithTriangleForcingInteriorEdgeWitness

theorem not_nonempty_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData
      diamondWithTriangleEmbedding) := by
  exact
    not_nonempty_planarBoundaryAnnulusRootParentPeelData
      (emb := diamondWithTriangleEmbedding)
      diamondWithTriangleForcingInteriorEdgeWitness

/-- The genuine cyclic diamond benchmark already carries the final theorem-4.9 synthesis
endpoint under its explicit Tait coloring while still exhibiting a forcing interior edge. -/
theorem
    exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_and_forcingInteriorEdgeWitness_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      (∃ C : diamondWithTriangleGraph.EdgeColoring Color,
        IsTaitEdgeColoring diamondWithTriangleGraph C ∧
          Theorem49BoundaryRootSynthesis emb C) ∧
        Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    ⟨diamondWithTriangleEmbedding,
      ⟨diamondWithTriangleTaitEdgeColoring,
        diamondWithTriangleTaitEdgeColoring_isTait,
        diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring⟩,
      ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

/-- So even the final theorem-4.9 synthesis endpoint under an actual Tait coloring does not
universally force the weaker same-embedding annulus-root adjacency-distance package. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_diamondWithTriangle_via_forcingInteriorEdgeWitness
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph}
        (C : diamondWithTriangleGraph.EdgeColoring Color),
        IsTaitEdgeColoring diamondWithTriangleGraph C →
          Theorem49BoundaryRootSynthesis emb C →
            Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  exact
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_and_forcingInteriorEdgeWitness
      (G := diamondWithTriangleGraph)
      exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_and_forcingInteriorEdgeWitness_diamondWithTriangleGraph

/-- So even the final theorem-4.9 synthesis endpoint under an actual Tait coloring does not
universally force the stronger same-embedding annulus-root parent-peel package. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_diamondWithTriangle_via_forcingInteriorEdgeWitness
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph}
        (C : diamondWithTriangleGraph.EdgeColoring Color),
        IsTaitEdgeColoring diamondWithTriangleGraph C →
          Theorem49BoundaryRootSynthesis emb C →
            Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  exact
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_and_forcingInteriorEdgeWitness
      (G := diamondWithTriangleGraph)
      exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_and_forcingInteriorEdgeWitness_diamondWithTriangleGraph

theorem not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ Nonempty
      (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData diamondWithTriangleEmbedding) := by
  exact
    not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData
      (emb := diamondWithTriangleEmbedding)
      diamondWithTriangleForcingInteriorEdgeWitness

theorem not_nonempty_planarBoundaryAnnulusConstructionFacePartitionData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ Nonempty
      (PlanarBoundaryAnnulusConstructionFacePartitionData diamondWithTriangleEmbedding) := by
  exact
    not_nonempty_planarBoundaryAnnulusConstructionFacePartitionData
      (emb := diamondWithTriangleEmbedding)
      diamondWithTriangleForcingInteriorEdgeWitness

theorem not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ Nonempty
      (PlanarBoundaryAnnulusConstructionPositiveFrontierData diamondWithTriangleEmbedding) := by
  exact
    not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData
      (emb := diamondWithTriangleEmbedding)
      diamondWithTriangleForcingInteriorEdgeWitness

theorem not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ Nonempty
      (PlanarBoundaryAnnulusConstructionFaceLayerData diamondWithTriangleEmbedding) := by
  exact
    not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData
      (emb := diamondWithTriangleEmbedding)
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    closedWalkAnnulusBoundarySource_does_not_imply_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) := by
  exact
    closedWalkAnnulusBoundarySource_does_not_imply_interiorDualBoundaryRootAdjDistancePeelData
      (emb := diamondWithTriangleEmbedding)
      nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    closedWalkAnnulusBoundarySource_does_not_imply_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData
        diamondWithTriangleEmbedding) := by
  exact
    closedWalkAnnulusBoundarySource_does_not_imply_planarBoundaryAnnulusRootAdjDistancePeelData
      (emb := diamondWithTriangleEmbedding)
      nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    closedWalkAnnulusBoundarySource_does_not_imply_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData
        diamondWithTriangleEmbedding) := by
  exact
    closedWalkAnnulusBoundarySource_does_not_imply_planarBoundaryAnnulusRootParentPeelData
      (emb := diamondWithTriangleEmbedding)
      nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    closedWalkAnnulusBoundarySource_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData
        diamondWithTriangleEmbedding) := by
  exact
    closedWalkAnnulusBoundarySource_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusRootAdjDistancePeelData
      (emb := diamondWithTriangleEmbedding)
      nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    closedWalkAnnulusBoundarySource_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData
        diamondWithTriangleEmbedding) := by
  exact
    closedWalkAnnulusBoundarySource_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusRootParentPeelData
      (emb := diamondWithTriangleEmbedding)
      nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    closedWalkAnnulusBoundarySource_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData
        diamondWithTriangleEmbedding) := by
  exact
    closedWalkAnnulusBoundarySource_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusRootAdjDistancePeelData
      (emb := diamondWithTriangleEmbedding)
      nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    closedWalkAnnulusBoundarySource_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData
        diamondWithTriangleEmbedding) := by
  exact
    closedWalkAnnulusBoundarySource_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusRootParentPeelData
      (emb := diamondWithTriangleEmbedding)
      nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph},
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          ¬ Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_exists_embedding_closedWalkAnnulusBoundarySource_and_forcingInteriorEdgeWitness
      (G := diamondWithTriangleGraph)
      ⟨diamondWithTriangleEmbedding,
        nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
        ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

theorem
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph},
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  exact
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_exists_embedding_closedWalkAnnulusBoundarySource_and_forcingInteriorEdgeWitness
      (G := diamondWithTriangleGraph)
      ⟨diamondWithTriangleEmbedding,
        nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
        ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

theorem
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph},
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  exact
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_closedWalkAnnulusBoundarySource_and_forcingInteriorEdgeWitness
      (G := diamondWithTriangleGraph)
      ⟨diamondWithTriangleEmbedding,
        nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
        ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

theorem
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) := by
  exact
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_interiorDualBoundaryRootAdjDistancePeelData
      (emb := diamondWithTriangleEmbedding)
      ⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩
      nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData
        diamondWithTriangleEmbedding) := by
  exact
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusRootAdjDistancePeelData
      (emb := diamondWithTriangleEmbedding)
      ⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩
      nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData
        diamondWithTriangleEmbedding) := by
  exact
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusRootParentPeelData
      (emb := diamondWithTriangleEmbedding)
      ⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩
      nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_nonempty_annulusBoundaryReachabilityData_and_nonempty_cyclicOrderedFaceArcEmbeddingData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph},
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) →
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) →
            ¬ Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness
      (G := diamondWithTriangleGraph)
      ⟨diamondWithTriangleEmbedding,
        ⟨⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩,
          nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_diamondWithTriangle⟩,
        ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

theorem
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_nonempty_annulusBoundaryReachabilityData_and_nonempty_cyclicOrderedFaceArcEmbeddingData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph},
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) →
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) →
            Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  exact
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness
      (G := diamondWithTriangleGraph)
      ⟨diamondWithTriangleEmbedding,
        ⟨⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩,
          nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_diamondWithTriangle⟩,
        ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

theorem
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_nonempty_annulusBoundaryReachabilityData_and_nonempty_cyclicOrderedFaceArcEmbeddingData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph},
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) →
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) →
            Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  exact
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness
      (G := diamondWithTriangleGraph)
      ⟨diamondWithTriangleEmbedding,
        ⟨⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩,
          nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_diamondWithTriangle⟩,
        ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

theorem
    closedWalkAnnulusBoundarySource_does_not_imply_planarBoundaryAnnulusConstructionBoundarySupportFaceData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData
          diamondWithTriangleEmbedding) := by
  exact
    closedWalkAnnulusBoundarySource_does_not_imply_planarBoundaryAnnulusConstructionBoundarySupportFaceData
      (emb := diamondWithTriangleEmbedding)
      nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    closedWalkAnnulusBoundarySource_does_not_imply_planarBoundaryAnnulusConstructionPositiveFrontierData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionPositiveFrontierData
          diamondWithTriangleEmbedding) := by
  exact
    closedWalkAnnulusBoundarySource_does_not_imply_planarBoundaryAnnulusConstructionPositiveFrontierData
      (emb := diamondWithTriangleEmbedding)
      nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    closedWalkAnnulusBoundarySource_does_not_imply_planarBoundaryAnnulusConstructionFaceLayerData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionFaceLayerData
          diamondWithTriangleEmbedding) := by
  exact
    closedWalkAnnulusBoundarySource_does_not_imply_planarBoundaryAnnulusConstructionFaceLayerData
      (emb := diamondWithTriangleEmbedding)
      nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusConstructionBoundarySupportFaceData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData diamondWithTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData
          diamondWithTriangleEmbedding) := by
  exact
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusConstructionBoundarySupportFaceData
      (emb := diamondWithTriangleEmbedding)
      ⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩
      nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusConstructionPositiveFrontierData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData diamondWithTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionPositiveFrontierData
          diamondWithTriangleEmbedding) := by
  exact
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusConstructionPositiveFrontierData
      (emb := diamondWithTriangleEmbedding)
      ⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩
      nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusConstructionFaceLayerData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData diamondWithTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionFaceLayerData
          diamondWithTriangleEmbedding) := by
  exact
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusConstructionFaceLayerData
      (emb := diamondWithTriangleEmbedding)
      ⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩
      nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) := by
  exact
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_interiorDualBoundaryRootAdjDistancePeelData
      (emb := diamondWithTriangleEmbedding)
      ⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩
      nonempty_planarBoundarySelectedBoundaryArcGeometry_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData
        diamondWithTriangleEmbedding) := by
  exact
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusRootAdjDistancePeelData
      (emb := diamondWithTriangleEmbedding)
      ⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩
      nonempty_planarBoundarySelectedBoundaryArcGeometry_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData
        diamondWithTriangleEmbedding) := by
  exact
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusRootParentPeelData
      (emb := diamondWithTriangleEmbedding)
      ⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩
      nonempty_planarBoundarySelectedBoundaryArcGeometry_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_nonempty_annulusBoundaryReachabilityData_and_nonempty_selectedBoundaryArcGeometry_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph},
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) →
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) →
            ¬ Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness
      (G := diamondWithTriangleGraph)
      ⟨diamondWithTriangleEmbedding,
        ⟨⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩,
          nonempty_planarBoundarySelectedBoundaryArcGeometry_diamondWithTriangle⟩,
        ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

theorem
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_nonempty_annulusBoundaryReachabilityData_and_nonempty_selectedBoundaryArcGeometry_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph},
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) →
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) →
            Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  exact
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness
      (G := diamondWithTriangleGraph)
      ⟨diamondWithTriangleEmbedding,
        ⟨⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩,
          nonempty_planarBoundarySelectedBoundaryArcGeometry_diamondWithTriangle⟩,
        ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

theorem
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_nonempty_annulusBoundaryReachabilityData_and_nonempty_selectedBoundaryArcGeometry_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph},
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) →
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) →
            Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  exact
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness
      (G := diamondWithTriangleGraph)
      ⟨diamondWithTriangleEmbedding,
        ⟨⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩,
          nonempty_planarBoundarySelectedBoundaryArcGeometry_diamondWithTriangle⟩,
        ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

theorem
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusConstructionPositiveFrontierData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry diamondWithTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionPositiveFrontierData
          diamondWithTriangleEmbedding) := by
  exact
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusConstructionPositiveFrontierData
      (emb := diamondWithTriangleEmbedding)
      ⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩
      nonempty_planarBoundarySelectedBoundaryArcGeometry_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusConstructionBoundarySupportFaceData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry diamondWithTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData
          diamondWithTriangleEmbedding) := by
  exact
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusConstructionBoundarySupportFaceData
      (emb := diamondWithTriangleEmbedding)
      ⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩
      nonempty_planarBoundarySelectedBoundaryArcGeometry_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

theorem
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusConstructionFaceLayerData_diamondWithTriangle_via_forcingInteriorEdgeWitness :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry diamondWithTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionFaceLayerData
          diamondWithTriangleEmbedding) := by
  exact
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusConstructionFaceLayerData
      (emb := diamondWithTriangleEmbedding)
      ⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩
      nonempty_planarBoundarySelectedBoundaryArcGeometry_diamondWithTriangle
      diamondWithTriangleForcingInteriorEdgeWitness

/-- The explicit same-embedding route surface carried by the diamond-with-triangle graph at the
honest closed-walk source level. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_forcingInteriorEdgeWitness_diamondWithTriangleGraph :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    ⟨diamondWithTriangleEmbedding,
      nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

/-- The same diamond-with-triangle embedding simultaneously carries the honest closed-walk source,
the stronger cyclic face-arc shell derived from it, and the forcing interior-edge witness. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_diamondWithTriangleGraph :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
        Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    ⟨diamondWithTriangleEmbedding,
      nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_of_nonempty_planarBoundaryClosedWalkAnnulusBoundarySource
        nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

/-- The same embedding also carries the weaker bundled selected-boundary-arc shell together with
the honest source and forcing interior-edge witness. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_diamondWithTriangleGraph :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
        Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    ⟨diamondWithTriangleEmbedding,
      nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      nonempty_planarBoundarySelectedBoundaryArcGeometry_of_nonempty_planarBoundaryClosedWalkAnnulusBoundarySource
        nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

/-- The explicit same-embedding route surface carried by the diamond-with-triangle graph at the
cyclic ordered face-arc level. -/
theorem
    exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_diamondWithTriangleGraph :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
        Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    ⟨diamondWithTriangleEmbedding,
      ⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩,
      nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_diamondWithTriangle,
      ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

/-- The explicit same-embedding route surface carried by the diamond-with-triangle graph at the
weaker selected-boundary-arc level. -/
theorem
    exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_diamondWithTriangleGraph :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
        Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    ⟨diamondWithTriangleEmbedding,
      ⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩,
      nonempty_planarBoundarySelectedBoundaryArcGeometry_diamondWithTriangle,
      ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩⟩

/-- No embedding of the same graph can simultaneously carry the honest closed-walk annulus
source, the forcing interior-edge witness, and the peeled interior-dual package. -/
theorem
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_forcingInteriorEdgeWitness_and_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangleGraph :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) := by
  exact
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_forcingInteriorEdgeWitness_and_interiorDualBoundaryRootAdjDistancePeelData
      (G := diamondWithTriangleGraph)

/-- No embedding of the same graph can simultaneously carry annulus reachability, cyclic ordered
face arcs, the forcing interior-edge witness, and the reduced positive-frontier shell. -/
theorem
    not_exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusConstructionPositiveFrontierData_diamondWithTriangleGraph :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusConstructionPositiveFrontierData emb) := by
  exact
    not_exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusConstructionPositiveFrontierData
      (G := diamondWithTriangleGraph)

/-- No embedding of the same graph can simultaneously carry annulus reachability, bundled
selected-boundary arc geometry, the forcing interior-edge witness, and the reduced
positive-frontier shell. -/
theorem
    not_exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangleGraph :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  exact
    not_exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootAdjDistancePeelData
      (G := diamondWithTriangleGraph)

theorem
    not_exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangleGraph :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  exact
    not_exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootParentPeelData
      (G := diamondWithTriangleGraph)

/-- No embedding of the same graph can simultaneously carry annulus reachability, bundled
selected-boundary arc geometry, the forcing interior-edge witness, and the reduced
positive-frontier shell. -/
theorem
    not_exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusConstructionPositiveFrontierData_diamondWithTriangleGraph :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusConstructionPositiveFrontierData emb) := by
  exact
    not_exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusConstructionPositiveFrontierData
      (G := diamondWithTriangleGraph)

theorem
    not_exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangleGraph :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  exact
    not_exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootAdjDistancePeelData
      (G := diamondWithTriangleGraph)

theorem
    not_exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangleGraph :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  exact
    not_exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootParentPeelData
      (G := diamondWithTriangleGraph)

theorem
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusConstructionFaceLayerData_diamondWithTriangleGraph :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  exact
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusConstructionFaceLayerData
      (G := diamondWithTriangleGraph)

theorem
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangleGraph :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  exact
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootAdjDistancePeelData
      (G := diamondWithTriangleGraph)

theorem
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangleGraph :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  exact
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootParentPeelData
      (G := diamondWithTriangleGraph)

theorem
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangleGraph :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  exact
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootAdjDistancePeelData
      (G := diamondWithTriangleGraph)

theorem
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangleGraph :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  exact
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootParentPeelData
      (G := diamondWithTriangleGraph)

theorem
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangleGraph :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  exact
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootParentPeelData
      (G := diamondWithTriangleGraph)

/-- Route implication of the diamond-with-triangle benchmark: the honest source and repaired
previous-boundary witness lanes can already be inhabited while the interior-dual root-distance
packages are impossible on the same embedding.  This records that the interior-dual
adjacency-distance route is a sufficient upstream construction, not a consequence of the
source-plus-previous-boundary geometry present in this benchmark. -/
theorem
    diamondWithTriangle_source_previousBoundaryWitness_and_witnessCover_without_interiorDual_rootDistance :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty
        (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Nonempty (ForcingInteriorEdgeWitness diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData
        diamondWithTriangleEmbedding) := by
  exact
    ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      ⟨diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry⟩,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasWellFoundedFacePeelWitnessData,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasHeightOrderedFacePeelWitnessData,
      ⟨diamondWithTriangleForcingInteriorEdgeWitness⟩,
      not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness,
      not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness⟩

/-- Failed converse form: repaired previous-boundary witness geometry alone cannot be used to
derive the current interior-dual root-distance package. -/
theorem
    not_forall_interiorDualBoundaryRootAdjDistancePeelData_of_previousBoundaryWitnessGeometry_diamondWithTriangle :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph},
        Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) →
          Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) := by
  intro h
  exact not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness
    (h (emb := diamondWithTriangleEmbedding)
      ⟨diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry⟩)

/-- Failed route-facing converse: even honest closed-walk source data plus repaired
previous-boundary witness geometry does not force the two-sided annulus-root
adjacency-distance package. -/
theorem
    not_forall_planarBoundaryAnnulusRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_previousBoundaryWitnessGeometry_diamondWithTriangle :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph},
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) →
            Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  intro h
  exact not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangle_via_forcingInteriorEdgeWitness
    (h (emb := diamondWithTriangleEmbedding)
      nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle
      ⟨diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry⟩)

theorem
    not_exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusConstructionFaceLayerData_diamondWithTriangleGraph :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  exact
    not_exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusConstructionFaceLayerData
      (G := diamondWithTriangleGraph)

theorem
    not_exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusConstructionFaceLayerData_diamondWithTriangleGraph :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  exact
    not_exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusConstructionFaceLayerData
      (G := diamondWithTriangleGraph)

/-- The wheel-with-inner-triangle benchmark has a forcing interior edge at the central spoke
`wit01`: every face incident to that spoke also contains selected boundary support. -/
def wheelWithInnerTriangleForcingInteriorEdgeWitness :
    ForcingInteriorEdgeWitness wheelWithInnerTriangleEmbedding where
  edge := wit01
  heInterior := wit01_mem_interiorEdgeSupport
  hforcing := by
    intro f hf
    rcases f with ⟨face, _hface⟩
    change WheelWithInnerTriangleFace at face
    fin_cases face
    · refine ⟨wit12, ?_, wit12_mem_selectedBoundarySupport⟩
      simp [wheelWithInnerTriangleEmbedding, wheelWithInnerTriangleFaceBoundary]
    · exfalso
      have hmem : wit01 ∈ ({wit02, wit03, wit23} :
          Finset wheelWithInnerTriangleGraph.edgeSet) := by
        simpa [wheelWithInnerTriangleEmbedding, wheelWithInnerTriangleFaceBoundary,
          wheelWithInnerTriangleGraph, wit01, wit02, wit03, wit23] using hf
      exact (by decide : wit01 ∉ ({wit02, wit03, wit23} :
        Finset wheelWithInnerTriangleGraph.edgeSet)) hmem
    · refine ⟨wit31, ?_, wit31_mem_selectedBoundarySupport⟩
      simp [wheelWithInnerTriangleEmbedding, wheelWithInnerTriangleFaceBoundary]
    · exfalso
      have hmem : wit01 ∈ ({wit45, wit56, wit64} :
          Finset wheelWithInnerTriangleGraph.edgeSet) := by
        simpa [wheelWithInnerTriangleEmbedding, wheelWithInnerTriangleFaceBoundary,
          wheelWithInnerTriangleGraph, wit01, wit45, wit56, wit64] using hf
      exact (by decide : wit01 ∉ ({wit45, wit56, wit64} :
        Finset wheelWithInnerTriangleGraph.edgeSet)) hmem

theorem nonempty_forcingInteriorEdgeWitness_wheelWithInnerTriangle :
    Nonempty (ForcingInteriorEdgeWitness wheelWithInnerTriangleEmbedding) :=
  ⟨wheelWithInnerTriangleForcingInteriorEdgeWitness⟩

/-- The wheel benchmark fails the positive local no-forcing condition: the central spoke has no
incident face whose boundary avoids selected-boundary support. -/
theorem not_everyInteriorEdgeHasBoundaryFreeIncidentFace_wheelWithInnerTriangle :
    ¬ EveryInteriorEdgeHasBoundaryFreeIncidentFace wheelWithInnerTriangleEmbedding := by
  intro hfree
  exact
    not_nonempty_forcingInteriorEdgeWitness_of_everyInteriorEdgeHasBoundaryFreeIncidentFace
      hfree nonempty_forcingInteriorEdgeWitness_wheelWithInnerTriangle

/-- Hence the wheel benchmark cannot carry a boundary-free incident-face selector.  This keeps
the selector route honest on the same source-bearing, Tait-colorable obstruction used by the
height-cycle regressions. -/
theorem not_nonempty_boundaryFreeIncidentFaceSelector_wheelWithInnerTriangle :
    ¬ Nonempty (BoundaryFreeIncidentFaceSelector wheelWithInnerTriangleEmbedding) := by
  exact
    (not_nonempty_boundaryFreeIncidentFaceSelector_iff_nonempty_forcingInteriorEdgeWitness).2
      nonempty_forcingInteriorEdgeWitness_wheelWithInnerTriangle

theorem not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness :
    ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData
      wheelWithInnerTriangleEmbedding) := by
  exact
    not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData
      (emb := wheelWithInnerTriangleEmbedding)
      wheelWithInnerTriangleForcingInteriorEdgeWitness

theorem not_nonempty_planarBoundaryAnnulusRootParentPeelData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness :
    ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData
      wheelWithInnerTriangleEmbedding) := by
  exact
    not_nonempty_planarBoundaryAnnulusRootParentPeelData
      (emb := wheelWithInnerTriangleEmbedding)
      wheelWithInnerTriangleForcingInteriorEdgeWitness

theorem not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness :
    ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
      wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faceBoundary) := by
  exact
    not_nonempty_interiorDualBoundaryRootAdjDistancePeelData
      (emb := wheelWithInnerTriangleEmbedding)
      wheelWithInnerTriangleForcingInteriorEdgeWitness

/-- Every face in the wheel-with-inner-triangle benchmark is represented by a three-edge
boundary. -/
theorem wheelWithInnerTriangleFaceBoundary_card_eq_three
    (f : WheelWithInnerTriangleFace) :
    (wheelWithInnerTriangleEmbedding.faceBoundary f).card = 3 := by
  fin_cases f <;> decide

theorem wheelWithInnerTriangle_faceBoundary_card_eq_three
    (f : AmbientFace wheelWithInnerTriangleEmbedding.faces) :
    (wheelWithInnerTriangleEmbedding.faceBoundary f.1).card = 3 := by
  exact wheelWithInnerTriangleFaceBoundary_card_eq_three f.1

theorem wheelWithInnerTriangle_two_le_faceBoundary_card
    (f : AmbientFace wheelWithInnerTriangleEmbedding.faces) :
    2 ≤ (wheelWithInnerTriangleEmbedding.faceBoundary f.1).card := by
  rw [wheelWithInnerTriangle_faceBoundary_card_eq_three f]
  decide

theorem not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_wheelWithInnerTriangle_via_terminal_card_lower_bound :
    ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
      wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faceBoundary) := by
  exact
    not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_of_mem_interiorEdgeSupport_of_forall_face_two_le_faceBoundary_card
      (emb := wheelWithInnerTriangleEmbedding)
      wit01_mem_interiorEdgeSupport
      wheelWithInnerTriangle_two_le_faceBoundary_card

theorem hasUnblockedInteriorEndpoint_wheelWithInnerTriangle :
    HasUnblockedInteriorEndpoint wheelWithInnerTriangleEmbedding := by
  exact
    (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
      wheelWithInnerTriangleEmbedding).2
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle

end Theorem49ForcingInteriorEdgeObstructionRegression

end Mettapedia.GraphTheory.FourColor
