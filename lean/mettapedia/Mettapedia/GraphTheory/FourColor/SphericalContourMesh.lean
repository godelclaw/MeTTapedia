import Mettapedia.GraphTheory.FourColor.ContourPathCrossing
import Mettapedia.GraphTheory.FourColor.RotationWalkMeshPath

/-!
# An injective mesh or a complete bounded bond from actual spherical contours

Construct all consecutive depth contours, obtain an ambient linkage or
separator, and prove that every linkage column meets every contour row.
The row and column carriers are converted to the existing rotation
multigraph without changing vertices. This gives the exact injective
`Mesh` used in the wall-free decomposition premise, not a surrogate wall.

With that mesh excluded, the small connected ordered bond is forced.
This local conclusion does not yet assemble mutually compatible cuts or
the complete recursive branch decomposition.
-/

namespace Mettapedia.GraphTheory.FourColor.SphericalContourSeparators

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24FaceOrbitIncidence GoertzelV24PrimalCycleFacialBond
open GoertzelV24OrbitFaceTwoSided GoertzelV24TwoEdgeCutMinimality
open GoertzelV24DeletedRegionRotationSplice GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24RetainedRegionBoundaryOrder GoertzelV24ComplementaryRegionBoundaryOrder
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationMultigraphAdapter GoertzelV24MeshIsoperimetry
open GoertzelV24InjectiveMeshWidthExclusion
open SphericalDistanceContours FaceDistanceFrontiers VertexSeparatorBond VertexSplitCut
open RotationWalkMeshPath ContourMeshExtraction

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The supplied linkage's intersections with ALL rows are derived; the
next theorem supplies the linkage or constructs the alternative cut. -/
theorem exists_injectiveMesh_of_contour_linkage (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (root far : OrbitFace data.toRotationSystem) (lo a b : ℕ)
    (hd : lo + a ≤ (orbitFaceDualGraph data).dist root far)
    (L : Linkage G (frontier data root far lo) (frontier data root far (lo + a - 1)) b) :
    ∃ M : Mesh (toMultigraph data.toRotationSystem) a b, IsVertexInjective M := by
  classical
  have hcycles (t : Fin a) : ∃ s : V, ∃ c : G.Walk s s,
      ∀ v, v ∈ c.support ↔ v ∈ frontier data root far (lo + t.val) := by
    obtain ⟨s, c, _hc, _he, hv⟩ :=
      exists_distance_contour data hclass htwo root far (lo + t.val) (by omega)
    exact ⟨s, c, hv⟩
  choose start cycles hcycles using hcycles
  let rows := fun t => ofWalk data (cycles t)
  let cols := fun t => ofWalk data (L.walk t)
  apply exists_injectiveMesh_of_distanceFrontiers (orbitFaceDualGraph data) root far
    (vertexFaces data)
    (vertexFaces_clique data hclass.spherical.cubic hclass.vertexRotationCyclic htwo)
    (fun t : Fin a => lo + t.val) (by
      intro i j h
      apply Fin.ext
      change lo + i.val = lo + j.val at h
      omega) rows cols
  · intro i s
    exact (hcycles i _).mp (vert_mem_support data (cycles i) s)
  · intro i j hij s t heq
    exact L.disjoint i j hij ((cols i).vert s)
      (vert_mem_support data (L.walk i) s)
      (heq ▸ vert_mem_support data (L.walk j) t)
  · intro i j
    obtain ⟨v, hp, hv⟩ := walk_meets_intermediate data hclass htwo root far
      (i := lo) (d := lo + i.val) (j := lo + a - 1)
      (by omega) (by omega) (L.start_mem j) (L.finish_mem j) (L.walk j)
    obtain ⟨s, hs⟩ := (exists_vert_iff data (cycles i)).mpr ((hcycles i v).mpr hv)
    obtain ⟨t, ht⟩ := (exists_vert_iff data (L.walk j)).mpr hp
    exact ⟨s, t, hs.trans ht.symm⟩

/-- Neither rows, columns, intersections nor a separator are supplied. -/
theorem exists_injectiveMesh_or_ordered_bond (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (root far : OrbitFace data.toRotationSystem) (lo a b : ℕ)
    (ha : 2 ≤ a) (hd : lo + a ≤ (orbitFaceDualGraph data).dist root far) :
    (∃ M : Mesh (toMultigraph data.toRotationSystem) a b, IsVertexInjective M) ∨
    ∃ deleted : Finset V,
      frontier data root far lo ⊆ {v | deletedRegionKeep deleted v} ∧
      frontier data root far (lo + a - 1) ⊆ {v | ¬ deletedRegionKeep deleted v} ∧
      (G.induce {v | deletedRegionKeep deleted v}).Connected ∧
      (G.induce {v | ¬ deletedRegionKeep deleted v}).Connected ∧
      (edgeBoundary G {v | deletedRegionKeep deleted v}).card ≤ 3 * (b - 1) ∧
      Fintype.card (BoundaryDart data.toRotationSystem (deletedRegionKeep deleted)) ≤ 3 * (b - 1) ∧
      CutFacesHaveUniqueRetainedBoundaryDart data.toRotationSystem deleted ∧
      retainedRegionBoundarySuccessor data.toRotationSystem (deletedRegionKeep deleted) =
        (deletedRegionBoundarySuccessor data.toRotationSystem deleted)⁻¹ := by
  rcases exists_linkage_or_ordered_bond data hclass htwo root far
    (i := lo) (j := lo + a - 1) (by omega) (by omega) (by omega) b with hL | hcut
  · obtain ⟨L⟩ := hL
    exact Or.inl (exists_injectiveMesh_of_contour_linkage data hclass htwo root far lo a b hd L)
  · exact Or.inr hcut

/-- The exact no-injective-mesh premise forces the constructed bounded cut. -/
theorem exists_ordered_bond_of_no_injectiveMesh (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (root far : OrbitFace data.toRotationSystem) (lo a b : ℕ)
    (ha : 2 ≤ a) (hd : lo + a ≤ (orbitFaceDualGraph data).dist root far)
    (hno : ¬ ∃ M : Mesh (toMultigraph data.toRotationSystem) a b, IsVertexInjective M) :
    ∃ deleted : Finset V,
      frontier data root far lo ⊆ {v | deletedRegionKeep deleted v} ∧
      frontier data root far (lo + a - 1) ⊆ {v | ¬ deletedRegionKeep deleted v} ∧
      (G.induce {v | deletedRegionKeep deleted v}).Connected ∧
      (G.induce {v | ¬ deletedRegionKeep deleted v}).Connected ∧
      (edgeBoundary G {v | deletedRegionKeep deleted v}).card ≤ 3 * (b - 1) ∧
      Fintype.card (BoundaryDart data.toRotationSystem (deletedRegionKeep deleted)) ≤ 3 * (b - 1) ∧
      CutFacesHaveUniqueRetainedBoundaryDart data.toRotationSystem deleted ∧
      retainedRegionBoundarySuccessor data.toRotationSystem (deletedRegionKeep deleted) =
        (deletedRegionBoundarySuccessor data.toRotationSystem deleted)⁻¹ :=
  (exists_injectiveMesh_or_ordered_bond data hclass htwo root far lo a b ha hd).resolve_left hno

end Mettapedia.GraphTheory.FourColor.SphericalContourSeparators
