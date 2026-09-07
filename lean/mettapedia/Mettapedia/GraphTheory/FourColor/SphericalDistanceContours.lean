import Mettapedia.GraphTheory.FourColor.FacialBondPrimalCycle
import Mettapedia.GraphTheory.FourColor.FaceDistanceFrontiers
import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicFaceCutTrailTransport

/-!
# Actual distance contours in a spherical cubic rotation system

The three face sectors at a cubic vertex form a clique in the facial dual.
An actual boundary dart exists at every mixed vertex, and conversely. Thus
the primal cycle extracted from a connected facial bipartition contains
exactly its mixed vertices, not merely a selected subset of the frontier.
Applying this to the constructed deep face components gives complete,
vertex-disjoint contours at different distances, with no contour supplier.

There is no bound on contour length here, nor a constructed inter-contour
linkage or branch decomposition.
-/

namespace Mettapedia.GraphTheory.FourColor.SphericalDistanceContours

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness
open GoertzelV24OrbitFaceTwoSided GoertzelV24PrimalCycleFacialBond
open GoertzelV24FaceBoundaryLinearAlgebra GoertzelV24KauffmanFacePotential
open GoertzelV24FaceSeparation GoertzelV24TwoEdgeCutMinimality
open FacialBondPrimalCycle FaceDistanceFrontiers

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- Incident faces are literal outgoing-dart sectors of the ambient rotation. -/
def vertexFaces (data : Data G) (v : V) : Set (OrbitFace data.toRotationSystem) :=
  {f | ∃ d : data.toRotationSystem.D,
    data.toRotationSystem.vertOf d = v ∧ dartOrbitFace data.toRotationSystem d = f}

theorem opposite_faces_adj (data : Data G)
    (htwo : OrbitFacesTwoSided data.toRotationSystem) (d : data.toRotationSystem.D) :
    (orbitFaceDualGraph data).Adj (dartOrbitFace data.toRotationSystem d)
      (dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha d)) := by
  have hright : data.toRotationSystem.edgeOf d ∈
      orbitFaceBoundary data.toRotationSystem
        (dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha d)) := by
    rw [← data.toRotationSystem.edge_alpha d]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace data.toRotationSystem
      (data.toRotationSystem.alpha d)
  exact interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
    (orbitFaceBoundary data.toRotationSystem)
    (Finset.univ : Finset (OrbitFace data.toRotationSystem))
    (orbitFace_incidence_le_two data.toRotationSystem) (htwo d)
    (edgeOf_mem_orbitFaceBoundary_dartOrbitFace data.toRotationSystem d) hright

/-- Cubicity discharges the local clique hypothesis of the distance lemma. -/
theorem vertexFaces_clique (data : Data G)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrot : VertexRotationCyclic data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem) :
    ∀ v f g, f ∈ vertexFaces data v → g ∈ vertexFaces data v →
      f = g ∨ (orbitFaceDualGraph data).Adj f g := by
  intro v f g ⟨d, hd, hdf⟩ ⟨e, he, heg⟩
  subst f
  subst g
  by_cases hde : d = e
  · exact Or.inl (congrArg (dartOrbitFace data.toRotationSystem) hde)
  right
  rcases data.toRotationSystem.rho_eq_or_rho_eq_of_cubic hcubic hrot
    (he.trans hd.symm) hde with hforward | hreverse
  · have hh := dartOrbitFace_alpha_eq_dartOrbitFace_rho data.toRotationSystem d
    rw [hforward] at hh
    rw [← hh]
    exact opposite_faces_adj data htwo d
  · have hh := dartOrbitFace_alpha_eq_dartOrbitFace_rho data.toRotationSystem e
    rw [hreverse] at hh
    rw [← hh]
    exact (opposite_faces_adj data htwo e).symm

/-- An edge is on the full boundary precisely when its two incident faces
belong to opposite sides. -/
theorem boundary_ne_zero_iff_separates (data : Data G)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (S : Finset (OrbitFace data.toRotationSystem)) (d : data.toRotationSystem.D) :
    orbitFaceBoundaryLinearMap data.toRotationSystem (faceSetIndicator data S)
      (data.toRotationSystem.edgeOf d) ≠ 0 ↔
      ((dartOrbitFace data.toRotationSystem d ∈ S ∧
        dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha d) ∉ S) ∨
       (dartOrbitFace data.toRotationSystem d ∉ S ∧
        dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha d) ∈ S)) := by
  rw [mem_image_iff_separates _ htwo]
  by_cases hl : dartOrbitFace data.toRotationSystem d ∈ S <;>
    by_cases hr : dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha d) ∈ S <;>
    simp only [faceSetIndicator, hl, hr, ↓reduceIte, not_true_eq_false, not_false_eq_true,
      and_true, and_false, or_true, or_false, ne_eq, one_ne_zero, zero_ne_one]

/-- Every mixed vertex has a boundary dart based at that vertex. The reverse
direction uses the rotated dart to represent the opposite edge face locally. -/
theorem mixed_iff_boundary_dart (data : Data G)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrot : VertexRotationCyclic data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (S : Finset (OrbitFace data.toRotationSystem)) (v : V) :
    Mixed (vertexFaces data) (S : Set (OrbitFace data.toRotationSystem)) v ↔
      ∃ d : data.toRotationSystem.D, data.toRotationSystem.vertOf d = v ∧
        orbitFaceBoundaryLinearMap data.toRotationSystem (faceSetIndicator data S)
          (data.toRotationSystem.edgeOf d) ≠ 0 := by
  constructor
  · rintro ⟨⟨f, ⟨d, hd, hdf⟩, hf⟩, ⟨g, ⟨e, he, heg⟩, hg⟩⟩
    subst f
    subst g
    have hde : d ≠ e := by
      rintro rfl
      exact hg hf
    rcases data.toRotationSystem.rho_eq_or_rho_eq_of_cubic hcubic hrot
      (he.trans hd.symm) hde with hforward | hreverse
    · refine ⟨d, hd, (boundary_ne_zero_iff_separates data htwo S d).mpr (Or.inl ⟨hf, ?_⟩)⟩
      rwa [dartOrbitFace_alpha_eq_dartOrbitFace_rho, hforward]
    · refine ⟨e, he, (boundary_ne_zero_iff_separates data htwo S e).mpr (Or.inr ⟨hg, ?_⟩)⟩
      rwa [dartOrbitFace_alpha_eq_dartOrbitFace_rho, hreverse]
  · rintro ⟨d, hd, hboundary⟩
    have hfirst : dartOrbitFace data.toRotationSystem d ∈ vertexFaces data v :=
      ⟨d, hd, rfl⟩
    have hsecond : dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha d) ∈
        vertexFaces data v :=
      ⟨data.toRotationSystem.rho d, (data.toRotationSystem.vert_rho d).trans hd,
        (dartOrbitFace_alpha_eq_dartOrbitFace_rho data.toRotationSystem d).symm⟩
    rcases (boundary_ne_zero_iff_separates data htwo S d).mp hboundary with h | h
    · exact ⟨⟨_, hfirst, h.1⟩, ⟨_, hsecond, h.2⟩⟩
    · exact ⟨⟨_, hsecond, h.2⟩, ⟨_, hfirst, h.1⟩⟩

/-- Exact edge coverage also gives exact vertex-frontier coverage. -/
theorem cycle_support_iff_mixed (data : Data G)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrot : VertexRotationCyclic data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (S : Finset (OrbitFace data.toRotationSystem))
    {root : V} (cycle : G.Walk root root) (hcycle : cycle.IsCycle)
    (hexact : ∀ e : G.edgeSet, e.val ∈ cycle.edges ↔
      orbitFaceBoundaryLinearMap data.toRotationSystem (faceSetIndicator data S) e ≠ 0)
    (v : V) : v ∈ cycle.support ↔ Mixed (vertexFaces data) (S : Set _) v := by
  rw [mixed_iff_boundary_dart data hcubic hrot htwo]
  constructor
  · intro hv
    obtain ⟨edge, hedge, hvertex⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hcycle.not_nil |>.mp hv
    obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp hvertex
    have hadj : G.Adj v w := by
      apply (SimpleGraph.mem_edgeSet G).mp
      rw [← hw]
      exact cycle.edges_subset_edgeSet hedge
    let d : G.Dart := ⟨(v, w), hadj⟩
    refine ⟨d, rfl, (hexact (data.toRotationSystem.edgeOf d)).mp ?_⟩
    change s(v, w) ∈ cycle.edges
    rwa [hw] at hedge
  · rintro ⟨d, hd, hboundary⟩
    have he := (hexact (data.toRotationSystem.edgeOf d)).mpr hboundary
    change d.fst = v at hd
    rw [← hd]
    exact cycle.fst_mem_support_of_mem_edges he

/-- The actual deep component has one complete simple primal contour, with
both its edge boundary and all mixed vertices identified. -/
theorem exists_distance_contour (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (root far : OrbitFace data.toRotationSystem) (depth : ℕ)
    (hdepth : depth < (orbitFaceDualGraph data).dist root far) :
    ∃ (start : V) (cycle : G.Walk start start), cycle.IsCycle ∧
      (∀ d : data.toRotationSystem.D,
        (data.toRotationSystem.edgeOf d).val ∈ cycle.edges ↔
          ((dartOrbitFace data.toRotationSystem d ∈ deepRegion (orbitFaceDualGraph data) root far depth ∧
            dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha d) ∉
              deepRegion (orbitFaceDualGraph data) root far depth) ∨
           (dartOrbitFace data.toRotationSystem d ∉ deepRegion (orbitFaceDualGraph data) root far depth ∧
            dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha d) ∈
              deepRegion (orbitFaceDualGraph data) root far depth))) ∧
      ∀ v, v ∈ cycle.support ↔ Mixed (vertexFaces data)
        (deepRegion (orbitFaceDualGraph data) root far depth) v := by
  classical
  let region := deepRegion (orbitFaceDualGraph data) root far depth
  let S := region.toFinset
  have hcoe : (S : Set (OrbitFace data.toRotationSystem)) = region := Set.coe_toFinset _
  have hS : ((orbitFaceDualGraph data).induce {f | f ∈ S}).Connected := by
    change ((orbitFaceDualGraph data).induce (S : Set _)).Connected
    rw [hcoe]
    exact deepRegion_connected _ root far depth hdepth
  have hSc : ((orbitFaceDualGraph data).induce {f | f ∉ S}).Connected := by
    change ((orbitFaceDualGraph data).induce (S : Set _)ᶜ).Connected
    rw [hcoe]
    exact deepRegion_compl_connected _ root far (orbitFaceDualGraph_connected data hclass) depth
  obtain ⟨start, cycle, hcycle, hexact⟩ := exists_cycle_of_facial_bond data hclass htwo S hS hSc
  refine ⟨start, cycle, hcycle, ?_, ?_⟩
  · intro d
    rw [hexact, boundary_ne_zero_iff_separates data htwo]
    simp only [S, Set.mem_toFinset, region]
  · intro v
    rw [cycle_support_iff_mixed data hclass.spherical.cubic hclass.vertexRotationCyclic
      htwo S cycle hcycle hexact, hcoe]

/-- Distinct actual distance frontiers share no vertex. The cubic incidence
condition is proved here rather than imposed on the family of contours. -/
theorem distance_frontiers_disjoint (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (root far : OrbitFace data.toRotationSystem) {i j : ℕ} (hij : i ≠ j) :
    Disjoint {v | Mixed (vertexFaces data) (deepRegion (orbitFaceDualGraph data) root far i) v}
      {v | Mixed (vertexFaces data) (deepRegion (orbitFaceDualGraph data) root far j) v} :=
  mixed_disjoint _ root far (vertexFaces data)
    (vertexFaces_clique data hclass.spherical.cubic hclass.vertexRotationCyclic htwo) hij

end
end Mettapedia.GraphTheory.FourColor.SphericalDistanceContours
