import Mettapedia.GraphTheory.FourColor.EdgeShoreRotation
import Mettapedia.GraphTheory.FourColor.SphericalContourSeparators

/-!
# The actual local degrees after selecting a facial region

Retain every edge incident with a selected quotient face. At a cubic vertex,
zero selected face sectors retain no edge, one retains two, and two or three
retain all three. This computes the boundary degree code from the ambient
rotation rather than supplying it as a patch hypothesis. In particular every
complete distance-contour vertex gives a degree-two or degree-three vertex of
the literal retained-edge map. Different contour vertices may give different
degrees; alternation is not asserted.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceRegionDegree

open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness
open PhysicalForkCodeFaces PhysicalForkCodeCut
open EdgeShoreFaceForkFold SphericalDistanceContours FaceDistanceFrontiers

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (RS : RotationSystem V E) (R : Finset (OrbitFace RS))

/-- Include boundary edges as well as edges between selected faces. -/
def edges : Finset E := R.biUnion (orbitFaceBoundary RS)

/-- Count face sectors, preserving multiplicities if a vertex meets the
same quotient face more than once. -/
def sectors (v : V) : Finset RS.D :=
  (RS.dartsAt v).filter fun d => dartOrbitFace RS d ∈ R

theorem edge_mem_iff (d : RS.D) :
    RS.edgeOf d ∈ edges RS R ↔
      dartOrbitFace RS d ∈ R ∨ dartOrbitFace RS (RS.alpha d) ∈ R := by
  constructor
  · intro h
    obtain ⟨f, hf, he⟩ := Finset.mem_biUnion.mp h
    obtain ⟨e, he, hed⟩ := (mem_orbitFaceBoundary_iff RS f _).mp he
    have hef := (mem_orbitFaceDarts_iff RS f e).mp he
    rcases RS.edge_fiber_two_cases rfl hed with rfl | rfl
    · exact Or.inl (hef.symm ▸ hf)
    · exact Or.inr (hef.symm ▸ hf)
  · rintro (h | h)
    · exact Finset.mem_biUnion.mpr ⟨_, h, edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS d⟩
    · apply Finset.mem_biUnion.mpr
      refine ⟨_, h, ?_⟩
      rw [← RS.edge_alpha d]
      exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS (RS.alpha d)

theorem edge_mem_iff_sectors (d : RS.D) :
    RS.edgeOf d ∈ edges RS R ↔
      dartOrbitFace RS d ∈ R ∨ dartOrbitFace RS (RS.rho d) ∈ R := by
  rw [edge_mem_iff, dartOrbitFace_alpha_eq_dartOrbitFace_rho]

theorem touched_iff (v : V) :
    v ∈ touched RS (edges RS R) ↔ ∃ d, RS.vertOf d = v ∧ dartOrbitFace RS d ∈ R := by
  rw [mem_touched]
  constructor
  · rintro ⟨d, hd, he⟩
    rcases (edge_mem_iff_sectors RS R d).mp he with hf | hf
    · exact ⟨d, hd, hf⟩
    · exact ⟨RS.rho d, (RS.vert_rho d).trans hd, hf⟩
  · rintro ⟨d, hd, hf⟩
    exact ⟨d, hd, (edge_mem_iff RS R d).mpr (Or.inl hf)⟩

theorem touched_iff_sectors_nonempty (v : V) :
    v ∈ touched RS (edges RS R) ↔ (sectors RS R v).Nonempty := by
  rw [touched_iff]
  simp [sectors, RotationSystem.dartsAt, Finset.Nonempty]

variable {RS R}

theorem dartsAt_three (hC : Cubic3 RS) (d : RS.D) :
    RS.dartsAt (RS.vertOf d) = {d, RS.rho d, RS.rho (RS.rho d)} := by
  ext e
  simp only [RotationSystem.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · exact hC.fiber d e
  · rintro (rfl | rfl | rfl) <;> simp [RS.vert_rho]

private theorem triple_ne (hC : Cubic3 RS) (d : RS.D) :
    d ≠ RS.rho d ∧ d ≠ RS.rho (RS.rho d) ∧ RS.rho d ≠ RS.rho (RS.rho d) := by
  refine ⟨(hC.moves d).symm, ?_, (hC.moves (RS.rho d)).symm⟩
  intro he
  have hh := congrArg RS.rho he
  rw [hC.cube] at hh
  exact hC.moves d hh

/-- Exact local incidence formula, before imposing planarity or any
connectivity condition on the selected facial region. -/
theorem retained_degree_formula (hC : Cubic3 RS) (d : RS.D) :
    ((RS.dartsAt (RS.vertOf d)).filter fun e => RS.edgeOf e ∈ edges RS R).card =
      if (sectors RS R (RS.vertOf d)).card = 0 then 0
      else if (sectors RS R (RS.vertOf d)).card = 1 then 2 else 3 := by
  obtain ⟨h01, h02, h12⟩ := triple_ne hC d
  by_cases h0 : dartOrbitFace RS d ∈ R <;>
    by_cases h1 : dartOrbitFace RS (RS.rho d) ∈ R <;>
    by_cases h2 : dartOrbitFace RS (RS.rho (RS.rho d)) ∈ R <;>
    simp [sectors, dartsAt_three hC d, Finset.filter_insert, Finset.filter_singleton,
      edge_mem_iff_sectors, hC.cube, h0, h1, h2, h01, h02, h12]

/-- Every touched vertex of a face-generated edge shore retains at least
two incident darts. Thus its literal map has no dangling vertices. -/
theorem degree_two_or_three (hC : Cubic3 RS)
    (outer : EdgeShoreRotation.Dart RS (edges RS R))
    (v : EdgeShoreRotation.Vertex RS (edges RS R)) :
    ((EdgeShoreRotation.toMap RS (edges RS R) outer).dartsAt v).card = 2 ∨
      ((EdgeShoreRotation.toMap RS (edges RS R) outer).dartsAt v).card = 3 := by
  obtain ⟨d, hd, _⟩ := (touched_iff RS R v.val).mp v.property
  have hn := (touched_iff_sectors_nonempty RS R v.val).mp v.property
  have hp := Finset.card_pos.mpr hn
  rw [EdgeShoreRotation.degree_eq, ← hd, retained_degree_formula hC d]
  rw [hd]
  split_ifs <;> omega

/-- The degree-two boundary state is exactly one selected ambient face
sector, rather than a freely chosen colour or orientation bit. -/
theorem degree_two_iff_one_sector (hC : Cubic3 RS)
    (outer : EdgeShoreRotation.Dart RS (edges RS R))
    (v : EdgeShoreRotation.Vertex RS (edges RS R)) :
    ((EdgeShoreRotation.toMap RS (edges RS R) outer).dartsAt v).card = 2 ↔
      (sectors RS R v.val).card = 1 := by
  obtain ⟨d, hd, _⟩ := (touched_iff RS R v.val).mp v.property
  rw [EdgeShoreRotation.degree_eq, ← hd, retained_degree_formula hC d]
  rw [hd]
  split_ifs <;> simp_all

section Contours

open _root_.SimpleGraph SimpleGraphDartRotation
open GoertzelV24PrimalCycleFacialBond SphericalContourSeparators

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A mixed vertex of an actual face region is present in the retained
map; no abstract mesh boundary is substituted for the ambient interface. -/
theorem mixed_touched (data : Data G) (R : Finset (OrbitFace data.toRotationSystem))
    {v : V} (hv : Mixed (vertexFaces data) (R : Set _) v) :
    v ∈ touched data.toRotationSystem (edges data.toRotationSystem R) := by
  obtain ⟨f, ⟨d, hd, hdf⟩, hf⟩ := hv.1
  exact (touched_iff _ _ _).mpr ⟨d, hd, hdf ▸ hf⟩

/-- Direct specialization to the complete distance contours already
constructed by the large-map alternative. -/
theorem frontier_touched (data : Data G)
    (root far : OrbitFace data.toRotationSystem) (depth : ℕ) {v : V}
    (hv : v ∈ frontier data root far depth) :
    v ∈ touched data.toRotationSystem
      (edges data.toRotationSystem
        (Finset.univ.filter fun f => f ∈ deepRegion (orbitFaceDualGraph data) root far depth)) := by
  apply mixed_touched data
  simpa only [SphericalContourSeparators.frontier, Set.mem_ofPred_eq, Mixed,
    Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] using hv

end Contours
end
end Mettapedia.GraphTheory.FourColor.FaceRegionDegree
