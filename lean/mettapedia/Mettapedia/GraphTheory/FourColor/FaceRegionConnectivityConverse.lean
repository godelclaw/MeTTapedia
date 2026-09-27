import Mettapedia.GraphTheory.FourColor.FaceRegionConnectivity

/-!
# Recovering facial connectivity from retained edges

In a cubic map, the face sectors at each vertex form a clique in the facial
dual. Consequently a walk through retained edges lifts to a walk through
selected faces. For a nonempty collection of faces, connectivity of its
retained edge shore is equivalent to connectivity in the actual facial dual.
No spherical embedding or connectedness of the complementary faces is needed.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceRegionConnectivityConverse

open SimpleGraphDartRotation GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceDualConnectedness GoertzelV24OrbitFaceTwoSided
open GoertzelV24PrimalCycleFacialBond SphericalDistanceContours
open FaceRegionDegree PhysicalForkCodeEuler PhysicalForkCodeCut

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G) (F : Finset (OrbitFace data.toRotationSystem))
variable (hcubic : data.toRotationSystem.IsCubic)
variable (hrotation : VertexRotationCyclic data.toRotationSystem)
variable (htwo : OrbitFacesTwoSided data.toRotationSystem)

include hcubic hrotation htwo

private theorem local_reachable {v : V} (f g : {f // f ∈ F})
    (hf : f.val ∈ vertexFaces data v) (hg : g.val ∈ vertexFaces data v) :
    ((orbitFaceDualGraph data).induce (F : Set _)).Reachable f g := by
  rcases vertexFaces_clique data hcubic hrotation htwo v f.val g.val hf hg with h | h
  · exact Subtype.ext h ▸ SimpleGraph.Reachable.refl f
  · exact SimpleGraph.Adj.reachable h

omit hcubic hrotation htwo in
private theorem edge_face {v w : V}
    (h : (shoreGraph data.toRotationSystem (edges data.toRotationSystem F)).Adj v w) :
    ∃ f : {f // f ∈ F}, f.val ∈ vertexFaces data v ∧ f.val ∈ vertexFaces data w := by
  obtain ⟨d, hd, hv, hw⟩ := h
  have at_other (a : data.toRotationSystem.D) :
      dartOrbitFace data.toRotationSystem a ∈
        vertexFaces data (data.toRotationSystem.vertOf (data.toRotationSystem.alpha a)) :=
    ⟨data.toRotationSystem.phi a, data.toRotationSystem.vert_phi_eq_vert_alpha a,
      dartOrbitFace_phi_eq data.toRotationSystem a⟩
  rcases (edge_mem_iff data.toRotationSystem F d).mp hd with hf | hf
  · exact ⟨⟨_, hf⟩, ⟨d, hv, rfl⟩, hw ▸ at_other d⟩
  · refine ⟨⟨_, hf⟩, ?_, ⟨data.toRotationSystem.alpha d, hw, rfl⟩⟩
    have hh := at_other (data.toRotationSystem.alpha d)
    simpa only [data.toRotationSystem.alpha_involutive, hv] using hh

/-- A retained primal walk transports any selected face at its first vertex
to any selected face at its last vertex. -/
theorem walk_faces {v w : V}
    (p : (shoreGraph data.toRotationSystem (edges data.toRotationSystem F)).Walk v w)
    (f g : {f // f ∈ F})
    (hf : f.val ∈ vertexFaces data v) (hg : g.val ∈ vertexFaces data w) :
    ((orbitFaceDualGraph data).induce (F : Set _)).Reachable f g := by
  induction p generalizing f with
  | nil => exact local_reachable data F hcubic hrotation htwo f g hf hg
  | cons h p ih =>
    obtain ⟨a, ha, ha'⟩ := edge_face data F h
    exact (local_reachable data F hcubic hrotation htwo f a hf ha).trans
      (ih a ha' hg)

/-- Connectivity of the literal retained edge shore supplies connectivity
of the selected original faces. -/
theorem connected_of_shoreConnected (hne : F.Nonempty)
    (hshore : ShoreConnected data.toRotationSystem (edges data.toRotationSystem F)) :
    ((orbitFaceDualGraph data).induce (F : Set _)).Connected := by
  obtain ⟨root, hroot⟩ := hne
  let : Nonempty {f // f ∈ F} := ⟨⟨root, hroot⟩⟩
  constructor
  intro f g
  obtain ⟨d, hd⟩ := exists_dartOrbitFace_eq data.toRotationSystem f.val
  obtain ⟨a, ha⟩ := exists_dartOrbitFace_eq data.toRotationSystem g.val
  have hdt : data.toRotationSystem.vertOf d ∈
      touched data.toRotationSystem (edges data.toRotationSystem F) :=
    (touched_iff _ _ _).mpr ⟨d, rfl, hd ▸ f.property⟩
  have hat : data.toRotationSystem.vertOf a ∈
      touched data.toRotationSystem (edges data.toRotationSystem F) :=
    (touched_iff _ _ _).mpr ⟨a, rfl, ha ▸ g.property⟩
  obtain ⟨p⟩ := hshore _ _ hdt hat
  exact walk_faces data F hcubic hrotation htwo p f g ⟨d, rfl, hd⟩ ⟨a, rfl, ha⟩

/-- The primal and dual presentations agree on connectivity of a nonempty
facial region in a cubic two-sided map. -/
theorem connected_iff_shoreConnected (hne : F.Nonempty) :
    ((orbitFaceDualGraph data).induce (F : Set _)).Connected ↔
      ShoreConnected data.toRotationSystem (edges data.toRotationSystem F) :=
  ⟨FaceRegionConnectivity.shore_connected data F,
    connected_of_shoreConnected data F hcubic hrotation htwo hne⟩

end
end Mettapedia.GraphTheory.FourColor.FaceRegionConnectivityConverse
