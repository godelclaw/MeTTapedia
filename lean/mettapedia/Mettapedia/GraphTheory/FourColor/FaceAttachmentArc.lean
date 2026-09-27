import Mettapedia.GraphTheory.FourColor.FaceAttachmentCount
import Mettapedia.GraphTheory.FourColor.PermutationSingleExitArc

/-!
# The ordered attachment arc of a facial construction step

The common edges of the old patch and added face form one proper arc of the
original face permutation. The arc is derived from the Euler attachment
count, not supplied as a geometric field of the construction event.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceAttachmentArc

open Equiv Equiv.Perm
open GoertzelV24FaceOrbitIncidence GoertzelV24TwoEdgeCutMinimality
open GoertzelV24OrbitFaceTwoSided GoertzelV24FaceDualConnectedness
open SimpleGraphDartRotation FaceRegionDegree EdgeShoreRotation
open PlanePatchCurvature FaceRegionShelling FaceAttachmentCount
open PhysicalForkCodeCut FaceRegionPatch PermutationSingleExitArc

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G)
variable (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)

theorem face_vertex_image (f : OrbitFace data.toRotationSystem) :
    touched data.toRotationSystem (orbitFaceBoundary data.toRotationSystem f) =
      (orbitFaceDarts data.toRotationSystem f).image data.toRotationSystem.vertOf := by
  ext v
  have he : edges data.toRotationSystem {f} = orbitFaceBoundary data.toRotationSystem f := by
    simp only [edges, Finset.singleton_biUnion]
  rw [← he, touched_iff]
  simp only [Finset.mem_singleton, Finset.mem_image, mem_orbitFaceDarts_iff]
  exact ⟨fun ⟨d, hv, hf⟩ => ⟨d, hf, hv⟩, fun ⟨d, hf, hv⟩ => ⟨d, hv, hf⟩⟩

include ambient

theorem face_edge_injective (f : OrbitFace data.toRotationSystem) :
    Set.InjOn data.toRotationSystem.edgeOf (orbitFaceDarts data.toRotationSystem f) := by
  apply Finset.card_image_iff.mp
  exact orbitFaceBoundarySimple_of_twoSided data.toRotationSystem
    (GoertzelV24BridgelessFaceTwoSided.BridgelessSphericalCubicMapData.orbitFacesTwoSided
      data.toRotationSystem ambient) f

/-- Facial vertices are not repeated in the actual original dart orbit. -/
theorem face_vertex_injective (f : OrbitFace data.toRotationSystem) :
    Set.InjOn data.toRotationSystem.vertOf (orbitFaceDarts data.toRotationSystem f) := by
  apply Finset.card_image_iff.mp
  rw [← face_vertex_image, single_face_vertex_count data ambient]
  exact Finset.card_image_of_injOn (face_edge_injective data ambient f)

omit ambient

/-- Orient each common edge as it occurs around the added face. -/
def attachmentDarts {S R : Region data} (e : Event S R) : Finset data.toRotationSystem.D :=
  (orbitFaceDarts data.toRotationSystem e.face).filter
    fun d => data.toRotationSystem.edgeOf d ∈ attachmentEdges data e

theorem mem_attachmentDarts {S R : Region data} (e : Event S R) (d : data.toRotationSystem.D) :
    d ∈ attachmentDarts data e ↔ dartOrbitFace data.toRotationSystem d = e.face ∧
      data.toRotationSystem.edgeOf d ∈ attachmentEdges data e := by
  simp only [attachmentDarts, Finset.mem_filter, mem_orbitFaceDarts_iff]

theorem attachment_edge_image {S R : Region data} (e : Event S R) :
    (attachmentDarts data e).image data.toRotationSystem.edgeOf = attachmentEdges data e := by
  ext a
  constructor
  · rintro h
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp h
    exact ((mem_attachmentDarts data e d).mp hd).2
  · intro ha
    obtain ⟨d, hd, hda⟩ := (mem_orbitFaceBoundary_iff data.toRotationSystem e.face a).mp
      (Finset.mem_inter.mp ha).2
    refine Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨hd, ?_⟩, hda⟩
    exact hda.symm ▸ ha

theorem attachment_vertex_image {S R : Region data} (e : Event S R) :
    touched data.toRotationSystem (attachmentEdges data e) =
      (attachmentDarts data e ∪ (attachmentDarts data e).image data.toRotationSystem.phi).image
        data.toRotationSystem.vertOf := by
  ext v
  constructor
  · intro hv
    obtain ⟨d, hdv, hd⟩ := mem_touched.mp hv
    rw [← attachment_edge_image data e] at hd
    obtain ⟨x, hx, hxd⟩ := Finset.mem_image.mp hd
    rcases data.toRotationSystem.edge_fiber_two_cases rfl hxd.symm with heq | heq
    · rw [heq] at hdv
      exact Finset.mem_image.mpr ⟨x, Finset.mem_union_left _ hx, hdv⟩
    · rw [heq] at hdv
      exact Finset.mem_image.mpr ⟨data.toRotationSystem.phi x,
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩),
        (data.toRotationSystem.vert_phi_eq_vert_alpha x).trans hdv⟩
  · intro hv
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hv
    rcases Finset.mem_union.mp hd with hd | hd
    · exact mem_touched.mpr ⟨d, rfl, ((mem_attachmentDarts data e d).mp hd).2⟩
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
      refine mem_touched.mpr ⟨data.toRotationSystem.alpha x,
        (data.toRotationSystem.vert_phi_eq_vert_alpha x).symm, ?_⟩
      rw [data.toRotationSystem.edge_alpha]
      exact ((mem_attachmentDarts data e x).mp hx).2

theorem attachment_successors_in_face {S R : Region data} (e : Event S R) :
    attachmentDarts data e ∪ (attachmentDarts data e).image data.toRotationSystem.phi ⊆
      orbitFaceDarts data.toRotationSystem e.face := by
  intro d hd
  apply (mem_orbitFaceDarts_iff _ _ _).mpr
  rcases Finset.mem_union.mp hd with hd | hd
  · exact ((mem_attachmentDarts data e d).mp hd).1
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
    exact (dartOrbitFace_phi_eq _ x).trans ((mem_attachmentDarts data e x).mp hx).1

include ambient

theorem attachment_darts_card {S R : Region data} (e : Event S R) :
    (attachmentDarts data e).card = (attachmentEdges data e).card := by
  rw [← attachment_edge_image data e]
  exact (Finset.card_image_of_injOn ((face_edge_injective data ambient e.face).mono
    (Finset.filter_subset _ _))).symm

/-- Euler characteristic detects exactly one exit from the attachment. -/
theorem attachment_successor_count {S R : Region data} (e : Event S R) :
    (attachmentDarts data e ∪ (attachmentDarts data e).image data.toRotationSystem.phi).card =
      (attachmentDarts data e).card + 1 := by
  have hv := Finset.card_image_of_injOn ((face_vertex_injective data ambient e.face).mono
    (attachment_successors_in_face data e))
  rw [← attachment_vertex_image data e, attachment_count data ambient e,
    ← attachment_darts_card data ambient e] at hv
  exact hv.symm

/-- Every facial growth event attaches along one nonempty proper ordered
arc, expressed in powers of the original face permutation. -/
theorem exists_attachment_arc {S R : Region data} (e : Event S R) :
    Nonempty (Arc data.toRotationSystem.phi (attachmentDarts data e)) := by
  apply exists_arc_of_union_card _ _ ?_ (attachment_successor_count data ambient e)
  intro x hx y hy
  exact @Quotient.exact _ (Perm.SameCycle.setoid data.toRotationSystem.phi) x y
    (((mem_attachmentDarts data e x).mp hx).1.trans
      ((mem_attachmentDarts data e y).mp hy).1.symm)

end
end Mettapedia.GraphTheory.FourColor.FaceAttachmentArc
