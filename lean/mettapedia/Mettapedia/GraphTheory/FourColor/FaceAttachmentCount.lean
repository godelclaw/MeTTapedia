import Mettapedia.GraphTheory.FourColor.FaceRegionSweep

/-!
# Euler count for the attachment of one original face

For a facial growth event, intersect the old retained edges with the boundary
of the new face. Cubicity shows that the common vertices are precisely those
touched by these common edges. Euler's formula on the old patch, new patch,
and single face gives one more attachment vertex than attachment edge.

Consequently the attachment is nonempty and omits an edge of the added face.
The argument uses the original vertex and edge identifiers throughout.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceAttachmentCount

open GoertzelV24FaceOrbitIncidence GoertzelV24TwoEdgeCutMinimality
open GoertzelV24FaceDualConnectedness
open SimpleGraphDartRotation FaceRegionDegree EdgeShoreRotation
open PlanePatchCurvature FaceRegionShelling FaceRegionSweep
open PhysicalForkCodeCut FaceRegionStepBoundary FaceRegionFaces FaceRegionPatch

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G)
variable (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)

include ambient

/-- Euler characteristic one for the selected disk, counted on its source
vertices, source edges, and selected source faces. -/
theorem region_euler (S : Region data) :
    ((touched data.toRotationSystem (edges data.toRotationSystem S.faces)).card : ℤ) -
        (edges data.toRotationSystem S.faces).card + S.faces.card = 1 := by
  obtain ⟨outer, ho, hp, _⟩ := Region.realizes ambient S
  let T := toMap data.toRotationSystem (edges data.toRotationSystem S.faces) outer
  let : DecidableEq (OrbitFace T) := orbitFaceDecidableEq T
  have hinner : (innerFaces T).card = S.faces.card := by
    have hh := sum_inner_face_lengths outer
      (mem_outerDarts_iff data S.faces ambient outer ho S.inside S.outside) (fun _ => (1 : ℕ))
    simpa using hh
  have hf : (innerFaces T).card + 1 = (Finset.univ : Finset (OrbitFace T)).card :=
    Finset.card_erase_add_one (Finset.mem_univ (outerFace T))
  rw [Finset.card_univ] at hf
  rw [hinner] at hf
  have he := hp.euler
  change (Fintype.card (Vertex data.toRotationSystem (edges data.toRotationSystem S.faces)) : ℤ) -
    Fintype.card (edges data.toRotationSystem S.faces) + Fintype.card (OrbitFace T) = 2 at he
  rw [Fintype.card_coe, Fintype.card_coe, ← hf] at he
  omega

theorem single_face_vertex_count (f : OrbitFace data.toRotationSystem) :
    (touched data.toRotationSystem (orbitFaceBoundary data.toRotationSystem f)).card =
      (orbitFaceBoundary data.toRotationSystem f).card := by
  have hh := region_euler data ambient (single data ambient f)
  simp only [single, edges, Finset.singleton_biUnion, Finset.card_singleton, Nat.cast_one] at hh
  omega

/-- A cubic vertex common to a patch and a new face lies on a common edge.
There are no isolated attachment vertices. -/
theorem touched_face_inter (S : Finset (OrbitFace data.toRotationSystem))
    (f : OrbitFace data.toRotationSystem) (hf : f ∉ S) :
    touched data.toRotationSystem (edges data.toRotationSystem S) ∩
        touched data.toRotationSystem (orbitFaceBoundary data.toRotationSystem f) =
      touched data.toRotationSystem
        (edges data.toRotationSystem S ∩ orbitFaceBoundary data.toRotationSystem f) := by
  ext v
  constructor
  · rintro hv
    obtain ⟨hvS, hvF⟩ := Finset.mem_inter.mp hv
    obtain ⟨e, hev, heS⟩ := (touched_iff data.toRotationSystem S v).mp hvS
    have hvF' : v ∈ touched data.toRotationSystem (edges data.toRotationSystem {f}) := by
      simpa only [edges, Finset.singleton_biUnion] using hvF
    obtain ⟨d, hdv, hdf⟩ := (touched_iff data.toRotationSystem {f} v).mp hvF'
    simp only [Finset.mem_singleton] at hdf
    have hde : d ≠ e := by
      intro heq
      subst e
      exact hf (hdf ▸ heS)
    rcases data.toRotationSystem.rho_eq_or_rho_eq_of_cubic ambient.spherical.cubic
      ambient.vertexRotationCyclic (hev.trans hdv.symm) hde with hforward | hreverse
    · apply mem_touched.mpr
      refine ⟨d, hdv, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · apply (edge_mem_iff_sectors data.toRotationSystem S d).mpr
        exact Or.inr (hforward ▸ heS)
      · exact hdf ▸ edgeOf_mem_orbitFaceBoundary_dartOrbitFace data.toRotationSystem d
    · apply mem_touched.mpr
      refine ⟨e, hev, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · exact (edge_mem_iff data.toRotationSystem S e).mpr (Or.inl heS)
      · have hh : data.toRotationSystem.edgeOf e ∈ edges data.toRotationSystem {f} := by
          apply (edge_mem_iff_sectors data.toRotationSystem {f} e).mpr
          right
          simp only [Finset.mem_singleton]
          exact hreverse ▸ hdf
        simpa only [edges, Finset.singleton_biUnion] using hh
  · intro hv
    obtain ⟨d, hdv, hd⟩ := mem_touched.mp hv
    obtain ⟨hS, hF⟩ := Finset.mem_inter.mp hd
    exact Finset.mem_inter.mpr ⟨mem_touched.mpr ⟨d, hdv, hS⟩,
      mem_touched.mpr ⟨d, hdv, hF⟩⟩

omit ambient

/-- The actual common edges of the old patch and added face. -/
def attachmentEdges {S R : Region data} (e : Event S R) : Finset G.edgeSet :=
  edges data.toRotationSystem S.faces ∩ orbitFaceBoundary data.toRotationSystem e.face

include ambient

/-- The attachment has Euler characteristic one, without assuming it is
connected or that its edges form a boundary interval. -/
theorem attachment_count {S R : Region data} (e : Event S R) :
    (touched data.toRotationSystem (attachmentEdges data e)).card =
      (attachmentEdges data e).card + 1 := by
  have hs := region_euler data ambient S
  have hr := region_euler data ambient R
  have hf := single_face_vertex_count data ambient e.face
  rw [event_retained_edges data e, touched_union, e.card] at hr
  have hv := Finset.card_union_add_card_inter
    (touched data.toRotationSystem (edges data.toRotationSystem S.faces))
    (touched data.toRotationSystem (orbitFaceBoundary data.toRotationSystem e.face))
  have he := Finset.card_union_add_card_inter
    (edges data.toRotationSystem S.faces) (orbitFaceBoundary data.toRotationSystem e.face)
  rw [touched_face_inter data ambient S.faces e.face e.fresh] at hv
  unfold attachmentEdges
  omega

theorem attachment_nonempty {S R : Region data} (e : Event S R) :
    (attachmentEdges data e).Nonempty := by
  have hh := attachment_count data ambient e
  by_contra hn
  have he : attachmentEdges data e = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  simp [he, touched] at hh

/-- Some edge of the added face is new; the whole facial cycle cannot be
an attachment while both the old and new complementary shores are connected. -/
theorem attachment_proper {S R : Region data} (e : Event S R) :
    attachmentEdges data e ⊂ orbitFaceBoundary data.toRotationSystem e.face := by
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.inter_subset_right, ?_⟩
  intro he
  have hh := attachment_count data ambient e
  rw [he, single_face_vertex_count data ambient e.face] at hh
  omega

end
end Mettapedia.GraphTheory.FourColor.FaceAttachmentCount
