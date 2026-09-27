import Mettapedia.GraphTheory.FourColor.FacePairColourExtension
import Mettapedia.GraphTheory.FourColor.ThreeEdgePathChoice

/-!
# Orienting the actual exposed path from a specified old endpoint

An old endpoint and an incident new edge orient the already constructed
facial path. Reversal preserves its exact colouring transfer. At a new
vertex the reconstructed profile comes entirely from the exposed path.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceOrientedTransfer

open GoertzelV24FaceOrbitIncidence GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation FaceRegionDegree EdgeShoreRotation
open FaceRegionShelling FaceRegionComplement PhysicalForkCodeCut PhysicalForkCodeFaces
open FaceExposedBoundary FaceExposedPath FaceExposedEndpoints
open GoertzelV24ForkInterfaceSupport OrderedEdgePath

noncomputable section
attribute [local instance] Classical.propDecidable
set_option autoImplicit false

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G) {S R : Region data} (e : Event S R)

/-- The path, its orientation and its transfer law are all derived from
the actual event and one of its old attachment vertices. -/
theorem exists_oriented_transfer
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    {u : V} (hu : u ∈ touched data.toRotationSystem (edges data.toRotationSystem S.faces))
    {x : G.edgeSet} (hx : x ∈ exposedEdges data e) (hux : u ∈ data.toRotationSystem.endpoints x) :
    ∃ p : Path data.toRotationSystem.endpoints (exposedEdges data e),
      p.first = u ∧ p.length = (exposedEdges data e).card ∧
      p.last ∈ touched data.toRotationSystem (edges data.toRotationSystem S.faces) ∧
      ∀ a c : G.edgeSet → Fin 3,
        Proper data.toRotationSystem.endpoints (edges data.toRotationSystem R.faces)
            (EdgeColouringGluing.glue (edges data.toRotationSystem S.faces) a c) ↔
          Proper data.toRotationSystem.endpoints (edges data.toRotationSystem S.faces) a ∧
          p.Consecutive c ∧ p.EndpointCompatible (edges data.toRotationSystem S.faces) a c := by
  obtain ⟨outer, ho, _, _⟩ := Region.realizes ambient R
  obtain ⟨arc⟩ := exists_exposed_arc data e outer ambient ho
  let p := path data e outer ambient ho arc
  rcases shared_vertex data e ambient outer ho arc hu hx hux with hfirst | hlast
  · exact ⟨p, hfirst.symm, path_length data e outer ambient ho arc,
      last_old data e ambient outer ho arc, FaceColourTransfer.glue_proper_iff data e outer ambient ho arc⟩
  · refine ⟨p.reverse, hlast.symm, path_length data e outer ambient ho arc, ?_, ?_⟩
    · simpa using first_old data e ambient outer ho arc
    · intro a c
      rw [FaceColourTransfer.glue_proper_iff data e outer ambient ho arc]
      change (_ ∧ p.Consecutive c ∧ p.EndpointCompatible _ a c) ↔
        (_ ∧ p.reverse.Consecutive c ∧ p.reverse.EndpointCompatible _ a c)
      have hc : p.Consecutive c ↔ p.reverse.Consecutive c :=
        (p.proper_iff c).symm.trans (p.reverse.proper_iff c)
      rw [hc]
      simp only [Path.EndpointCompatible, Path.reverse_first, Path.reverse_last,
        Path.reverse_firstEdge, Path.reverse_lastEdge]
      tauto

/-- A vertex absent from a face-generated patch has empty old profile. -/
theorem profile_empty_of_new {v : V}
    (hv : v ∉ touched data.toRotationSystem (edges data.toRotationSystem S.faces))
    (a : G.edgeSet → Fin 3) :
    profile data.toRotationSystem.endpoints (edges data.toRotationSystem S.faces) a v = ∅ := by
  apply Finset.image_eq_empty.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro x hx hvx
  obtain ⟨d, hd, hdv⟩ := data.toRotationSystem.mem_endpoints_iff.mp hvx
  exact hv (mem_touched.mpr ⟨d, hdv,
    (data.toRotationSystem.mem_dartsOn.mp hd).symm ▸ hx⟩)

/-- The full profile at a new vertex is precisely its exposed-path profile. -/
theorem profile_at_new {v : V}
    (hv : v ∉ touched data.toRotationSystem (edges data.toRotationSystem S.faces))
    (a : G.edgeSet → Fin 3) :
    profile data.toRotationSystem.endpoints (edges data.toRotationSystem R.faces) a v =
      profile data.toRotationSystem.endpoints (exposedEdges data e) a v := by
  rw [FaceColourTransfer.shores_union data e, profile_union]
  change profile _ _ a v ∪ profile _ _ a v = _
  rw [profile_empty_of_new data hv a, Finset.empty_union]

/-- Exact marked-vertex transfer for a three-edge event, after its
geometric path and transfer have been constructed. -/
theorem three_edge_marked_transfer
    (p : Path data.toRotationSystem.endpoints (exposedEdges data e)) (hp : p.length = 3)
    (transfer : ∀ a c : G.edgeSet → Fin 3,
      Proper data.toRotationSystem.endpoints (edges data.toRotationSystem R.faces)
          (EdgeColouringGluing.glue (edges data.toRotationSystem S.faces) a c) ↔
        Proper data.toRotationSystem.endpoints (edges data.toRotationSystem S.faces) a ∧
        p.Consecutive c ∧ p.EndpointCompatible (edges data.toRotationSystem S.faces) a c)
    (hv : p.nextVertex ∉ touched data.toRotationSystem (edges data.toRotationSystem S.faces))
    (a : G.edgeSet → Fin 3)
    (ha : Proper data.toRotationSystem.endpoints (edges data.toRotationSystem S.faces) a)
    (r s q : Fin 3)
    (hr : ∀ t, t ∉ profile data.toRotationSystem.endpoints
      (edges data.toRotationSystem S.faces) a p.first ↔ t = r)
    (hs : ∀ t, t ∉ profile data.toRotationSystem.endpoints
      (edges data.toRotationSystem S.faces) a p.last ↔ t = s) :
    (∃ b : G.edgeSet → Fin 3,
      Proper data.toRotationSystem.endpoints (edges data.toRotationSystem R.faces) b ∧
      (∀ x ∈ edges data.toRotationSystem S.faces, b x = a x) ∧
      q ∈ profile data.toRotationSystem.endpoints (edges data.toRotationSystem R.faces) b p.nextVertex) ↔
        q = r ∨ q ≠ s := by
  rw [← p.prescribed_using_next_three_iff hp r s q]
  constructor
  · rintro ⟨b, hb, hba, hq⟩
    have hglue : EdgeColouringGluing.glue (edges data.toRotationSystem S.faces) a b = b := by
      funext x
      by_cases hx : x ∈ edges data.toRotationSystem S.faces
      · exact (EdgeColouringGluing.glue_left _ a b hx).trans (hba x hx).symm
      · simp [EdgeColouringGluing.glue, hx]
    have ht := (transfer a b).mp (hglue.symm ▸ hb)
    exact ⟨b, ht.2.1, (hr _).mp ht.2.2.1, (hs _).mp ht.2.2.2,
      (profile_at_new data e hv b) ▸ hq⟩
  · rintro ⟨c, hc, hcr, hcs, hq⟩
    refine ⟨EdgeColouringGluing.glue (edges data.toRotationSystem S.faces) a c,
      (transfer a c).mpr ⟨ha, hc, (hr _).mpr hcr, (hs _).mpr hcs⟩,
      fun _ hx => EdgeColouringGluing.glue_left _ a c hx, ?_⟩
    rw [FaceColourTransfer.reconstructed_profile data e]
    exact Finset.mem_union_right _ hq

end
end Mettapedia.GraphTheory.FourColor.FaceOrientedTransfer
