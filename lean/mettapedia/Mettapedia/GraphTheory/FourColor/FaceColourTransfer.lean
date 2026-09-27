import Mettapedia.GraphTheory.FourColor.FaceExposedEndpoints
import Mettapedia.GraphTheory.FourColor.EdgeColouringGluing

/-!
# Exact colouring transfer for an actual facial construction

A facial event adds a simple edge path whose internal vertices are new.
For any chosen old colouring, a chosen colouring of the new edges extends
it precisely when consecutive path colours differ and its two end colours
are absent from the corresponding old endpoint profiles. The witness is
the literal union of those assignments, preserving every old edge colour.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceColourTransfer

open GoertzelV24FaceOrbitIncidence GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation FaceRegionDegree EdgeShoreRotation
open FaceRegionShelling FaceRegionComplement PhysicalForkCodeCut
open PermutationSingleExitArc FaceExposedBoundary FaceExposedPath FaceExposedEndpoints
open GoertzelV24ForkInterfaceSupport

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G)
variable {S R : Region data} (e : Event S R)

theorem shores_disjoint :
    Disjoint (edges data.toRotationSystem S.faces) (exposedEdges data e) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact (Finset.mem_sdiff.mp hy).2 hx

theorem shores_union :
    edges data.toRotationSystem R.faces =
      edges data.toRotationSystem S.faces ∪ exposedEdges data e := by
  rw [FaceRegionStepBoundary.event_retained_edges data e]
  ext x
  simp only [exposedEdges, Finset.mem_union, Finset.mem_sdiff]
  tauto

variable (outer : Dart data.toRotationSystem (edges data.toRotationSystem R.faces))
variable (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
variable (ho : dartOrbitFace data.toRotationSystem outer.val ∉ R.faces)
variable (b : Arc
  (toMap data.toRotationSystem (edges data.toRotationSystem R.faces) outer).phi
  (exposedDarts data e outer))

/-- Only the two actual attachment vertices enter this test. -/
abbrev EndpointCompatible (a c : G.edgeSet → Fin 3) : Prop :=
  (path data e outer ambient ho b).EndpointCompatible (edges data.toRotationSystem S.faces) a c

/-- Full vertexwise compatibility reduces to the two endpoint tests.
Properness is not assumed or hidden in this reduction. -/
theorem compatible_iff_endpoints (a c : G.edgeSet → Fin 3) :
    Compatible
        (profile data.toRotationSystem.endpoints (edges data.toRotationSystem S.faces) a)
        (profile data.toRotationSystem.endpoints (exposedEdges data e) c) ↔
      EndpointCompatible data e outer ambient ho b a c := by
  let p := path data e outer ambient ho b
  constructor
  · intro h
    have hfirst := h p.first
    have hlast := h p.last
    rw [p.profile_first] at hfirst
    rw [p.profile_last] at hlast
    exact ⟨Finset.disjoint_singleton_right.mp hfirst, Finset.disjoint_singleton_right.mp hlast⟩
  · intro h v
    apply Finset.disjoint_left.mpr
    intro colour ha hc
    obtain ⟨x, hx, _⟩ := Finset.mem_image.mp ha
    obtain ⟨hxS, hvx⟩ := Finset.mem_filter.mp hx
    obtain ⟨d, hd, hdv⟩ := data.toRotationSystem.mem_endpoints_iff.mp hvx
    have hv : v ∈ touched data.toRotationSystem (edges data.toRotationSystem S.faces) :=
      mem_touched.mpr ⟨d, hdv, (data.toRotationSystem.mem_dartsOn.mp hd).symm ▸ hxS⟩
    obtain ⟨y, hy, _⟩ := Finset.mem_image.mp hc
    obtain ⟨hyX, hvy⟩ := Finset.mem_filter.mp hy
    rcases shared_vertex data e ambient outer ho b hv hyX hvy with hv | hv
    · rw [hv, p.profile_first, Finset.mem_singleton] at hc
      exact h.1 (by simpa only [hv, hc] using ha)
    · rw [hv, p.profile_last, Finset.mem_singleton] at hc
      exact h.2 (by simpa only [hv, hc] using ha)

/-- The exact one-event transfer relation, including a literal reconstructed
colouring. No extension or richness premise is assumed. -/
theorem glue_proper_iff (a c : G.edgeSet → Fin 3) :
    Proper data.toRotationSystem.endpoints (edges data.toRotationSystem R.faces)
        (EdgeColouringGluing.glue (edges data.toRotationSystem S.faces) a c) ↔
      Proper data.toRotationSystem.endpoints (edges data.toRotationSystem S.faces) a ∧
        (path data e outer ambient ho b).Consecutive c ∧
        EndpointCompatible data e outer ambient ho b a c := by
  rw [shores_union data e,
    EdgeColouringGluing.glue_proper_iff _ _ _ (shores_disjoint data e),
    FaceExposedPath.proper_iff data e outer ambient ho b,
    compatible_iff_endpoints data e outer ambient ho b]

/-- The reconstructed witness presents exactly the union of the two piece
profiles, so it is the same operation as the existing support fork law. -/
theorem reconstructed_profile (a c : G.edgeSet → Fin 3) :
    profile data.toRotationSystem.endpoints (edges data.toRotationSystem R.faces)
        (EdgeColouringGluing.glue (edges data.toRotationSystem S.faces) a c) =
      merge (profile data.toRotationSystem.endpoints (edges data.toRotationSystem S.faces) a)
        (profile data.toRotationSystem.endpoints (exposedEdges data e) c) := by
  rw [shores_union data e]
  exact EdgeColouringGluing.profile_glue _ _ _ (shores_disjoint data e) a c

/-- The existing finite support fork reduces to two compatibility tests
for a facial event. It retains every realizable profile. -/
theorem support_transfer :
    GoertzelV24ForkInterfaceSupport.support data.toRotationSystem.endpoints
        (edges data.toRotationSystem R.faces) =
      (((GoertzelV24ForkInterfaceSupport.support data.toRotationSystem.endpoints
          (edges data.toRotationSystem S.faces)) ×ˢ
          (GoertzelV24ForkInterfaceSupport.support data.toRotationSystem.endpoints
            (exposedEdges data e))).filter
        (fun qr =>
          Disjoint (qr.1 (path data e outer ambient ho b).first)
            (qr.2 (path data e outer ambient ho b).first) ∧
          Disjoint (qr.1 (path data e outer ambient ho b).last)
            (qr.2 (path data e outer ambient ho b).last))).image
        (fun qr => merge qr.1 qr.2) := by
  rw [shores_union data e, GoertzelV24ForkInterfaceSupport.support_union _ _ _ (shores_disjoint data e)]
  congr 1
  apply Finset.filter_congr
  rintro ⟨q, r⟩ hqr
  obtain ⟨ha, hc⟩ := Finset.mem_product.mp hqr
  obtain ⟨a, _, rfl⟩ := mem_support.mp ha
  obtain ⟨c, _, rfl⟩ := mem_support.mp hc
  dsimp only
  rw [compatible_iff_endpoints data e outer ambient ho b,
    (path data e outer ambient ho b).profile_first,
    (path data e outer ambient ho b).profile_last]
  simp only [Finset.disjoint_singleton_right]
  rfl

/-- Every extension is recovered by the transfer law; conversely every
successful local choice constructs an extension preserving the old witness. -/
theorem extension_iff (a : G.edgeSet → Fin 3)
    (ha : Proper data.toRotationSystem.endpoints (edges data.toRotationSystem S.faces) a) :
    (∃ d : G.edgeSet → Fin 3,
      Proper data.toRotationSystem.endpoints (edges data.toRotationSystem R.faces) d ∧
        ∀ x ∈ edges data.toRotationSystem S.faces, d x = a x) ↔
      ∃ c : G.edgeSet → Fin 3, (path data e outer ambient ho b).Consecutive c ∧
        EndpointCompatible data e outer ambient ho b a c := by
  constructor
  · rintro ⟨d, hd, hda⟩
    have heq : EdgeColouringGluing.glue (edges data.toRotationSystem S.faces) a d = d := by
      funext x
      by_cases hx : x ∈ edges data.toRotationSystem S.faces
      · exact (EdgeColouringGluing.glue_left _ a d hx).trans (hda x hx).symm
      · simp [EdgeColouringGluing.glue, hx]
    refine ⟨d, ?_⟩
    have ht := (glue_proper_iff data e outer ambient ho b a d).mp (heq.symm ▸ hd)
    exact ht.2
  · rintro ⟨c, hc, hends⟩
    refine ⟨EdgeColouringGluing.glue (edges data.toRotationSystem S.faces) a c,
      (glue_proper_iff data e outer ambient ho b a c).mpr ⟨ha, hc, hends⟩, ?_⟩
    exact fun _ hx => EdgeColouringGluing.glue_left _ a c hx

include ambient in
/-- Every event supplies its own geometric path and exact transfer law.
There is no boundary-arc or colouring-lifting assumption. -/
theorem exists_exact_transfer :
    ∃ p : OrderedEdgePath.Path data.toRotationSystem.endpoints (exposedEdges data e),
      p.length = (exposedEdges data e).card ∧
      ∀ a c : G.edgeSet → Fin 3,
        Proper data.toRotationSystem.endpoints (edges data.toRotationSystem R.faces)
            (EdgeColouringGluing.glue (edges data.toRotationSystem S.faces) a c) ↔
          Proper data.toRotationSystem.endpoints (edges data.toRotationSystem S.faces) a ∧
            p.Consecutive c ∧ p.EndpointCompatible (edges data.toRotationSystem S.faces) a c := by
  obtain ⟨oR, hR, _, _⟩ := Region.realizes ambient R
  obtain ⟨arc⟩ := exists_exposed_arc data e oR ambient hR
  exact ⟨path data e oR ambient hR arc, path_length data e oR ambient hR arc,
    glue_proper_iff data e oR ambient hR arc⟩

end
end Mettapedia.GraphTheory.FourColor.FaceColourTransfer
