import Mettapedia.GraphTheory.FourColor.FaceExposedDegrees
import Mettapedia.GraphTheory.FourColor.OrderedPathFlexibility

/-!
# Compatible choices for two facial additions

A first addition with at least four exposed edges can choose its colours
to accommodate a later two-edge addition. One contact is a new vertex
adjacent to the original patch; the other lies in the original patch.
Only the original colouring is fixed before the pair is constructed.
-/

namespace Mettapedia.GraphTheory.FourColor.FacePairColourExtension

open GoertzelV24FaceOrbitIncidence GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation FaceRegionDegree EdgeShoreRotation
open FaceRegionShelling FaceRegionComplement PhysicalForkCodeCut PhysicalForkCodeFaces
open PermutationSingleExitArc FaceExposedBoundary FaceExposedPath FaceExposedEndpoints
open GoertzelV24ForkInterfaceSupport OrderedEdgePath

noncomputable section
attribute [local instance] Classical.propDecidable
set_option autoImplicit false

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G) {S R T : Region data} (e : Event S R)
variable (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)


variable (f : Event R T)

include e in
theorem retained_subset :
    edges data.toRotationSystem S.faces ⊆ edges data.toRotationSystem R.faces := by
  rw [FaceRegionStepBoundary.event_retained_edges data e]
  exact Finset.subset_union_left

include ambient f in
/-- An original vertex where the second event adds an edge could not have
acquired an edge in the first event: cubicity leaves only one free slot. -/
theorem old_endpoint_untouched {v : V}
    (hv : v ∈ touched data.toRotationSystem (edges data.toRotationSystem S.faces))
    {y : G.edgeSet} (hy : y ∈ exposedEdges data f) (hvy : v ∈ data.toRotationSystem.endpoints y) :
    ∀ x ∈ exposedEdges data e, v ∉ data.toRotationSystem.endpoints x := by
  have hvR : v ∈ touched data.toRotationSystem (edges data.toRotationSystem R.faces) := by
    obtain ⟨d, hd, he⟩ := mem_touched.mp hv
    exact mem_touched.mpr ⟨d, hd, retained_subset data e he⟩
  have htwo := FaceRegionMissingColour.incident_card_two
    (cubic3_of _ ambient.spherical.cubic ambient.vertexRotationCyclic)
    ambient.spherical.cubic hvR (Finset.mem_sdiff.mp hy).2 hvy
  rw [FaceRegionMissingColour.incident_card] at htwo
  intro x hx hvx
  have hthree := FaceExposedDegrees.degree_three_at_old_new_edge data e ambient hv hx hvx
  omega

include ambient e in
/-- The endpoint reserved for the second event retains its original
profile under every first-event colouring that agrees on old edges. -/
theorem profile_eq_old_at_endpoint {v : V}
    (hv : v ∈ touched data.toRotationSystem (edges data.toRotationSystem S.faces))
    {y : G.edgeSet} (hy : y ∈ exposedEdges data f) (hvy : v ∈ data.toRotationSystem.endpoints y)
    (a c : G.edgeSet → Fin 3)
    (hca : ∀ x ∈ edges data.toRotationSystem S.faces, c x = a x) :
    profile data.toRotationSystem.endpoints (edges data.toRotationSystem R.faces) c v =
      profile data.toRotationSystem.endpoints (edges data.toRotationSystem S.faces) a v := by
  have hempty : profile data.toRotationSystem.endpoints (exposedEdges data e) c v = ∅ := by
    apply Finset.image_eq_empty.mpr
    exact Finset.filter_eq_empty_iff.mpr (old_endpoint_untouched data e ambient f hv hy hvy)
  rw [FaceColourTransfer.shores_union data e, profile_union]
  change profile _ _ c v ∪ profile _ _ c v = _
  rw [EdgeColouringGluing.profile_congr _ _ c a hca, hempty, Finset.union_empty]

include ambient in
/-- The first colouring can be chosen at a new vertex adjacent to an
original vertex. The source map supplies the exposed path and its order. -/
theorem extends_using_adjacent (hn : 4 ≤ (exposedEdges data e).card)
    {u v : V}
    (hu : u ∈ touched data.toRotationSystem (edges data.toRotationSystem S.faces))
    (hv : v ∉ touched data.toRotationSystem (edges data.toRotationSystem S.faces))
    {x : G.edgeSet} (hx : x ∈ exposedEdges data e)
    (hux : u ∈ data.toRotationSystem.endpoints x) (hvx : v ∈ data.toRotationSystem.endpoints x)
    (a : G.edgeSet → Fin 3)
    (ha : Proper data.toRotationSystem.endpoints (edges data.toRotationSystem S.faces) a)
    (q : Fin 3) :
    ∃ b : G.edgeSet → Fin 3,
      Proper data.toRotationSystem.endpoints (edges data.toRotationSystem R.faces) b ∧
      (∀ x ∈ edges data.toRotationSystem S.faces, b x = a x) ∧
      q ∈ profile data.toRotationSystem.endpoints (edges data.toRotationSystem R.faces) b v := by
  obtain ⟨outer, ho, _, _⟩ := Region.realizes ambient R
  obtain ⟨arc⟩ := exists_exposed_arc data e outer ambient ho
  let p := path data e outer ambient ho arc
  have hp : p.EndNeighbour v := by
    rcases shared_vertex data e ambient outer ho arc hu hx hux with hfirst | hlast
    · left
      have he := p.eq_firstEdge hx (hfirst ▸ hux)
      exact ⟨he ▸ hvx, fun hh => hv (hh.symm ▸ first_old data e ambient outer ho arc)⟩
    · right
      have he := p.eq_lastEdge hx (hlast ▸ hux)
      exact ⟨he ▸ hvx, fun hh => hv (hh.symm ▸ last_old data e ambient outer ho arc)⟩
  obtain ⟨r, s, hr, hs⟩ := FacePathExtension.endpoint_colours data e outer ambient ho arc a ha
  have hp4 : 4 ≤ p.length := by rw [path_length]; exact hn
  obtain ⟨c, hc, hcr, hcs, hq⟩ := p.prescribed_using_neighbour hp4 v hp r s q
  refine ⟨EdgeColouringGluing.glue (edges data.toRotationSystem S.faces) a c, ?_, ?_, ?_⟩
  · exact (FaceColourTransfer.glue_proper_iff data e outer ambient ho arc a c).mpr
      ⟨ha, hc, (hr _).mpr hcr, (hs _).mpr hcs⟩
  · exact fun _ hx => EdgeColouringGluing.glue_left _ a c hx
  · rw [FaceColourTransfer.reconstructed_profile data e]
    exact Finset.mem_union_right _ hq

include ambient in
/-- Two actual additions admit compatible choices whenever the second
adds two edges between an original vertex and a new vertex adjacent to
an original vertex through the first addition. All geometric paths and
endpoint profiles are derived from these incidences. -/
theorem extends_pair_of_adjacent_contact
    (hn : 4 ≤ (exposedEdges data e).card) (hnT : (exposedEdges data f).card = 2)
    {u v w : V}
    (hu : u ∈ touched data.toRotationSystem (edges data.toRotationSystem S.faces))
    (hw : w ∈ touched data.toRotationSystem (edges data.toRotationSystem S.faces))
    {x y z : G.edgeSet}
    (hx : x ∈ exposedEdges data e)
    (hux : u ∈ data.toRotationSystem.endpoints x) (hvx : v ∈ data.toRotationSystem.endpoints x)
    (hy : y ∈ exposedEdges data f) (hwy : w ∈ data.toRotationSystem.endpoints y)
    (hz : z ∈ exposedEdges data f) (hvz : v ∈ data.toRotationSystem.endpoints z)
    (a : G.edgeSet → Fin 3)
    (ha : Proper data.toRotationSystem.endpoints (edges data.toRotationSystem S.faces) a) :
    ∃ b c : G.edgeSet → Fin 3,
      Proper data.toRotationSystem.endpoints (edges data.toRotationSystem R.faces) b ∧
      (∀ x ∈ edges data.toRotationSystem S.faces, b x = a x) ∧
      Proper data.toRotationSystem.endpoints (edges data.toRotationSystem T.faces) c ∧
      (∀ x ∈ edges data.toRotationSystem R.faces, c x = b x) := by
  have hv : v ∉ touched data.toRotationSystem (edges data.toRotationSystem S.faces) := by
    intro hv
    exact old_endpoint_untouched data e ambient f hv hz hvz x hx hvx
  have hvw : v ≠ w := fun he => hv (he.symm ▸ hw)
  have hyS : y ∉ edges data.toRotationSystem S.faces :=
    fun hyS => (Finset.mem_sdiff.mp hy).2 (retained_subset data e hyS)
  obtain ⟨q, hq, _⟩ := FaceRegionMissingColour.existsUnique_missing
    (cubic3_of _ ambient.spherical.cubic ambient.vertexRotationCyclic)
    ambient.spherical.cubic hw hyS hwy ha
  obtain ⟨b, hb, hba, hqv⟩ := extends_using_adjacent data e ambient hn hu hv hx hux hvx a ha q
  have hqw : q ∉ profile data.toRotationSystem.endpoints
      (edges data.toRotationSystem R.faces) b w := by
    rw [profile_eq_old_at_endpoint data e ambient f hw hy hwy a b hba]
    exact hq
  obtain ⟨outer, ho, _, _⟩ := Region.realizes ambient T
  obtain ⟨arc⟩ := exists_exposed_arc data f outer ambient ho
  let p := path data f outer ambient ho arc
  have hvR : v ∈ touched data.toRotationSystem (edges data.toRotationSystem R.faces) := by
    obtain ⟨d, hd, hdv⟩ := data.toRotationSystem.mem_endpoints_iff.mp hvx
    exact mem_touched.mpr ⟨d, hdv,
      (data.toRotationSystem.mem_dartsOn.mp hd).symm ▸ exposed_mem_new data e hx⟩
  have hwR : w ∈ touched data.toRotationSystem (edges data.toRotationSystem R.faces) := by
    obtain ⟨d, hd, he⟩ := mem_touched.mp hw
    exact mem_touched.mpr ⟨d, hd, retained_subset data e he⟩
  have hvEnds := shared_vertex data f ambient outer ho arc hvR hz hvz
  have hwEnds := shared_vertex data f ambient outer ho arc hwR hy hwy
  obtain ⟨r, s, hr, hs, hext⟩ :=
    FacePathExtension.extension_classification data f outer ambient ho arc b hb
  have hrs : r ≠ s := by
    intro hrs
    rcases hvEnds with hvFirst | hvLast <;> rcases hwEnds with hwFirst | hwLast
    · exact hvw (hvFirst.trans hwFirst.symm)
    · have hqs : q = s := (hs q).mp (by rw [← hwLast]; exact hqw)
      have hno := (hr q).mpr (hqs.trans hrs.symm)
      rw [← hvFirst] at hno
      exact hno hqv
    · have hqr : q = r := (hr q).mp (by rw [← hwFirst]; exact hqw)
      have hno := (hs q).mpr (hqr.trans hrs)
      rw [← hvLast] at hno
      exact hno hqv
    · exact hvw (hvLast.trans hwLast.symm)
  obtain ⟨c, hc, hcb⟩ := hext.mpr (Or.inr (Or.inl ⟨hnT, hrs⟩))
  exact ⟨b, c, hb, hba, hc, hcb⟩

end
end Mettapedia.GraphTheory.FourColor.FacePairColourExtension
