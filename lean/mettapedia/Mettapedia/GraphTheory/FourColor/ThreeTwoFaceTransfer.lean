import Mettapedia.GraphTheory.FourColor.FaceOrientedTransfer

/-!
# Exact compatibility for a three-edge then two-edge facial pair

The first path runs from an old vertex u through a new vertex v to its
other old endpoint t. The second path runs from v to an old vertex w.
If the original missing colours at u,t,w are r,s,q, respectively, the
pair extends the original colouring exactly when q = r or q differs
from s. The other endpoint and all missing colours are constructed.
-/

namespace Mettapedia.GraphTheory.FourColor.ThreeTwoFaceTransfer

open GoertzelV24FaceOrbitIncidence GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation FaceRegionDegree EdgeShoreRotation
open FaceRegionShelling FaceRegionComplement PhysicalForkCodeCut PhysicalForkCodeFaces
open FaceExposedBoundary FaceExposedPath FaceExposedEndpoints
open GoertzelV24ForkInterfaceSupport OrderedEdgePath FacePairColourExtension

noncomputable section
attribute [local instance] Classical.propDecidable
set_option autoImplicit false

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G)
variable (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)

include ambient

/-- At a two-edge attachment, the colour missing at one endpoint must
already occur at the other. Both endpoints are identified by incidence. -/
theorem two_edge_extension_iff_used {R T : Region data} (f : Event R T)
    (hn : (exposedEdges data f).card = 2) {v w : V} (hvw : v ≠ w)
    (hv : v ∈ touched data.toRotationSystem (edges data.toRotationSystem R.faces))
    (hw : w ∈ touched data.toRotationSystem (edges data.toRotationSystem R.faces))
    {y z : G.edgeSet} (hy : y ∈ exposedEdges data f) (hwy : w ∈ data.toRotationSystem.endpoints y)
    (hz : z ∈ exposedEdges data f) (hvz : v ∈ data.toRotationSystem.endpoints z)
    (b : G.edgeSet → Fin 3)
    (hb : Proper data.toRotationSystem.endpoints (edges data.toRotationSystem R.faces) b)
    (q : Fin 3) (hq : q ∉ profile data.toRotationSystem.endpoints
      (edges data.toRotationSystem R.faces) b w) :
    (∃ c : G.edgeSet → Fin 3,
      Proper data.toRotationSystem.endpoints (edges data.toRotationSystem T.faces) c ∧
      ∀ x ∈ edges data.toRotationSystem R.faces, c x = b x) ↔
      q ∈ profile data.toRotationSystem.endpoints (edges data.toRotationSystem R.faces) b v := by
  obtain ⟨outer, ho, _, _⟩ := Region.realizes ambient T
  obtain ⟨arc⟩ := exists_exposed_arc data f outer ambient ho
  obtain ⟨r, s, hr, hs, hext⟩ :=
    FacePathExtension.extension_classification data f outer ambient ho arc b hb
  have hext' : (∃ c : G.edgeSet → Fin 3,
      Proper data.toRotationSystem.endpoints (edges data.toRotationSystem T.faces) c ∧
      ∀ x ∈ edges data.toRotationSystem R.faces, c x = b x) ↔ r ≠ s := by
    simpa [hn] using hext
  rw [hext']
  have hvEnds := shared_vertex data f ambient outer ho arc hv hz hvz
  have hwEnds := shared_vertex data f ambient outer ho arc hw hy hwy
  rcases hvEnds with hvf | hvl <;> rcases hwEnds with hwf | hwl
  · exact (hvw (hvf.trans hwf.symm)).elim
  · have hqs : q = s := (hs q).mp (hwl ▸ hq)
    have key := hr q
    rw [← hvf, hqs] at key
    rw [hqs]
    constructor
    · intro hne
      by_contra hnot
      exact hne (key.mp hnot).symm
    · intro hmem heq
      exact (key.mpr heq.symm) hmem
  · have hqr : q = r := (hr q).mp (hwf ▸ hq)
    have key := hs q
    rw [← hvl, hqr] at key
    rw [hqr]
    constructor
    · intro hne
      by_contra hnot
      exact hne (key.mp hnot)
    · intro hmem heq
      exact (key.mpr heq) hmem
  · exact (hvw (hvl.trans hwl.symm)).elim

/-- Source geometry supplies the other endpoint and the three missing
colours. The criterion is exact for jointly chosen extensions, without
fixing the intermediate colouring in advance. -/
theorem exists_exact_criterion {S R T : Region data} (e : Event S R) (f : Event R T)
    (hn : (exposedEdges data e).card = 3) (hnT : (exposedEdges data f).card = 2)
    {u v w : V}
    (hu : u ∈ touched data.toRotationSystem (edges data.toRotationSystem S.faces))
    (hw : w ∈ touched data.toRotationSystem (edges data.toRotationSystem S.faces))
    {x y z : G.edgeSet} (hx : x ∈ exposedEdges data e)
    (hux : u ∈ data.toRotationSystem.endpoints x) (hvx : v ∈ data.toRotationSystem.endpoints x)
    (hy : y ∈ exposedEdges data f) (hwy : w ∈ data.toRotationSystem.endpoints y)
    (hz : z ∈ exposedEdges data f) (hvz : v ∈ data.toRotationSystem.endpoints z) :
    ∃ t : V, t ∈ touched data.toRotationSystem (edges data.toRotationSystem S.faces) ∧
      t ≠ u ∧ t ≠ w ∧ u ≠ w ∧
      ∀ a : G.edgeSet → Fin 3,
        Proper data.toRotationSystem.endpoints (edges data.toRotationSystem S.faces) a →
        ∃ r s q : Fin 3,
          (∀ k, k ∉ profile data.toRotationSystem.endpoints
            (edges data.toRotationSystem S.faces) a u ↔ k = r) ∧
          (∀ k, k ∉ profile data.toRotationSystem.endpoints
            (edges data.toRotationSystem S.faces) a t ↔ k = s) ∧
          (∀ k, k ∉ profile data.toRotationSystem.endpoints
            (edges data.toRotationSystem S.faces) a w ↔ k = q) ∧
          ((∃ b c : G.edgeSet → Fin 3,
            Proper data.toRotationSystem.endpoints (edges data.toRotationSystem R.faces) b ∧
            (∀ x ∈ edges data.toRotationSystem S.faces, b x = a x) ∧
            Proper data.toRotationSystem.endpoints (edges data.toRotationSystem T.faces) c ∧
            (∀ x ∈ edges data.toRotationSystem R.faces, c x = b x)) ↔ q = r ∨ q ≠ s) := by
  have hv : v ∉ touched data.toRotationSystem (edges data.toRotationSystem S.faces) := by
    intro hv
    exact old_endpoint_untouched data e ambient f hv hz hvz x hx hvx
  have hvw : v ≠ w := fun he => hv (he.symm ▸ hw)
  obtain ⟨p, hpu, hlen, hpt, transfer⟩ :=
    FaceOrientedTransfer.exists_oriented_transfer data e ambient hu hx hux
  have hxfirst : x = p.firstEdge := p.eq_firstEdge hx (hpu.symm ▸ hux)
  have hvnext : v = p.nextVertex := p.eq_next_of_first_edge (hxfirst ▸ hvx)
    (fun h => hv (h.symm ▸ (hpu.symm ▸ hu)))
  refine ⟨p.last, hpt, ?_, ?_, ?_, ?_⟩
  · simpa only [hpu] using Ne.symm p.first_ne_last
  · intro htw
    exact old_endpoint_untouched data e ambient f hw hy hwy
      p.lastEdge p.lastEdge_mem (htw ▸ p.lastEdge_incident)
  · intro huw
    exact old_endpoint_untouched data e ambient f hw hy hwy x hx (huw ▸ hux)
  · intro a ha
    have hC := cubic3_of _ ambient.spherical.cubic ambient.vertexRotationCyclic
    obtain ⟨r, hr, hur⟩ := FaceRegionMissingColour.existsUnique_missing hC ambient.spherical.cubic
      (hpu.symm ▸ hu) (Finset.mem_sdiff.mp p.firstEdge_mem).2 p.firstEdge_incident ha
    obtain ⟨s, hs, hus⟩ := FaceRegionMissingColour.existsUnique_missing hC ambient.spherical.cubic
      hpt (Finset.mem_sdiff.mp p.lastEdge_mem).2 p.lastEdge_incident ha
    have hyS : y ∉ edges data.toRotationSystem S.faces :=
      fun hyS => (Finset.mem_sdiff.mp hy).2 (retained_subset data e hyS)
    obtain ⟨q, hq, huq⟩ := FaceRegionMissingColour.existsUnique_missing hC ambient.spherical.cubic
      hw hyS hwy ha
    have hriff : ∀ k, k ∉ profile data.toRotationSystem.endpoints
        (edges data.toRotationSystem S.faces) a p.first ↔ k = r :=
      fun k => ⟨hur k, fun hk => hk.symm ▸ hr⟩
    have hsiff : ∀ k, k ∉ profile data.toRotationSystem.endpoints
        (edges data.toRotationSystem S.faces) a p.last ↔ k = s :=
      fun k => ⟨hus k, fun hk => hk.symm ▸ hs⟩
    refine ⟨r, s, q, hpu ▸ hriff, hsiff, fun k => ⟨huq k, fun hk => hk.symm ▸ hq⟩, ?_⟩
    have hmarked := FaceOrientedTransfer.three_edge_marked_transfer data e p (hlen.trans hn)
      transfer (hvnext ▸ hv) a ha r s q hriff hsiff
    rw [← hvnext] at hmarked
    have hvR : v ∈ touched data.toRotationSystem (edges data.toRotationSystem R.faces) := by
      obtain ⟨d, hd, hdv⟩ := data.toRotationSystem.mem_endpoints_iff.mp hvx
      exact mem_touched.mpr ⟨d, hdv,
        (data.toRotationSystem.mem_dartsOn.mp hd).symm ▸ exposed_mem_new data e hx⟩
    have hwR : w ∈ touched data.toRotationSystem (edges data.toRotationSystem R.faces) := by
      obtain ⟨d, hd, he⟩ := mem_touched.mp hw
      exact mem_touched.mpr ⟨d, hd, retained_subset data e he⟩
    have second (b : G.edgeSet → Fin 3)
        (hb : Proper data.toRotationSystem.endpoints (edges data.toRotationSystem R.faces) b)
        (hba : ∀ x ∈ edges data.toRotationSystem S.faces, b x = a x) :
        (∃ c : G.edgeSet → Fin 3,
          Proper data.toRotationSystem.endpoints (edges data.toRotationSystem T.faces) c ∧
          ∀ x ∈ edges data.toRotationSystem R.faces, c x = b x) ↔
        q ∈ profile data.toRotationSystem.endpoints (edges data.toRotationSystem R.faces) b v := by
      apply two_edge_extension_iff_used data ambient f hnT hvw hvR hwR hy hwy hz hvz b hb q
      rw [profile_eq_old_at_endpoint data e ambient f hw hy hwy a b hba]
      exact hq
    constructor
    · rintro ⟨b, c, hb, hba, hc, hcb⟩
      exact hmarked.mp ⟨b, hb, hba, (second b hb hba).mp ⟨c, hc, hcb⟩⟩
    · intro h
      obtain ⟨b, hb, hba, hqb⟩ := hmarked.mpr h
      obtain ⟨c, hc, hcb⟩ := (second b hb hba).mpr hqb
      exact ⟨b, c, hb, hba, hc, hcb⟩

end
end Mettapedia.GraphTheory.FourColor.ThreeTwoFaceTransfer
