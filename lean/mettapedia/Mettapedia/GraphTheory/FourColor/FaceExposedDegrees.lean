import Mettapedia.GraphTheory.FourColor.FaceContourExtension

/-!
# The new boundary degree word and loss of alternation

The newly exposed path has degree three at both ends and degree two at
every internal vertex in the new retained map. In particular, a step with
at least three new edges cannot leave an alternating boundary. Safe
colouring extension therefore does not preserve that proposed invariant.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceExposedDegrees

open Equiv Equiv.Perm
open GoertzelV24FaceOrbitIncidence GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation FaceRegionDegree EdgeShoreRotation
open PlanePatchCurvature FaceRegionShelling FaceRegionComplement
open FaceAttachmentArc FaceExposedBoundary FaceExposedPath FaceExposedEndpoints
open PhysicalForkCodeCut PhysicalForkCodeFaces PermutationSingleExitArc
open FaceRegionMissingColour FaceContourExtension GoertzelV24ForkInterfaceSupport

noncomputable section
attribute [local instance] Classical.propDecidable
set_option autoImplicit false

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G) {S R : Region data} (e : Event S R)
variable (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)


include ambient e

/-- At a genuinely new vertex only the added face supplies a selected
sector. Facial simplicity prevents two occurrences of that sector. -/
theorem degree_two_at_new_vertex {v : V}
    (hv : v ∈ touched (data.toRotationSystem) (edges (data.toRotationSystem) R.faces))
    (hold : v ∉ touched (data.toRotationSystem) (edges (data.toRotationSystem) S.faces)) :
    (((data.toRotationSystem).dartsAt v).filter fun d => (data.toRotationSystem).edgeOf d ∈ edges (data.toRotationSystem) R.faces).card = 2 := by
  have only (d : (data.toRotationSystem).D) (hd : (data.toRotationSystem).vertOf d = v)
      (hf : dartOrbitFace (data.toRotationSystem) d ∈ R.faces) : dartOrbitFace (data.toRotationSystem) d = e.face := by
    rw [e.target, Finset.mem_insert] at hf
    exact hf.resolve_right (fun hh => hold ((touched_iff (data.toRotationSystem) S.faces v).mpr ⟨d, hd, hh⟩))
  obtain ⟨d, hd, hf⟩ := (touched_iff (data.toRotationSystem) R.faces v).mp hv
  have hdf := only d hd hf
  have hs : sectors (data.toRotationSystem) R.faces v = {d} := by
    ext x
    simp only [sectors, Finset.mem_filter, RotationSystem.dartsAt,
      Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, hxf⟩
      exact face_vertex_injective data ambient e.face
        ((mem_orbitFaceDarts_iff _ _ _).mpr (only x hx hxf))
        ((mem_orbitFaceDarts_iff _ _ _).mpr hdf) (hx.trans hd.symm)
    · rintro rfl
      exact ⟨hd, hf⟩
  rw [← hd, retained_degree_formula
    (cubic3_of _ ambient.spherical.cubic ambient.vertexRotationCyclic) d, hd, hs]
  simp

/-- An old degree-two vertex gains its missing incident edge at each
attachment end. This uses the actual edge sets of the event. -/
theorem degree_three_at_old_new_edge {v : V}
    (hv : v ∈ touched (data.toRotationSystem) (edges (data.toRotationSystem) S.faces)) {x : G.edgeSet}
    (hx : x ∈ exposedEdges data e) (hvx : v ∈ (data.toRotationSystem).endpoints x) :
    (((data.toRotationSystem).dartsAt v).filter fun d => (data.toRotationSystem).edgeOf d ∈ edges (data.toRotationSystem) R.faces).card = 3 := by
  have hC := cubic3_of _ ambient.spherical.cubic ambient.vertexRotationCyclic
  have htwo := incident_card_two hC ambient.spherical.cubic hv (Finset.mem_sdiff.mp hx).2 hvx
  have hsub : (edges (data.toRotationSystem) S.faces).filter (fun y => v ∈ (data.toRotationSystem).endpoints y) ⊂
      (edges (data.toRotationSystem) R.faces).filter (fun y => v ∈ (data.toRotationSystem).endpoints y) := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨?_, ?_⟩
    · intro y hy
      obtain ⟨hys, hyv⟩ := Finset.mem_filter.mp hy
      refine Finset.mem_filter.mpr ⟨?_, hyv⟩
      rw [FaceRegionStepBoundary.event_retained_edges data e]
      exact Finset.mem_union_left _ hys
    · intro he
      have hm : x ∈ (edges (data.toRotationSystem) R.faces).filter (fun y => v ∈ (data.toRotationSystem).endpoints y) :=
        Finset.mem_filter.mpr ⟨exposed_mem_new data e hx, hvx⟩
      rw [← he] at hm
      exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_filter.mp hm).1
  have hlt := Finset.card_lt_card hsub
  simp only [incident_card (data.toRotationSystem)] at htwo hlt
  have hle := Finset.card_le_card (Finset.filter_subset
    (fun d => (data.toRotationSystem).edgeOf d ∈ edges (data.toRotationSystem) R.faces) ((data.toRotationSystem).dartsAt v))
  rw [ambient.spherical.cubic v] at hle
  omega

variable (outer : Dart (data.toRotationSystem) (edges (data.toRotationSystem) R.faces))
variable (ho : dartOrbitFace (data.toRotationSystem) outer.val ∉ R.faces)
variable (b : Arc (toMap (data.toRotationSystem) (edges (data.toRotationSystem) R.faces) outer).phi (exposedDarts data e outer))

local notation "New" => toMap (data.toRotationSystem) (edges (data.toRotationSystem) R.faces) outer

include ho

theorem internal_degree (i : ℕ) (hi : 0 < i) (hil : i < b.length) :
    ((New).dartsAt ((New).vertOf (((New).phi ^ i) b.first))).card = 2 := by
  let p := path data e outer ambient ho b
  let j : Fin (b.length + 1) := ⟨i, by omega⟩
  have hn : p.vertex j ∉ touched (data.toRotationSystem) (edges (data.toRotationSystem) S.faces) := by
    intro hh
    have hh' := (vertex_old_iff data e ambient outer ho b j).mp hh
    dsimp [j] at hh'
    omega
  rw [EdgeShoreRotation.degree_eq]
  exact degree_two_at_new_vertex data e ambient
    ((New).vertOf (((New).phi ^ i) b.first)).property hn

theorem endpoint_degree (i : ℕ) (hi : i = 0 ∨ i = b.length) :
    ((New).dartsAt ((New).vertOf (((New).phi ^ i) b.first))).card = 3 := by
  let p := path data e outer ambient ho b
  rw [EdgeShoreRotation.degree_eq]
  rcases hi with rfl | rfl
  · exact degree_three_at_old_new_edge data e ambient
      (first_old data e ambient outer ho b) p.firstEdge_mem p.firstEdge_incident
  · exact degree_three_at_old_new_edge data e ambient
      (last_old data e ambient outer ho b) p.lastEdge_mem p.lastEdge_incident

/-- The replacement word is `3, 2, ..., 2, 3` in the actual new boundary. -/
theorem degree_word (i : Fin (b.length + 1)) :
    ((New).dartsAt ((New).vertOf (((New).phi ^ i.val) b.first))).card =
      if i.val = 0 ∨ i.val = b.length then 3 else 2 := by
  split_ifs with hi
  · exact endpoint_degree data e ambient outer ho b i.val hi
  · exact internal_degree data e ambient outer ho b i.val (by omega) (by omega)

omit b in
/-- Every step in the unconditional path-extension range creates two
consecutive degree-two boundary vertices. Thus its new contour does not
alternate, even when the old contour did. -/
theorem not_alternating_of_three_le_exposed (hlen : 3 ≤ (exposedEdges data e).card) :
    ¬ BoundaryAlternates New := by
  obtain ⟨b⟩ := exists_exposed_arc data e outer ambient ho
  have hb : 3 ≤ b.length := by
    rw [b.length_eq_card, exposed_darts_card data e outer ambient ho]
    exact hlen
  intro ha
  have h1 := internal_degree data e ambient outer ho b 1 (by omega) (by omega)
  have h2 := internal_degree data e ambient outer ho b 2 (by omega) (by omega)
  have hd := power_on_outer data e outer b 1
  have hh := ha (((New).phi ^ 1) b.first) hd
  apply hh
  rw [h1]
  have he : (New).phi (((New).phi ^ 1) b.first) = ((New).phi ^ 2) b.first := by
    rw [← Perm.mul_apply, ← pow_succ']
  rw [he, h2]

omit b in
/-- Alternation makes every sufficiently long face addition colourable,
but the resulting boundary is necessarily nonalternating. -/
theorem not_alternating_after_alternates
    (oldOuter : Dart data.toRotationSystem (edges data.toRotationSystem S.faces))
    (hold : dartOrbitFace data.toRotationSystem oldOuter.val ∉ S.faces)
    (ha : BoundaryAlternates
      (toMap data.toRotationSystem (edges data.toRotationSystem S.faces) oldOuter))
    (hface : 5 ≤ (orbitFaceDarts data.toRotationSystem e.face).card) :
    ¬ BoundaryAlternates New :=
  not_alternating_of_three_le_exposed data e ambient outer ho
    (three_le_exposed_of_no_run data e ambient oldOuter hold 2
      (no_two_run_of_alternates ha) hface)

omit b in
/-- A hexagonal addition from an alternating contour creates a run of
two degree-three vertices as well. The weaker no-run condition therefore
also fails to propagate through every single-face step. -/
theorem hexagon_creates_two_run
    (oldOuter : Dart data.toRotationSystem (edges data.toRotationSystem S.faces))
    (hold : dartOrbitFace data.toRotationSystem oldOuter.val ∉ S.faces)
    (ha : BoundaryAlternates
      (toMap data.toRotationSystem (edges data.toRotationSystem S.faces) oldOuter))
    (hface : (orbitFaceDarts data.toRotationSystem e.face).card = 6) :
    HasThreeRun New 2 := by
  have hp := FaceRegionPatch.patch data R.faces ambient outer ho R.inside R.outside
  have hpOld := FaceRegionPatch.patch data S.faces ambient oldOuter hold S.inside S.outside
  have hcOld := hpOld.curvature_eq_six_of_alternates ha
  have hbalance := FaceRegionStepBoundary.event_degree_imbalance
    (ambient := ambient) (e := e) (inner := oldOuter) (hi := hold) (outer := outer) (ho := ho)
  have hnew := hp.curvature_eq
  have holdEq := hpOld.curvature_eq
  have hc : curvature New = 6 := by
    rw [hface] at hbalance
    dsimp at hbalance
    omega
  by_contra hn
  exact not_alternating_after_alternates data e ambient outer ho oldOuter hold ha (by omega)
    (alternates_of_no_two_run_of_curvature_six hp hc hn)

omit b ho e in
/-- An alternating contour has a genuine colour-preserving successor
toward any larger target with faces of length at least five. Its new
contour and loss of alternation are both derived from that event. -/
theorem exists_coloured_non_alternating_event_between
    (oldOuter : Dart data.toRotationSystem (edges data.toRotationSystem S.faces))
    (hold : dartOrbitFace data.toRotationSystem oldOuter.val ∉ S.faces)
    (ha : BoundaryAlternates
      (toMap data.toRotationSystem (edges data.toRotationSystem S.faces) oldOuter))
    (T : Region data) (hST : S.faces ⊂ T.faces)
    (hfaces : ∀ f ∈ T.faces \ S.faces,
      5 ≤ (orbitFaceDarts data.toRotationSystem f).card)
    (a : G.edgeSet → Fin 3)
    (hproper : Proper data.toRotationSystem.endpoints (edges data.toRotationSystem S.faces) a) :
    ∃ U : Region data, ∃ _ : Event S U,
      U.faces ⊆ T.faces ∧ U.faces.card = S.faces.card + 1 ∧
        ∃ oU : Dart data.toRotationSystem (edges data.toRotationSystem U.faces),
          dartOrbitFace data.toRotationSystem oU.val ∉ U.faces ∧
          ¬ BoundaryAlternates (toMap data.toRotationSystem (edges data.toRotationSystem U.faces) oU) ∧
          ∃ c : G.edgeSet → Fin 3,
            Proper data.toRotationSystem.endpoints (edges data.toRotationSystem U.faces) c ∧
              ∀ x ∈ edges data.toRotationSystem S.faces, c x = a x := by
  obtain ⟨U, e, hUT, hc, c, hp, he⟩ := exists_coloured_event_between data ambient oldOuter hold
    T hST 2 (no_two_run_of_alternates ha) hfaces a hproper
  obtain ⟨oU, hoU, _, _⟩ := Region.realizes ambient U
  have hf : e.face ∈ T.faces \ S.faces := by
    refine Finset.mem_sdiff.mpr ⟨hUT ?_, e.fresh⟩
    rw [e.target]
    exact Finset.mem_insert_self _ _
  exact ⟨U, e, hUT, hc, oU, hoU,
    not_alternating_after_alternates data e ambient oU hoU oldOuter hold ha (hfaces e.face hf),
    c, hp, he⟩

end
end Mettapedia.GraphTheory.FourColor.FaceExposedDegrees
