import Mettapedia.GraphTheory.FourColor.FaceAttachmentBoundary
import Mettapedia.GraphTheory.FourColor.FaceRegionMissingColour

/-!
# The degree word of an actual facial attachment

An attachment arc has retained degree two at each end and degree three
at every internal vertex. The degrees are computed on the original
incidence and transported to the actual old boundary permutation.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceAttachmentDegrees

open Equiv Equiv.Perm
open GoertzelV24FaceOrbitIncidence GoertzelV24TwoEdgeCutMinimality
open PhysicalForkCodeFaces PhysicalForkCodeCut
open SimpleGraphDartRotation FaceRegionDegree EdgeShoreRotation
open FaceRegionShelling FaceAttachmentCount FaceAttachmentArc
open FaceAttachmentBoundary PermutationSingleExitArc PlanePatchCurvature

noncomputable section
attribute [local instance] Classical.propDecidable

section Local

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable {RS : RotationSystem V E} {F : Finset (OrbitFace RS)}

/-- Two successive retained edges of an unselected face force the third
edge at their common vertex to be retained too. -/
theorem degree_three_of_retained_step (hC : Cubic3 RS) (hcubic : RS.IsCubic)
    (d : RS.D) (hd : RS.edgeOf d ∈ edges RS F)
    (hn : RS.edgeOf (RS.phi d) ∈ edges RS F)
    (hout : dartOrbitFace RS (RS.phi d) ∉ F) :
    ((RS.dartsAt (RS.vertOf (RS.phi d))).filter fun x => RS.edgeOf x ∈ edges RS F).card = 3 := by
  have ha : RS.edgeOf (RS.alpha d) ∈ edges RS F := by rwa [RS.edge_alpha]
  have hb : dartOrbitFace RS (RS.rho (RS.phi d)) ∈ F :=
    ((edge_mem_iff_sectors RS F (RS.phi d)).mp hn).resolve_left hout
  have ht : RS.edgeOf (RS.rho (RS.phi d)) ∈ edges RS F :=
    (edge_mem_iff RS F _).mpr (Or.inl hb)
  have hall : ∀ x ∈ RS.dartsAt (RS.vertOf (RS.phi d)), RS.edgeOf x ∈ edges RS F := by
    intro x hx
    have hv : RS.vertOf x = RS.vertOf (RS.alpha d) := by
      have he : RS.vertOf x = RS.vertOf (RS.phi d) := by
        simpa only [RotationSystem.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and] using hx
      exact he.trans (RS.vert_phi_eq_vert_alpha d)
    rcases hC.fiber (RS.alpha d) x hv with he | he | he
    · exact he ▸ ha
    · exact he ▸ hn
    · exact he ▸ ht
  rw [Finset.filter_eq_self.mpr hall]
  exact hcubic _

end Local

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G) {S R : Region data} (e : Event S R)
variable (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
variable (outer : Dart data.toRotationSystem (edges data.toRotationSystem S.faces))

local notation "RS" => data.toRotationSystem
local notation "Old" => toMap RS (edges RS S.faces) outer

include ambient

/-- Every internal attachment vertex has degree three in the old patch. -/
theorem internal_degree (a : Arc (RS).phi (attachmentDarts data e))
    (i : ℕ) (hi : 0 < i) (hil : i < a.length) :
    ((Old).dartsAt ((Old).vertOf (((Old).phi ^ i) (oldStart data e a)))).card = 3 := by
  rw [EdgeShoreRotation.degree_eq]
  change (((RS).dartsAt ((RS).vertOf (((Old).phi ^ i) (oldStart data e a)).val)).filter
    fun d => (RS).edgeOf d ∈ edges RS S.faces).card = 3
  rw [old_pow data e outer a i hil]
  have hs : (RS).phi (((RS).phi ^ (i - 1)) a.first) = ((RS).phi ^ i) a.first := by
    rw [← Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel hi]
  have hd := (mem_attachmentDarts data e _).mp (a.mem (show i - 1 < a.length by omega))
  have hn := (mem_attachmentDarts data e _).mp (a.mem hil)
  rw [← hs]
  exact degree_three_of_retained_step
    (cubic3_of _ ambient.spherical.cubic ambient.vertexRotationCyclic) ambient.spherical.cubic _
    (Finset.mem_inter.mp hd.2).1 (hs.symm ▸ (Finset.mem_inter.mp hn.2).1)
    (by rw [hs, hn.1]; exact e.fresh)

/-- At either end of an attachment, one incident edge is retained and
another is absent, so exactly two old incident edges remain. -/
theorem endpoint_degree (a : Arc (RS).phi (attachmentDarts data e))
    (i : ℕ) (hi : i = 0 ∨ i = a.length) :
    ((Old).dartsAt ((Old).vertOf (((Old).phi ^ i) (oldStart data e a)))).card = 2 := by
  have missing (d : (RS).D) (hf : d ∈ orbitFaceDarts RS e.face)
      (hd : d ∉ attachmentDarts data e) : (RS).edgeOf d ∉ edges RS S.faces := by
    intro hm
    apply hd
    exact (mem_attachmentDarts data e d).mpr
      ⟨(mem_orbitFaceDarts_iff _ _ _).mp hf,
        Finset.mem_inter.mpr ⟨hm, Finset.mem_image.mpr ⟨d, hf, rfl⟩⟩⟩
  have hc := cubic3_of _ ambient.spherical.cubic ambient.vertexRotationCyclic
  have firstret := (Finset.mem_inter.mp ((mem_attachmentDarts data e _).mp a.first_mem).2).1
  rw [EdgeShoreRotation.degree_eq]
  change (((RS).dartsAt ((RS).vertOf (((Old).phi ^ i) (oldStart data e a)).val)).filter
    fun d => (RS).edgeOf d ∈ edges RS S.faces).card = 2
  rcases hi with rfl | rfl
  · simp only [pow_zero, Perm.one_apply]
    have hp : dartOrbitFace RS ((RS).phi.symm a.first) = e.face := by
      have hh := dartOrbitFace_phi_eq RS ((RS).phi.symm a.first)
      rw [(RS).phi.apply_symm_apply] at hh
      exact hh.symm.trans ((mem_attachmentDarts data e _).mp a.first_mem).1
    have hm := missing ((RS).phi.symm a.first) ((mem_orbitFaceDarts_iff _ _ _).mpr hp) a.before_outside
    have hv : (RS).vertOf a.first = (RS).vertOf ((RS).alpha ((RS).phi.symm a.first)) := by
      simpa only [(RS).phi.apply_symm_apply] using (RS).vert_phi_eq_vert_alpha ((RS).phi.symm a.first)
    rw [← FaceRegionMissingColour.incident_card]
    apply FaceRegionMissingColour.incident_card_two hc ambient.spherical.cubic
      (mem_touched.mpr ⟨a.first, rfl, firstret⟩) hm
    exact (RS).mem_endpoints_iff.mpr ⟨(RS).alpha ((RS).phi.symm a.first),
      (RS).mem_dartsOn.mpr ((RS).edge_alpha _), hv.symm⟩
  · rw [old_after_vertex data e outer a]
    have hm := missing _ (arc_pow_in_face data e a a.length) a.after_outside
    have hlast := (Finset.mem_inter.mp ((mem_attachmentDarts data e _).mp a.last_mem).2).1
    have hv : (RS).vertOf (((RS).phi ^ a.length) a.first) =
        (RS).vertOf ((RS).alpha (((RS).phi ^ (a.length - 1)) a.first)) := by
      rw [← a.last_next]
      exact (RS).vert_phi_eq_vert_alpha _
    rw [← FaceRegionMissingColour.incident_card]
    apply FaceRegionMissingColour.incident_card_two hc ambient.spherical.cubic
      (hv ▸ alpha_touched hlast) hm
    exact (RS).mem_endpoints_iff.mpr ⟨_, (RS).mem_dartsOn.mpr rfl, rfl⟩

/-- The complete ordered degree word is `2, 3, ..., 3, 2`, read in the
actual old boundary permutation. -/
theorem degree_word (a : Arc (RS).phi (attachmentDarts data e))
    (i : Fin (a.length + 1)) :
    ((Old).dartsAt ((Old).vertOf (((Old).phi ^ i.val) (oldStart data e a)))).card =
      if i.val = 0 ∨ i.val = a.length then 2 else 3 := by
  split_ifs with hi
  · exact endpoint_degree data e ambient outer a i.val hi
  · exact internal_degree data e ambient outer a i.val (by omega) (by omega)

end
end Mettapedia.GraphTheory.FourColor.FaceAttachmentDegrees
