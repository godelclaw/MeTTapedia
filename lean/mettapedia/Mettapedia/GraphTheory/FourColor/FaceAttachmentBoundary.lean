import Mettapedia.GraphTheory.FourColor.FaceAttachmentArc

/-!
# Agreement of facial attachment order and the old boundary order

The literal attachment arc on the added face lifts to an arc on the old
retained-edge map. Every dart and every interior successor agrees under
the subtype projection. Both adjacent darts lie outside the attachment.
When the map's chosen outer dart is exterior, this is an arc of its actual
outer facial boundary.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceAttachmentBoundary

open Equiv Equiv.Perm
open GoertzelV24FaceOrbitIncidence GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation FaceRegionDegree EdgeShoreRotation
open PlanePatchCurvature FaceRegionShelling FaceAttachmentCount FaceAttachmentArc
open FaceRegionPatch PermutationSingleExitArc

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G)
variable {S R : Region data} (e : Event S R)

def oldAttachmentDarts : Finset (Dart data.toRotationSystem (edges data.toRotationSystem S.faces)) :=
  Finset.univ.filter fun d => d.val ∈ attachmentDarts data e

theorem mem_oldAttachmentDarts (d : Dart data.toRotationSystem (edges data.toRotationSystem S.faces)) :
    d ∈ oldAttachmentDarts data e ↔ d.val ∈ attachmentDarts data e := by
  simp only [oldAttachmentDarts, Finset.mem_filter, Finset.mem_univ, true_and]

def oldStart (a : Arc data.toRotationSystem.phi (attachmentDarts data e)) :
    Dart data.toRotationSystem (edges data.toRotationSystem S.faces) :=
  ⟨a.first, (Finset.mem_inter.mp ((mem_attachmentDarts data e a.first).mp a.first_mem).2).1⟩

variable (outer : Dart data.toRotationSystem (edges data.toRotationSystem S.faces))

/-- First-return restriction makes no change to an interior attachment step. -/
theorem old_pow (a : Arc data.toRotationSystem.phi (attachmentDarts data e))
    (i : ℕ) (hi : i < a.length) :
    (((toMap data.toRotationSystem (edges data.toRotationSystem S.faces) outer).phi ^ i)
      (oldStart data e a)).val = (data.toRotationSystem.phi ^ i) a.first := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hip : i < a.length := by omega
    rw [pow_succ', Perm.mul_apply, phi_step, ih hip, pow_succ', Perm.mul_apply]
    rw [ih hip]
    have hh := ((mem_attachmentDarts data e _).mp (a.mem hi)).2
    rw [pow_succ', Perm.mul_apply] at hh
    exact (Finset.mem_inter.mp hh).1

theorem arc_pow_in_face (a : Arc data.toRotationSystem.phi (attachmentDarts data e)) (i : ℕ) :
    (data.toRotationSystem.phi ^ i) a.first ∈ orbitFaceDarts data.toRotationSystem e.face := by
  apply (mem_orbitFaceDarts_iff _ _ _).mpr
  induction i with
  | zero => exact ((mem_attachmentDarts data e a.first).mp a.first_mem).1
  | succ i ih =>
    rw [pow_succ', Perm.mul_apply, dartOrbitFace_phi_eq]
    exact ih

/-- The first dart after the attachment starts at the same original vertex
in the old boundary and in the added face, even though the dart can differ. -/
theorem old_after_vertex (a : Arc data.toRotationSystem.phi (attachmentDarts data e)) :
    data.toRotationSystem.vertOf
        ((((toMap data.toRotationSystem (edges data.toRotationSystem S.faces) outer).phi ^ a.length)
          (oldStart data e a)).val) =
      data.toRotationSystem.vertOf ((data.toRotationSystem.phi ^ a.length) a.first) := by
  let T := toMap data.toRotationSystem (edges data.toRotationSystem S.faces) outer
  have hn : a.length - 1 + 1 = a.length := by have := a.positive; omega
  have hi : a.length - 1 < a.length := by have := a.positive; omega
  have hs := congrArg Subtype.val
    (T.vert_phi_eq_vert_alpha ((T.phi ^ (a.length - 1)) (oldStart data e a)))
  change data.toRotationSystem.vertOf
      (T.phi ((T.phi ^ (a.length - 1)) (oldStart data e a))).val =
    data.toRotationSystem.vertOf
      (data.toRotationSystem.alpha (((T.phi ^ (a.length - 1)) (oldStart data e a)).val)) at hs
  rw [← Perm.mul_apply, ← pow_succ', hn, old_pow data e outer a _ hi] at hs
  have ht := data.toRotationSystem.vert_phi_eq_vert_alpha
    ((data.toRotationSystem.phi ^ (a.length - 1)) a.first)
  rw [← Perm.mul_apply, ← pow_succ', hn] at ht
  exact hs.trans ht.symm

variable (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)

include ambient

theorem old_after_outside (a : Arc data.toRotationSystem.phi (attachmentDarts data e)) :
    (((toMap data.toRotationSystem (edges data.toRotationSystem S.faces) outer).phi ^ a.length)
      (oldStart data e a)) ∉ oldAttachmentDarts data e := by
  intro hm
  have hd := (mem_oldAttachmentDarts data e _).mp hm
  have hf := (mem_orbitFaceDarts_iff _ _ _).mpr ((mem_attachmentDarts data e _).mp hd).1
  have heq := face_vertex_injective data ambient e.face hf (arc_pow_in_face data e a a.length)
    (old_after_vertex data e outer a)
  exact a.after_outside (heq ▸ hd)

/-- The same attachment arc in the actual old map's face permutation. -/
def oldArc (a : Arc data.toRotationSystem.phi (attachmentDarts data e)) :
    Arc (toMap data.toRotationSystem (edges data.toRotationSystem S.faces) outer).phi
      (oldAttachmentDarts data e) where
  first := oldStart data e a
  length := a.length
  positive := a.positive
  exact := by
    ext d
    constructor
    · intro hd
      have hm := (mem_oldAttachmentDarts data e d).mp hd
      have him := (congrArg (fun B : Finset data.toRotationSystem.D => d.val ∈ B) a.exact).mp hm
      obtain ⟨i, hi, hid⟩ := Finset.mem_image.mp him
      exact Finset.mem_image.mpr ⟨i, hi, Subtype.ext
        ((old_pow data e outer a i (Finset.mem_range.mp hi)).trans hid)⟩
    · intro hd
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
      apply (mem_oldAttachmentDarts data e _).mpr
      rw [old_pow data e outer a i (Finset.mem_range.mp hi)]
      exact a.mem (Finset.mem_range.mp hi)
  injective := by
    intro i j hij
    apply a.injective
    have hh := congrArg Subtype.val hij
    rw [old_pow data e outer a i.val i.isLt, old_pow data e outer a j.val j.isLt] at hh
    exact hh
  after_outside := old_after_outside data e outer ambient a

theorem oldArc_agrees (a : Arc data.toRotationSystem.phi (attachmentDarts data e))
    (i : ℕ) (hi : i < a.length) :
    (((toMap data.toRotationSystem (edges data.toRotationSystem S.faces) outer).phi ^ i)
      (oldArc data e outer ambient a).first).val = (data.toRotationSystem.phi ^ i) a.first :=
  old_pow data e outer a i hi

/-- All darts of this interval belong to the old map's outer boundary. -/
theorem old_attachment_on_outer
    (ho : dartOrbitFace data.toRotationSystem outer.val ∉ S.faces) :
    oldAttachmentDarts data e ⊆
      outerDarts (toMap data.toRotationSystem (edges data.toRotationSystem S.faces) outer) := by
  intro d hd
  apply (mem_outerDarts_iff data S.faces ambient outer ho S.inside S.outside d).mpr
  rw [((mem_attachmentDarts data e d.val).mp ((mem_oldAttachmentDarts data e d).mp hd)).1]
  exact e.fresh

/-- An actual facial construction supplies both ordered arcs and their
pointwise agreement. No interval or ordering witness is an input. -/
theorem exists_ordered_attachment :
    ∃ a : Arc data.toRotationSystem.phi (attachmentDarts data e),
      ∃ b : Arc (toMap data.toRotationSystem (edges data.toRotationSystem S.faces) outer).phi
          (oldAttachmentDarts data e),
        b.length = a.length ∧ ∀ i < a.length,
          (((toMap data.toRotationSystem (edges data.toRotationSystem S.faces) outer).phi ^ i)
            b.first).val = (data.toRotationSystem.phi ^ i) a.first := by
  obtain ⟨a⟩ := exists_attachment_arc data ambient e
  exact ⟨a, oldArc data e outer ambient a, rfl, oldArc_agrees data e outer ambient a⟩

end
end Mettapedia.GraphTheory.FourColor.FaceAttachmentBoundary
