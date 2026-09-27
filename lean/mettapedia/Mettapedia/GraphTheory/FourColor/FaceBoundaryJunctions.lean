import Mettapedia.GraphTheory.FourColor.FaceBoundarySplice

/-!
# The two exact junctions of a facial boundary splice

The predecessor of the removed arc is followed by the first newly exposed
dart. The new arc then rejoins the unchanged old boundary immediately after
the removed arc. Together with the surviving-successor theorem and exact
boundary partition, these equations specify the entire ordered replacement.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceBoundaryJunctions

open Equiv Equiv.Perm
open GoertzelV24FaceOrbitIncidence GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation FaceRegionDegree EdgeShoreRotation
open PlanePatchCurvature FaceRegionShelling FaceRegionBoundary FaceRegionPatch
open FaceAttachmentArc FaceAttachmentBoundary FaceExposedBoundary FaceBoundarySplice
open PhysicalForkCodeFaces PermutationSingleExitArc

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G)
variable {S R : Region data} (e : Event S R)
variable (oldOuter : Dart data.toRotationSystem (edges data.toRotationSystem S.faces))
variable (newOuter : Dart data.toRotationSystem (edges data.toRotationSystem R.faces))

local notation "Old" => toMap data.toRotationSystem (edges data.toRotationSystem S.faces) oldOuter
local notation "New" => toMap data.toRotationSystem (edges data.toRotationSystem R.faces) newOuter

theorem old_not_exposed (d : Dart data.toRotationSystem (edges data.toRotationSystem S.faces)) :
    oldIntoNew data e d ∉ exposedDarts data e newOuter := by
  intro h
  exact (Finset.mem_sdiff.mp ((mem_exposedDarts data e newOuter _).mp h).2).2 d.property

variable (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
variable (hold : dartOrbitFace data.toRotationSystem oldOuter.val ∉ S.faces)
variable (hnew : dartOrbitFace data.toRotationSystem newOuter.val ∉ R.faces)

include ambient hold hnew

theorem step_into_attachment (d : (Old).D) (hd : d ∈ outerDarts Old)
    (hkeep : d ∉ oldAttachmentDarts data e)
    (hnext : (Old).phi d ∈ oldAttachmentDarts data e) :
    (New).phi (oldIntoNew data e d) ∈ exposedDarts data e newOuter := by
  have hdnew := (old_outer_survives_iff data e ambient oldOuter newOuter hold hnew d hd).mpr hkeep
  have hn : (New).phi (oldIntoNew data e d) ∈ outerDarts New := (outer_phi_iff (RS := New) _).mpr hdnew
  apply (exposed_iff_new_edge data e newOuter _ hn).mpr
  intro he
  let x : (Old).D := ⟨((New).phi (oldIntoNew data e d)).val, he⟩
  have hout := (mem_outerDarts_iff data R.faces ambient newOuter hnew R.inside R.outside _).mp hn
  have hxout : dartOrbitFace data.toRotationSystem x.val ∉ S.faces := fun h => hout (e.subset h)
  have htout := outer_dart_outside oldOuter hold ((outer_phi_iff (RS := Old) d).mpr hd)
  have hv : data.toRotationSystem.vertOf x.val =
      data.toRotationSystem.vertOf ((Old).phi d).val :=
    (congrArg (fun v : Vertex data.toRotationSystem (edges data.toRotationSystem R.faces) => v.val)
      ((New).vert_phi_eq_vert_alpha (oldIntoNew data e d))).trans
      (congrArg (fun v : Vertex data.toRotationSystem (edges data.toRotationSystem S.faces) => v.val)
        ((Old).vert_phi_eq_vert_alpha d)).symm
  have hx := outside_vertex_injective (RS := data.toRotationSystem) (R := S.faces)
    (cubic3_of _ ambient.spherical.cubic ambient.vertexRotationCyclic) x ((Old).phi d) hxout htout hv
  have hf := (old_attachment_iff_face data e ((Old).phi d)).mp hnext
  have hxf : dartOrbitFace data.toRotationSystem x.val = e.face := by rw [hx]; exact hf
  apply hout
  change dartOrbitFace data.toRotationSystem x.val ∈ R.faces
  rw [hxf, e.target]
  exact Finset.mem_insert_self _ _

theorem step_out_of_attachment (d : (Old).D) (hd : d ∈ outerDarts Old)
    (hkeep : d ∉ oldAttachmentDarts data e)
    (hprev : (Old).phi.symm d ∈ oldAttachmentDarts data e) :
    (New).phi.symm (oldIntoNew data e d) ∈ exposedDarts data e newOuter := by
  have hdnew := (old_outer_survives_iff data e ambient oldOuter newOuter hold hnew d hd).mpr hkeep
  have hp : (New).phi.symm (oldIntoNew data e d) ∈ outerDarts New := by
    apply (outer_phi_iff (RS := New) _).mp
    simpa only [(New).phi.apply_symm_apply] using hdnew
  apply (exposed_iff_new_edge data e newOuter _ hp).mpr
  intro he
  let x : (Old).D := ⟨((New).phi.symm (oldIntoNew data e d)).val, he⟩
  have hout := (mem_outerDarts_iff data R.faces ambient newOuter hnew R.inside R.outside _).mp hp
  have hxout : dartOrbitFace data.toRotationSystem x.val ∉ S.faces := fun h => hout (e.subset h)
  have hx : x ∈ outerDarts Old :=
    (mem_outerDarts_iff data S.faces ambient oldOuter hold S.inside S.outside x).mpr hxout
  have hnout := outer_dart_outside oldOuter hold ((outer_phi_iff (RS := Old) x).mpr hx)
  have hdout := outer_dart_outside oldOuter hold hd
  have hnewv := congrArg
    (fun v : Vertex data.toRotationSystem (edges data.toRotationSystem R.faces) => v.val)
    ((New).vert_phi_eq_vert_alpha ((New).phi.symm (oldIntoNew data e d)))
  rw [(New).phi.apply_symm_apply] at hnewv
  have hv : data.toRotationSystem.vertOf ((Old).phi x).val = data.toRotationSystem.vertOf d.val :=
    (congrArg (fun v : Vertex data.toRotationSystem (edges data.toRotationSystem S.faces) => v.val)
      ((Old).vert_phi_eq_vert_alpha x)).trans hnewv.symm
  have hn := outside_vertex_injective (RS := data.toRotationSystem) (R := S.faces)
    (cubic3_of _ ambient.spherical.cubic ambient.vertexRotationCyclic) ((Old).phi x) d hnout hdout hv
  have hxe : x = (Old).phi.symm d := by
    apply (Old).phi.injective
    simpa only [(Old).phi.apply_symm_apply] using hn
  have hxa : x ∈ oldAttachmentDarts data e := hxe.symm ▸ hprev
  have hxf := (old_attachment_iff_face data e x).mp hxa
  apply hout
  change dartOrbitFace data.toRotationSystem x.val ∈ R.faces
  rw [hxf, e.target]
  exact Finset.mem_insert_self _ _

/-- The two starts are joined to the same surviving predecessor. -/
theorem first_junction (a : Arc (Old).phi (oldAttachmentDarts data e))
    (b : Arc (New).phi (exposedDarts data e newOuter)) :
    b.first = (New).phi (oldIntoNew data e ((Old).phi.symm a.first)) := by
  have hfirst := old_attachment_on_outer data e oldOuter ambient hold a.first_mem
  have hpred : (Old).phi.symm a.first ∈ outerDarts Old := by
    apply (outer_phi_iff (RS := Old) _).mp
    simpa only [(Old).phi.apply_symm_apply] using hfirst
  have hn := step_into_attachment data e oldOuter newOuter ambient hold hnew
    ((Old).phi.symm a.first) hpred a.before_outside (by
      simpa only [(Old).phi.apply_symm_apply] using a.first_mem)
  apply (b.entry_eq_first hn ?_).symm
  simpa only [(New).phi.symm_apply_apply] using
    old_not_exposed data e newOuter ((Old).phi.symm a.first)

/-- After traversing the new arc, the new boundary rejoins precisely the
old dart immediately after the removed arc. -/
theorem last_junction (a : Arc (Old).phi (oldAttachmentDarts data e))
    (b : Arc (New).phi (exposedDarts data e newOuter)) :
    ((New).phi ^ b.length) b.first = oldIntoNew data e (((Old).phi ^ a.length) a.first) := by
  have hlast := old_attachment_on_outer data e oldOuter ambient hold a.last_mem
  have hafter : ((Old).phi ^ a.length) a.first ∈ outerDarts Old := by
    rw [← a.last_next]
    exact (outer_phi_iff (RS := Old) _).mpr hlast
  have hprev : (Old).phi.symm (((Old).phi ^ a.length) a.first) ∈ oldAttachmentDarts data e := by
    rw [← a.last_next, (Old).phi.symm_apply_apply]
    exact a.last_mem
  have hn := step_out_of_attachment data e oldOuter newOuter ambient hold hnew
    (((Old).phi ^ a.length) a.first) hafter a.after_outside hprev
  have he := b.exit_eq_last hn (by
    simpa only [(New).phi.apply_symm_apply] using
      old_not_exposed data e newOuter (((Old).phi ^ a.length) a.first))
  have hh := congrArg (New).phi he
  rw [(New).phi.apply_symm_apply, b.last_next] at hh
  exact hh.symm

omit hold hnew in
/-- Every actual facial construction supplies both boundary arcs and the
two exact splice junctions. The outer darts and all interval data are
constructed from the source map and event. -/
theorem exists_splice :
    ∃ oS : Dart data.toRotationSystem (edges data.toRotationSystem S.faces),
      ∃ oR : Dart data.toRotationSystem (edges data.toRotationSystem R.faces),
        dartOrbitFace data.toRotationSystem oS.val ∉ S.faces ∧
        dartOrbitFace data.toRotationSystem oR.val ∉ R.faces ∧
        ∃ a : Arc (toMap data.toRotationSystem (edges data.toRotationSystem S.faces) oS).phi
            (oldAttachmentDarts data e),
          ∃ b : Arc (toMap data.toRotationSystem (edges data.toRotationSystem R.faces) oR).phi
              (exposedDarts data e oR),
            b.first = (toMap data.toRotationSystem (edges data.toRotationSystem R.faces) oR).phi
              (oldIntoNew data e
                ((toMap data.toRotationSystem (edges data.toRotationSystem S.faces) oS).phi.symm a.first)) ∧
            ((toMap data.toRotationSystem (edges data.toRotationSystem R.faces) oR).phi ^ b.length) b.first =
              oldIntoNew data e
                (((toMap data.toRotationSystem (edges data.toRotationSystem S.faces) oS).phi ^ a.length) a.first) := by
  obtain ⟨oS, hS, _, _⟩ := Region.realizes ambient S
  obtain ⟨oR, hR, _, _⟩ := Region.realizes ambient R
  obtain ⟨aF⟩ := exists_attachment_arc data ambient e
  let a := oldArc data e oS ambient aF
  obtain ⟨b⟩ := exists_exposed_arc data e oR ambient hR
  exact ⟨oS, oR, hS, hR, a, b,
    first_junction data e oS oR ambient hS hR a b,
    last_junction data e oS oR ambient hS hR a b⟩

end
end Mettapedia.GraphTheory.FourColor.FaceBoundaryJunctions
