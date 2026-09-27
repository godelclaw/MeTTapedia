import Mettapedia.GraphTheory.FourColor.FaceExposedBoundary

/-!
# Literal boundary replacement in a facial construction

Old darts embed in the new map by their unchanged original identifiers.
An old outer dart remains outer exactly when it is outside the attachment
arc. The new outer boundary consists exactly of these surviving darts and
the newly exposed arc. Successor steps between surviving darts are
unchanged. These are statements about the actual boundary permutations.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceBoundarySplice

open GoertzelV24FaceOrbitIncidence GoertzelV24TwoEdgeCutMinimality
open GoertzelV24FaceDualConnectedness
open SimpleGraphDartRotation FaceRegionDegree EdgeShoreRotation
open PlanePatchCurvature FaceRegionShelling FaceRegionComplement
open FaceRegionBoundary FaceRegionPatch FaceRegionStepBoundary
open FaceAttachmentArc FaceAttachmentBoundary FaceExposedBoundary
open PhysicalForkCodeFaces

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G)
variable {S R : Region data} (e : Event S R)

/-- The inclusion is literal on original darts, edges, and vertices. -/
def oldIntoNew (d : Dart data.toRotationSystem (edges data.toRotationSystem S.faces)) :
    Dart data.toRotationSystem (edges data.toRotationSystem R.faces) :=
  ⟨d.val, by
    rw [event_retained_edges data e]
    exact Finset.mem_union_left _ d.property⟩

theorem oldIntoNew_injective : Function.Injective (oldIntoNew data e) := by
  intro d x h
  exact Subtype.ext (congrArg
    (fun z : Dart data.toRotationSystem (edges data.toRotationSystem R.faces) => z.val) h)

theorem old_attachment_iff_face
    (d : Dart data.toRotationSystem (edges data.toRotationSystem S.faces)) :
    d ∈ oldAttachmentDarts data e ↔ dartOrbitFace data.toRotationSystem d.val = e.face := by
  rw [mem_oldAttachmentDarts, mem_attachmentDarts]
  refine ⟨And.left, fun hf => ⟨hf, ?_⟩⟩
  exact Finset.mem_inter.mpr ⟨d.property,
    hf ▸ edgeOf_mem_orbitFaceBoundary_dartOrbitFace data.toRotationSystem d.val⟩

variable (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
variable (oldOuter : Dart data.toRotationSystem (edges data.toRotationSystem S.faces))
variable (newOuter : Dart data.toRotationSystem (edges data.toRotationSystem R.faces))
variable (hold : dartOrbitFace data.toRotationSystem oldOuter.val ∉ S.faces)
variable (hnew : dartOrbitFace data.toRotationSystem newOuter.val ∉ R.faces)

include ambient hold hnew

/-- Exactly the old attachment darts cease to be outer darts. -/
theorem old_outer_survives_iff
    (d : Dart data.toRotationSystem (edges data.toRotationSystem S.faces))
    (hd : d ∈ outerDarts (toMap data.toRotationSystem (edges data.toRotationSystem S.faces) oldOuter)) :
    oldIntoNew data e d ∈
        outerDarts (toMap data.toRotationSystem (edges data.toRotationSystem R.faces) newOuter) ↔
      d ∉ oldAttachmentDarts data e := by
  rw [mem_outerDarts_iff data R.faces ambient newOuter hnew R.inside R.outside,
    old_attachment_iff_face]
  have hout := (mem_outerDarts_iff data S.faces ambient oldOuter hold S.inside S.outside d).mp hd
  change dartOrbitFace data.toRotationSystem d.val ∉ R.faces ↔ _
  simp only [e.target, Finset.mem_insert, hout, or_false]

/-- Away from the two attachment junctions, the old successor is literally
the new successor, after the carrier inclusion. -/
theorem surviving_step
    (d : Dart data.toRotationSystem (edges data.toRotationSystem S.faces))
    (hd : d ∈ outerDarts (toMap data.toRotationSystem (edges data.toRotationSystem S.faces) oldOuter))
    (hdkeep : d ∉ oldAttachmentDarts data e)
    (hnkeep : (toMap data.toRotationSystem (edges data.toRotationSystem S.faces) oldOuter).phi d ∉
      oldAttachmentDarts data e) :
    (toMap data.toRotationSystem (edges data.toRotationSystem R.faces) newOuter).phi
        (oldIntoNew data e d) =
      oldIntoNew data e
        ((toMap data.toRotationSystem (edges data.toRotationSystem S.faces) oldOuter).phi d) := by
  let T := toMap data.toRotationSystem (edges data.toRotationSystem S.faces) oldOuter
  let U := toMap data.toRotationSystem (edges data.toRotationSystem R.faces) newOuter
  have hdnew := (old_outer_survives_iff data e ambient oldOuter newOuter hold hnew d hd).mpr hdkeep
  have hnnew := (old_outer_survives_iff data e ambient oldOuter newOuter hold hnew
    (T.phi d) ((outer_phi_iff (RS := T) d).mpr hd)).mpr hnkeep
  apply outside_vertex_injective (RS := data.toRotationSystem) (R := R.faces)
    (cubic3_of _ ambient.spherical.cubic ambient.vertexRotationCyclic)
    (U.phi (oldIntoNew data e d)) (oldIntoNew data e (T.phi d))
  · exact (mem_outerDarts_iff data R.faces ambient newOuter hnew R.inside R.outside _).mp
      ((outer_phi_iff (RS := U) _).mpr hdnew)
  · exact (mem_outerDarts_iff data R.faces ambient newOuter hnew R.inside R.outside _).mp hnnew
  · have hu : data.toRotationSystem.vertOf (U.phi (oldIntoNew data e d)).val =
        data.toRotationSystem.vertOf (data.toRotationSystem.alpha d.val) :=
      congrArg (fun v : Vertex data.toRotationSystem (edges data.toRotationSystem R.faces) => v.val)
        (U.vert_phi_eq_vert_alpha (oldIntoNew data e d))
    have ht : data.toRotationSystem.vertOf (T.phi d).val =
        data.toRotationSystem.vertOf (data.toRotationSystem.alpha d.val) :=
      congrArg (fun v : Vertex data.toRotationSystem (edges data.toRotationSystem S.faces) => v.val)
        (T.vert_phi_eq_vert_alpha d)
    exact hu.trans ht.symm

omit ambient hold hnew

/-- A new outer dart is newly exposed exactly when its edge is new. -/
theorem exposed_iff_new_edge
    (d : Dart data.toRotationSystem (edges data.toRotationSystem R.faces))
    (hd : d ∈ outerDarts (toMap data.toRotationSystem (edges data.toRotationSystem R.faces) newOuter)) :
    d ∈ exposedDarts data e newOuter ↔
      data.toRotationSystem.edgeOf d.val ∉ edges data.toRotationSystem S.faces := by
  rw [mem_exposedDarts]
  constructor
  · intro h
    exact (Finset.mem_sdiff.mp h.2).2
  · intro h
    refine ⟨hd, Finset.mem_sdiff.mpr ⟨?_, h⟩⟩
    have he := (congrArg
      (fun F : Finset G.edgeSet => data.toRotationSystem.edgeOf d.val ∈ F)
      (event_retained_edges data e)).mp d.property
    exact (Finset.mem_union.mp he).resolve_left h

include ambient hold hnew

/-- Exact exhaustion of the new boundary by surviving old darts and the
newly exposed arc; no additional boundary pieces are omitted. -/
theorem new_boundary_partition
    (d : Dart data.toRotationSystem (edges data.toRotationSystem R.faces))
    (hd : d ∈ outerDarts (toMap data.toRotationSystem (edges data.toRotationSystem R.faces) newOuter)) :
    (∃ x : Dart data.toRotationSystem (edges data.toRotationSystem S.faces),
      oldIntoNew data e x = d ∧
        x ∈ outerDarts (toMap data.toRotationSystem (edges data.toRotationSystem S.faces) oldOuter) ∧
        x ∉ oldAttachmentDarts data e) ∨ d ∈ exposedDarts data e newOuter := by
  by_cases he : data.toRotationSystem.edgeOf d.val ∈ edges data.toRotationSystem S.faces
  · let x : Dart data.toRotationSystem (edges data.toRotationSystem S.faces) := ⟨d.val, he⟩
    have hout := (mem_outerDarts_iff data R.faces ambient newOuter hnew R.inside R.outside d).mp hd
    have hx : x ∈ outerDarts
        (toMap data.toRotationSystem (edges data.toRotationSystem S.faces) oldOuter) := by
      apply (mem_outerDarts_iff data S.faces ambient oldOuter hold S.inside S.outside x).mpr
      exact fun h => hout (e.subset h)
    refine Or.inl ⟨x, rfl, hx, ?_⟩
    exact (old_outer_survives_iff data e ambient oldOuter newOuter hold hnew x hx).mp hd
  · exact Or.inr ((exposed_iff_new_edge data e newOuter d hd).mpr he)

end
end Mettapedia.GraphTheory.FourColor.FaceBoundarySplice
