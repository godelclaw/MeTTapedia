import Mettapedia.GraphTheory.FourColor.InvolutionEulerTransport
import Mettapedia.GraphTheory.FourColor.VertexCodeRotationCyclic
import Mettapedia.GraphTheory.FourColor.VertexCodeViablePrefix

/-!
# Handles cannot disappear during a physical vertex-code run

Serial composition is a disjoint union followed by sewing previously free
darts. Erasing those seams recovers the disjoint union on the same carrier.
The presentation-independent edge-deletion inequality therefore proves
superadditivity of defect, and monotonicity for attachment of a planar star.
-/

namespace Mettapedia.GraphTheory.FourColor.VertexCodeDefectMonotone

open Equiv Equiv.Perm
open GoertzelV24OpenTangleComposition TwoSidedOpenTangleData
open GoertzelV24CompositeSeamCubic SerialTangleSmallCutTransfer
open OpenTangleEulerPresentation InvolutionRestrictionEdgeList
open VertexCodeRotationCyclic TwoSidedBoundaryReindex VertexAttachmentTransfer
open OpenTangleReplacementEuler GoertzelV24CompositeSeamMultigraph
open VertexCodeTrace VertexCodeRealization TubeSlab.VertexTransfer VertexCodePartition

noncomputable section
attribute [local instance] Classical.propDecidable
variable {V W I J L P R : Type*}
  [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq P]
  [Fintype R] [DecidableEq R]

theorem defect_presentation (T : TwoSidedOpenTangleData V I L P)
    (hc : RotationCyclic T) (hs : Function.Surjective T.vertOf) :
    VertexAttachmentTransfer.defect T = InvolutionEulerDefect.defect T.rho (alpha (asOpen T)) := by
  have hs' : Function.Surjective (asOpen T).vertOf := by
    intro v
    obtain ⟨d, hd⟩ := hs v
    exact ⟨d, (asOpen_vertOf T d).trans hd⟩
  have hh := OpenTangleEulerPresentation.defect_eq_twice (asOpen T)
    (rotationCyclic_asOpen hc) hs'
  rw [InvolutionEulerDefect.defect_eq_presentation _ _ (alpha_involutive (asOpen T))]
  exact hh

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R] in
theorem serial_surjective (A : TwoSidedOpenTangleData V I L P)
    (B : TwoSidedOpenTangleData W J P R)
    (hA : Function.Surjective A.vertOf) (hB : Function.Surjective B.vertOf) :
    Function.Surjective (A.serialCompose B (Equiv.refl P)).vertOf := by
  rintro (v | w)
  · obtain ⟨d, hd⟩ := hA v
    refine ⟨serialDartEquiv (.inl d), ?_⟩
    rw [vertOf_serialCompose, serialOutputVertOf_serialDartEquiv]
    exact congrArg Sum.inl hd
  · obtain ⟨d, hd⟩ := hB w
    refine ⟨serialDartEquiv (.inr d), ?_⟩
    rw [vertOf_serialCompose, serialOutputVertOf_serialDartEquiv]
    exact congrArg Sum.inr hd

def sewnAlpha (A : TwoSidedOpenTangleData V I L P)
    (B : TwoSidedOpenTangleData W J P R) : Perm (SerialTangleFaceTransfer.Source I J L P R) :=
  Equiv.sumCongr (alpha (asOpen A)) (alpha (asOpen B)) * SerialTangleFaceTransfer.swap

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R] in
theorem sewnAlpha_involutive (A : TwoSidedOpenTangleData V I L P)
    (B : TwoSidedOpenTangleData W J P R) : Function.Involutive (sewnAlpha A B) := by
  rintro ((i | (l | p)) | (j | (p | r))) <;>
    simp [sewnAlpha, SerialTangleFaceTransfer.swap, alpha, asOpen,
      A.interiorAlpha_involutive, B.interiorAlpha_involutive]

def oldDart : SerialTangleFaceTransfer.Source I J L P R → Prop
  | .inl (.inl _) => True
  | .inr (.inl _) => True
  | _ => False

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R] in
theorem oldDart_sewn (A : TwoSidedOpenTangleData V I L P)
    (B : TwoSidedOpenTangleData W J P R) (d : SerialTangleFaceTransfer.Source I J L P R) :
    oldDart (sewnAlpha A B d) ↔ oldDart d := by
  rcases d with (i | (l | p)) | (j | (p | r)) <;> rfl

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R] in
theorem erase_seams (A : TwoSidedOpenTangleData V I L P)
    (B : TwoSidedOpenTangleData W J P R) :
    restrict (sewnAlpha A B) (sewnAlpha_involutive A B) oldDart (oldDart_sewn A B) =
      Equiv.sumCongr (alpha (asOpen A)) (alpha (asOpen B)) := by
  ext d
  rcases d with (i | (l | p)) | (j | (p | r)) <;>
    simp [restrict_apply, oldDart, sewnAlpha, SerialTangleFaceTransfer.swap, alpha]

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R] in
theorem serial_alpha (A : TwoSidedOpenTangleData V I L P)
    (B : TwoSidedOpenTangleData W J P R) :
    alpha (asOpen (A.serialCompose B (Equiv.refl P))) = serialDartEquiv.permCongr (sewnAlpha A B) := by
  ext d
  obtain ⟨d, rfl⟩ := serialDartEquiv.surjective d
  rcases d with (i | (l | p)) | (j | (p | r)) <;> rfl

theorem serial_defect (A : TwoSidedOpenTangleData V I L P)
    (B : TwoSidedOpenTangleData W J P R)
    (hcA : RotationCyclic A) (hcB : RotationCyclic B)
    (hsA : Function.Surjective A.vertOf) (hsB : Function.Surjective B.vertOf) :
    VertexAttachmentTransfer.defect A + VertexAttachmentTransfer.defect B ≤
      VertexAttachmentTransfer.defect (A.serialCompose B (Equiv.refl P)) := by
  rw [defect_presentation A hcA hsA, defect_presentation B hcB hsB,
    defect_presentation _ (serialCompose_rotationCyclic _ _ _ hcA hcB)
      (serial_surjective A B hsA hsB), serial_alpha]
  have hr : (A.serialCompose B (Equiv.refl P)).rho =
      serialDartEquiv.permCongr (Equiv.sumCongr A.rho B.rho) := rfl
  rw [hr, InvolutionEulerDefect.defect_congr]
  have h := InvolutionEulerDefect.defect_restrict_le (Equiv.sumCongr A.rho B.rho)
    (sewnAlpha A B) (sewnAlpha_involutive A B) oldDart (oldDart_sewn A B)
  rwa [erase_seams, InvolutionEulerDefect.defect_sum] at h

omit [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R] in
theorem star_surjective (order : Fin 3 ≃ P ⊕ R) : Function.Surjective (star order).vertOf := by
  intro v
  exact ⟨(star order).outer, Subsingleton.elim _ _⟩

theorem star_defect (order : Fin 3 ≃ P ⊕ R) : VertexAttachmentTransfer.defect (star order) = 0 := by
  have hc : Nat.card (Quotient (BoundarySmallCutViability.componentSetoid
      (sideMultigraph (asOpen (star order))))) = 1 := by
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  unfold VertexAttachmentTransfer.defect
  rw [hc, star_mass]
  norm_num

theorem append_mono (A : TwoSidedOpenTangleData V I L P) (order : Fin 3 ≃ P ⊕ R)
    (hc : RotationCyclic A) (hs : Function.Surjective A.vertOf) :
    VertexAttachmentTransfer.defect A ≤ VertexAttachmentTransfer.defect (append A order) := by
  have h := serial_defect A (star order) hc (star_rotationCyclic order) hs (star_surjective order)
  rwa [star_defect, add_zero] at h

/-- The former open inequality (M), on the actual attachment. The consumed
component count is not replaced by the number of consumed ports. -/
theorem face_change_bound (A : TwoSidedOpenTangleData V I L P) (order : Fin 3 ≃ P ⊕ R)
    (hc : RotationCyclic A) (hs : Function.Surjective A.vertOf) :
    deltaFaces A order ≤ 1 + (Fintype.card P : Int) -
      2 * Nat.card (Quotient (BoundarySmallCutViability.portSetoid
        (BoundarySmallCutProfile.profile (sideMultigraph (asOpen A)) A.rightVert))) := by
  have hm := append_mono A order hc hs
  have he := defect_change A order
  omega

section Reindex
variable {L' R' : Type*} [Fintype L'] [DecidableEq L'] [Fintype R'] [DecidableEq R']

omit [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq P] [Fintype L'] [DecidableEq L'] [Fintype R'] [DecidableEq R'] in
theorem reindex_surjective (T : TwoSidedOpenTangleData V I L P) (e : L' ⊕ R' ≃ L ⊕ P)
    (hs : Function.Surjective T.vertOf) : Function.Surjective (reindex T e).vertOf := by
  intro v
  obtain ⟨d, hd⟩ := hs v
  refine ⟨(darts e).symm d, ?_⟩
  rw [vert_reindex, Equiv.apply_symm_apply, hd]

omit [DecidableEq V] in
theorem reindex_defect (T : TwoSidedOpenTangleData V I L P) (e : L' ⊕ R' ≃ L ⊕ P) :
    VertexAttachmentTransfer.defect (reindex T e) = VertexAttachmentTransfer.defect T := by
  unfold VertexAttachmentTransfer.defect
  rw [TwoSidedBoundaryJoint.side_reindex, TwoSidedBoundaryJoint.mass_reindex]
  rfl
end Reindex

theorem attach_mono {l r : ℕ} (a : Code l r) (h : Valid a)
    (T : TwoSidedOpenTangleData V I (Fin 0) (Fin l))
    (hc : RotationCyclic T) (hs : Function.Surjective T.vertOf) :
    VertexAttachmentTransfer.defect T ≤ VertexAttachmentTransfer.defect (attach a h T) := by
  change VertexAttachmentTransfer.defect T ≤ VertexAttachmentTransfer.defect
    (reindex (append (prepared a h T) (starOrder a h)) (outCoordinates a))
  rw [reindex_defect]
  have hh := append_mono (prepared a h T) (starOrder a h)
    (reindex_rotationCyclic _ _ hc) (reindex_surjective _ _ hs)
  rw [prepared, reindex_defect] at hh
  exact hh

theorem realize_surjective : {r : ℕ} → (t : Trace r) → Function.Surjective t.realize.vertOf
  | _, .first _ _ => reindex_surjective _ _ (star_surjective _)
  | _, .step t _ _ => reindex_surjective _ _
      (serial_surjective _ _ (reindex_surjective _ _ (realize_surjective t)) (star_surjective _))

theorem realize_defect_nonneg {r : ℕ} (t : Trace r) : 0 ≤ VertexAttachmentTransfer.defect t.realize := by
  rw [defect_presentation _ (realize_rotationCyclic t) (realize_surjective t)]
  exact InvolutionEulerDefect.defect_nonneg _ _ (alpha_involutive _)

omit [DecidableEq V] [DecidableEq I] in
theorem defect_decEq (T : TwoSidedOpenTangleData V I L P) (d e : DecidableEq I) :
    (letI := d; VertexAttachmentTransfer.defect T) =
      (letI := e; VertexAttachmentTransfer.defect T) := by
  cases Subsingleton.elim d e
  rfl

theorem step_mono {l r : ℕ} (t : Trace l) (a : Code l r) (h : Valid a) :
    VertexAttachmentTransfer.defect t.realize ≤ VertexAttachmentTransfer.defect (Trace.step t a h).realize := by
  letI : DecidableEq t.Interior := Classical.decEq _
  exact (attach_mono a h t.realize (realize_rotationCyclic t) (realize_surjective t)).trans_eq
    (defect_decEq (attach a h t.realize) _ _)

/-- Reflexive prefix relation on actual dependent code traces. -/
inductive Prefix : {l r : ℕ} → Trace l → Trace r → Prop
  | refl {r} (t : Trace r) : Prefix t t
  | step {l m r} {s : Trace l} {t : Trace m} (h : Prefix s t)
      (a : Code m r) (valid : Valid a) : Prefix s (.step t a valid)

theorem prefix_mono {l r : ℕ} {s : Trace l} {t : Trace r} (h : Prefix s t) :
    VertexAttachmentTransfer.defect s.realize ≤ VertexAttachmentTransfer.defect t.realize := by
  induction h with
  | refl => exact le_rfl
  | step _ a valid ih => exact ih.trans (step_mono _ a valid)

/-- The terminal hypothesis is essential: later sewing can create handles,
but it cannot repair a prefix that already has one. No colourability premise. -/
theorem planar_prefix {l r : ℕ} {s : Trace l} {t : Trace r} (h : Prefix s t)
    (ht : VertexAttachmentTransfer.defect t.realize = 0) :
    VertexAttachmentTransfer.defect s.realize = 0 := by
  have hl := realize_defect_nonneg s
  have hu := prefix_mono h
  omega

end
end Mettapedia.GraphTheory.FourColor.VertexCodeDefectMonotone
