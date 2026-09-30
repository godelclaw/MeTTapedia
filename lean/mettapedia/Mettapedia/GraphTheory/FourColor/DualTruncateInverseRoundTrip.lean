import Mettapedia.GraphTheory.FourColor.DualTruncateInverseGeometry

/-!
# Exact round trip through the recovered source

The literal construction has a face cover selected by its actual face
classification. The target-only inverse recovers the source vertex orbits.
The round trip transports genuine source vertex colours, retaining their
edge constraints, for use by target reconstruction. No colour table is used.
-/

namespace Mettapedia.GraphTheory.FourColor.DualTruncateInverseRoundTrip

open DualTruncateColoring DualTruncateInverse DualTruncateFaceCoverFrame
open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness
open GoertzelV24OrbitFaceTwoSided

noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (S : RotationSystem.{u,u,u} V E) (hc : S.IsCubic)
  (hr : VertexRotationCyclic S)

def marked (face : OrbitFace (rotation S)) : Prop :=
  (DualTruncateFaceGeometry.faceEquiv S hc hr face).isRight

theorem marked_iff (x : (rotation S).D) :
    marked S hc hr (dartOrbitFace (rotation S) x) ↔ x.2 = 2 := by
  rcases x with ⟨v, i⟩
  simp only [marked, DualTruncateFaceGeometry.faceEquiv_dart]
  fin_cases i <;> simp [DualTruncateFaceGeometry.faceTag]

/-- The recovered data is supplied by the target's actual face marks and
frame. It carries no source rotation or colouring field. -/
def data : Data (rotation S) where
  frame := {
    dart := Equiv.refl _
    vertex := fun _ => rfl
    turn := fun _ => rfl }
  marked := marked S hc hr
  mark := marked_iff S hc hr

def cover : Cover (rotation S) where
  marked := marked S hc hr
  unique v := by
    refine ⟨(v, 2), ⟨rfl, (marked_iff S hc hr _).mpr rfl⟩, ?_⟩
    rintro ⟨w, i⟩ ⟨hv, hm⟩
    change w = v at hv
    have hi := (marked_iff S hc hr (w, i)).mp hm
    exact Prod.ext hv hi

theorem unmarked_hexagons (x : (rotation S).D)
    (hm : ¬(data S hc hr).marked (dartOrbitFace (rotation S) x)) :
    ((rotation S).faceOrbit x).card = 6 := by
  rcases x with ⟨v, i⟩
  have hi : i ≠ 2 := by simpa only [data, marked_iff] using hm
  fin_cases i
  · exact DualTruncateFaceGeometry.vertex_face_length S hc hr v
  · exact DualTruncateFaceGeometry.vertex_face_length_one S hc hr v
  · exact (hi rfl).elim

abbrev recovered := source (rotation S) (data S hc hr) (DualTruncateFaceGeometry.facesTwoSided S)

@[simp] theorem recovered_alpha (v : S.D) :
    sourceAlpha (rotation S) (data S hc hr) v = S.alpha v := rfl

@[simp] theorem recovered_phi (v : S.D) :
    sourcePhi (rotation S) (data S hc hr) v = S.phi v := rfl

theorem recovered_rho : sourceRho (rotation S) (data S hc hr) = S.rho := by
  apply Equiv.ext
  intro v
  change S.phi (S.alpha v) = S.rho v
  rw [RotationSystem.phi_apply, S.alpha_involutive]

private theorem vertex_sameCycle {v w : S.D} (h : S.rho.SameCycle v w) :
    S.vertOf v = S.vertOf w := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have hp : ∀ n : ℕ, S.vertOf ((S.rho ^ n) v) = S.vertOf v := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, S.vert_rho, ih]
  rw [← hn]
  exact (hp n).symm

def vertexMap : SourceVertex (rotation S) (data S hc hr) → V :=
  Quotient.lift S.vertOf (fun v w h => by
    apply vertex_sameCycle S
    change (sourceRho (rotation S) (data S hc hr)).SameCycle v w at h
    rwa [recovered_rho] at h)

/-- Source vertices are recovered exactly, rather than replaced by an
observational quotient which merges distinct source vertices. -/
def vertexEquiv : SourceVertex (rotation S) (data S hc hr) ≃ V :=
  Equiv.ofBijective (vertexMap S hc hr) ⟨by
    intro x y h
    induction x, y using Quotient.inductionOn₂ with
    | _ v w =>
      apply Quotient.sound
      change (sourceRho (rotation S) (data S hc hr)).SameCycle v w
      rw [recovered_rho]
      exact hr v w h,
    by
      intro v
      obtain ⟨w, hw⟩ := exists_dart_vertOf_eq_of_isCubic S hc v
      exact ⟨Quotient.mk _ w, hw⟩⟩

@[simp] theorem vertexEquiv_dart (v : S.D) :
    vertexEquiv S hc hr ((recovered S hc hr).vertOf v) = S.vertOf v := rfl

/-- Genuine vertex colouring witnesses descend through the recovered
rotation orbits and remain proper on every actual source edge. -/
def colouring (c : ThreeVertexColoring S) : ThreeVertexColoring (recovered S hc hr) where
  colour v := c.colour (vertexEquiv S hc hr v)
  nonzero v := c.nonzero _
  proper v := by
    change c.colour (S.vertOf v) ≠
      c.colour (S.vertOf (sourceAlpha (rotation S) (data S hc hr) v))
    rw [recovered_alpha]
    exact c.proper v

/-- Cover selection recovers the same canonical frame; the chosen marked
dart is uniquely determined by the actual target face observation. -/
theorem fromCover_dart :
    (DualTruncateFaceCoverFrame.fromCover (rotation S) (cubic S)
      (DualTruncateConstructionGSLT.rotationCyclic S) (cover S hc hr)).dart =
      Equiv.refl _ := by
  apply Equiv.ext
  rintro ⟨v, i⟩
  have hm : markedDart (rotation S) (cover S hc hr) v = ⟨(v, 2), rfl⟩ :=
    (markedDart_unique (rotation S) (cover S hc hr) v ⟨(v, 2), rfl⟩
      ((marked_iff S hc hr (v, 2)).mpr rfl)).symm
  change (VertexCodeCyclicEncoder.cyc (VertexCodeCyclicEncoder.rot
    (markedDart (rotation S) (cover S hc hr) v)) i).1 = (v, i)
  rw [hm]
  fin_cases i <;> rfl

/-- The convenient literal data and data obtained from target face-cover
selection are equal, including the joint slot observations. -/
theorem fromCover_data :
    DualTruncateInverse.fromCover (rotation S) (cubic S)
      (DualTruncateConstructionGSLT.rotationCyclic S) (cover S hc hr) = data S hc hr := by
  have he := fromCover_dart S hc hr
  unfold DualTruncateInverse.fromCover data
  congr 1
  cases hf : DualTruncateFaceCoverFrame.fromCover (rotation S) (cubic S)
      (DualTruncateConstructionGSLT.rotationCyclic S) (cover S hc hr) with
  | mk dart vertex turn =>
    rw [hf] at he
    change dart = Equiv.refl _ at he
    subst dart
    rfl

end
end Mettapedia.GraphTheory.FourColor.DualTruncateInverseRoundTrip
