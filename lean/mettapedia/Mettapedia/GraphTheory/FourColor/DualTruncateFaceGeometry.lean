import Mettapedia.GraphTheory.FourColor.DualTruncateConstructionGSLT
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceTwoSided

/-!
# Actual faces of the dual-and-truncate construction

The expanded face permutation interleaves slots zero and one along source
vertex rotations. Slot two follows the inverse source face permutation.
The joint face label separates these two kinds of actual facial cycles.
Under a genuine cyclic source vertex rotation, it is a complete invariant.
This gives an exact face equivalence and preserves the quotient-face Euler
characteristic, rather than supplying an assumed face count.
-/

namespace Mettapedia.GraphTheory.FourColor.DualTruncateFaceGeometry

open DualTruncateColoring GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceDualConnectedness GoertzelV24OrbitFaceTwoSided
open GoertzelV24OrbitFaceCurvatureBulk

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (RS : RotationSystem V E)

@[simp] theorem phi_zero (d : RS.D) :
    (rotation RS).phi (d, 0) = (RS.alpha d, 1) := by
  simp [RotationSystem.phi, rotation, rho, alpha, DualTruncateColoring.flip]

@[simp] theorem phi_one (d : RS.D) :
    (rotation RS).phi (d, 1) = (RS.phi d, 0) := by
  simp [RotationSystem.phi, rotation, rho, alpha, DualTruncateColoring.flip]

@[simp] theorem phi_two (d : RS.D) :
    (rotation RS).phi (d, 2) = (RS.phi.symm d, 2) := by
  simp [RotationSystem.phi, rotation, rho, alpha, DualTruncateColoring.flip]

theorem phi_sq_zero (d : RS.D) :
    ((rotation RS).phi ^ 2) (d, 0) = (RS.rho d, 0) := by
  rw [pow_two, Equiv.Perm.mul_apply, phi_zero, phi_one]
  simp [RS.alpha_involutive]

theorem pow_zero_slot (n : ℕ) (d : RS.D) :
    ((rotation RS).phi ^ (2 * n)) (d, 0) = ((RS.rho ^ n) d, 0) := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ, pow_add, Equiv.Perm.mul_apply, phi_sq_zero, ih,
      pow_succ, Equiv.Perm.mul_apply]

theorem pow_two_slot (n : ℕ) (d : RS.D) :
    ((rotation RS).phi ^ n) (d, 2) = ((RS.phi⁻¹ ^ n) d, 2) := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, phi_two, ih,
      pow_succ, Equiv.Perm.mul_apply]
    rfl

/-- The joint label retains whether a face comes from a source vertex or
a source face, together with its actual identity. -/
def faceTag (x : Dart RS) : V ⊕ OrbitFace RS :=
  if x.2 = 0 then .inl (RS.vertOf x.1)
  else if x.2 = 1 then .inl (RS.vertOf (RS.alpha x.1))
  else .inr (dartOrbitFace RS x.1)

theorem faceTag_phi (x : Dart RS) :
    faceTag RS ((rotation RS).phi x) = faceTag RS x := by
  rcases x with ⟨d, i⟩
  fin_cases i
  · change faceTag RS ((rotation RS).phi (d, 0)) = faceTag RS (d, 0)
    rw [phi_zero RS d]
    simp [faceTag, RS.alpha_involutive]
  · change faceTag RS ((rotation RS).phi (d, 1)) = faceTag RS (d, 1)
    rw [phi_one RS d]
    simp [faceTag, RS.vert_rho]
  · change faceTag RS ((rotation RS).phi (d, 2)) = faceTag RS (d, 2)
    rw [phi_two RS d]
    change Sum.inr (dartOrbitFace RS (RS.phi.symm d)) = Sum.inr (dartOrbitFace RS d)
    have h := dartOrbitFace_phi_eq RS (RS.phi.symm d)
    exact congrArg (Sum.inr : OrbitFace RS → V ⊕ OrbitFace RS)
      (by simpa only [Equiv.apply_symm_apply] using h.symm)

theorem faceTag_pow (n : ℕ) (x : Dart RS) :
    faceTag RS (((rotation RS).phi ^ n) x) = faceTag RS x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, faceTag_phi, ih]

theorem faceTag_of_sameCycle {x y : Dart RS}
    (h : (rotation RS).phi.SameCycle x y) : faceTag RS x = faceTag RS y := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  simpa only [hn] using (faceTag_pow RS n x).symm

theorem zero_sameCycle (hrotation : VertexRotationCyclic RS) {d e : RS.D}
    (h : RS.vertOf d = RS.vertOf e) :
    (rotation RS).phi.SameCycle (d, 0) (e, 0) := by
  obtain ⟨n, hn⟩ := (hrotation d e h).exists_nat_pow_eq
  refine ⟨(2 * n : ℕ), ?_⟩
  rw [zpow_natCast, pow_zero_slot, hn]

theorem one_sameCycle (d : RS.D) :
    (rotation RS).phi.SameCycle (d, 1) (RS.alpha d, 0) := by
  have h := Mettapedia.GraphTheory.EquivPermSameCycle.step_right
    (rotation RS).phi (RS.alpha d, 0)
  rw [phi_zero RS (RS.alpha d), RS.alpha_involutive] at h
  exact h.symm

theorem two_sameCycle {d e : RS.D}
    (h : dartOrbitFace RS d = dartOrbitFace RS e) :
    (rotation RS).phi.SameCycle (d, 2) (e, 2) := by
  have hsource : RS.phi.SameCycle d e := Quotient.exact h
  obtain ⟨n, hn⟩ := hsource.inv.exists_nat_pow_eq
  refine ⟨(n : ℕ), ?_⟩
  rw [zpow_natCast, pow_two_slot, hn]

/-- Equality of the joint label is exactly equality of actual face orbits. -/
theorem sameCycle_iff_faceTag (hrotation : VertexRotationCyclic RS)
    (x y : Dart RS) :
    (rotation RS).phi.SameCycle x y ↔ faceTag RS x = faceTag RS y := by
  refine ⟨faceTag_of_sameCycle RS, ?_⟩
  rcases x with ⟨d, i⟩
  rcases y with ⟨e, j⟩
  fin_cases i <;> fin_cases j
  · intro h
    exact zero_sameCycle RS hrotation (by simpa [faceTag] using h)
  · intro h
    exact (zero_sameCycle RS hrotation (by simpa [faceTag] using h)).trans
      (one_sameCycle RS e).symm
  · simp [faceTag]
  · intro h
    exact (one_sameCycle RS d).trans
      (zero_sameCycle RS hrotation (by simpa [faceTag] using h))
  · intro h
    exact (one_sameCycle RS d).trans
      ((zero_sameCycle RS hrotation (by simpa [faceTag] using h)).trans
        (one_sameCycle RS e).symm)
  · simp [faceTag]
  · simp [faceTag]
  · simp [faceTag]
  · intro h
    exact two_sameCycle RS (by simpa [faceTag] using h)



theorem faceOrbit_zero_eq (hrotation : VertexRotationCyclic RS) (d : RS.D) :
    (rotation RS).faceOrbit (d, 0) =
      (RS.dartsAt (RS.vertOf d)).image (fun e => (e, (0 : Fin 3))) ∪
      (RS.dartsAt (RS.vertOf d)).image (fun e => (RS.alpha e, (1 : Fin 3))) := by
  ext ⟨e, i⟩
  rw [(rotation RS).mem_faceOrbit, sameCycle_iff_faceTag RS hrotation]
  fin_cases i <;> simp [faceTag, RotationSystem.dartsAt, eq_comm]
  constructor
  · intro h
    exact ⟨RS.alpha e, h, (RS.alpha_involutive e).symm⟩
  · rintro ⟨a, ha, he⟩
    rw [he, RS.alpha_involutive]
    exact ha

theorem faceOrbit_zero_card (hrotation : VertexRotationCyclic RS) (d : RS.D) :
    ((rotation RS).faceOrbit (d, 0)).card = 2 * (RS.dartsAt (RS.vertOf d)).card := by
  have hdisjoint : Disjoint
      ((RS.dartsAt (RS.vertOf d)).image (fun e => (e, (0 : Fin 3))))
      ((RS.dartsAt (RS.vertOf d)).image (fun e => (RS.alpha e, (1 : Fin 3)))) := by
    rw [Finset.disjoint_left]
    rintro x hx hy
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hy
    have hi := congrArg Prod.snd hb
    norm_num at hi
  rw [faceOrbit_zero_eq RS hrotation, Finset.card_union_of_disjoint hdisjoint,
    Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1),
    Finset.card_image_of_injective _ (fun _ _ h => RS.alpha.injective (Prod.mk.inj h).1)]
  omega

theorem faceOrbit_two_eq (hrotation : VertexRotationCyclic RS) (d : RS.D) :
    (rotation RS).faceOrbit (d, 2) =
      (RS.faceOrbit d).image (fun e => (e, (2 : Fin 3))) := by
  ext ⟨e, i⟩
  rw [(rotation RS).mem_faceOrbit, sameCycle_iff_faceTag RS hrotation]
  fin_cases i <;> simp [faceTag, RS.mem_faceOrbit]
  constructor
  · exact Quotient.exact
  · intro h
    change Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi) d =
      Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi) e
    exact Quotient.sound h

/-- The source facial cycle persists with its original length. -/
theorem faceOrbit_two_card (hrotation : VertexRotationCyclic RS) (d : RS.D) :
    ((rotation RS).faceOrbit (d, 2)).card = (RS.faceOrbit d).card := by
  rw [faceOrbit_two_eq RS hrotation]
  exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)

/-- Every source cubic vertex produces one actual hexagonal face. -/
theorem vertex_face_length (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (d : RS.D) : ((rotation RS).faceOrbit (d, 0)).card = 6 := by
  rw [faceOrbit_zero_card RS hrotation, hcubic]


theorem faceTag_surjective (hcubic : RS.IsCubic) :
    Function.Surjective (faceTag RS) := by
  rintro (v | face)
  · obtain ⟨d, hd⟩ := exists_dart_vertOf_eq_of_isCubic RS hcubic v
    exact ⟨(d, 0), by simp [faceTag, hd]⟩
  · obtain ⟨d, hd⟩ := exists_dartOrbitFace_eq RS face
    exact ⟨(d, 2), by simp [faceTag, hd]⟩

/-- Every expanded face is either a source vertex face or a source face,
with both identity and uniqueness retained. -/
def faceEquiv (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS) :
    OrbitFace (rotation RS) ≃ V ⊕ OrbitFace RS :=
  Equiv.ofBijective
    (Quotient.lift (faceTag RS) (fun _ _ h => faceTag_of_sameCycle RS h)) (by
      constructor
      · intro x y h
        obtain ⟨x, rfl⟩ := Quotient.mk_surjective x
        obtain ⟨y, rfl⟩ := Quotient.mk_surjective y
        exact Quotient.sound ((sameCycle_iff_faceTag RS hrotation x y).mpr h)
      · intro tag
        obtain ⟨x, hx⟩ := faceTag_surjective RS hcubic tag
        exact ⟨dartOrbitFace (rotation RS) x, hx⟩)

@[simp] theorem faceEquiv_dart (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS) (x : Dart RS) :
    faceEquiv RS hcubic hrotation (dartOrbitFace (rotation RS) x) = faceTag RS x := rfl

theorem face_count (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS) :
    Fintype.card (OrbitFace (rotation RS)) =
      Fintype.card V + Fintype.card (OrbitFace RS) := by
  simpa only [Fintype.card_sum] using Fintype.card_congr (faceEquiv RS hcubic hrotation)

/-- The actual facial equivalence supplies the entire Euler calculation. -/
theorem euler_preserved (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS) :
    (Fintype.card RS.D : ℤ) - Fintype.card (Edge RS) +
      Fintype.card (OrbitFace (rotation RS)) =
    (Fintype.card V : ℤ) - Fintype.card E + Fintype.card (OrbitFace RS) := by
  rw [face_count RS hcubic hrotation]
  simp only [Fintype.card_sum, Nat.cast_add]
  omega

/-- A cubic cellular-sphere source produces a cubic cellular-sphere target. -/
theorem spherical (h : OrbitSphericalCubicMapData RS)
    (hrotation : VertexRotationCyclic RS) : OrbitSphericalCubicMapData (rotation RS) where
  cubic := DualTruncateColoring.cubic RS
  euler := (euler_preserved RS h.cubic hrotation).trans h.euler

/-- Every target edge has two distinct actual facial sides. -/
theorem facesTwoSided : OrbitFacesTwoSided (rotation RS) := by
  rintro ⟨d, i⟩ h
  have ht := faceTag_of_sameCycle RS (Quotient.exact h)
  fin_cases i
  · exact RS.no_self_loops d (by simpa [faceTag, rotation, alpha, DualTruncateColoring.flip] using ht)
  · simp [faceTag, rotation, alpha, DualTruncateColoring.flip] at ht
  · simp [faceTag, rotation, alpha, DualTruncateColoring.flip] at ht

theorem faceBoundarySimple : OrbitFaceBoundarySimple (rotation RS) :=
  orbitFaceBoundarySimple_of_twoSided (rotation RS) (facesTwoSided RS)

theorem vertex_face_length_one (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (d : RS.D) : ((rotation RS).faceOrbit (d, 1)).card = 6 := by
  rw [(rotation RS).faceOrbit_eq_of_sameCycle (one_sameCycle RS d)]
  exact vertex_face_length RS hcubic hrotation (RS.alpha d)

/-- Source pentagonal and hexagonal facial boundaries persist; the added
source-vertex faces are hexagons. Boundary simplicity is explicit. -/
theorem fullerene (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (hsimple : OrbitFaceBoundarySimple RS) (hfull : OrbitFaceFullerene RS) :
    OrbitFaceFullerene (rotation RS) := by
  intro face
  rw [faceBoundarySimple RS face]
  obtain ⟨⟨d, i⟩, rfl⟩ := exists_dartOrbitFace_eq (rotation RS) face
  rw [orbitFaceDarts_dartOrbitFace_eq_faceOrbit]
  fin_cases i
  · change ((rotation RS).faceOrbit (d, 0)).card = 5 ∨
      ((rotation RS).faceOrbit (d, 0)).card = 6
    exact Or.inr (vertex_face_length RS hcubic hrotation d)
  · change ((rotation RS).faceOrbit (d, 1)).card = 5 ∨
      ((rotation RS).faceOrbit (d, 1)).card = 6
    exact Or.inr (vertex_face_length_one RS hcubic hrotation d)
  · change ((rotation RS).faceOrbit (d, 2)).card = 5 ∨
      ((rotation RS).faceOrbit (d, 2)).card = 6
    rw [faceOrbit_two_card RS hrotation]
    have hf := hfull (dartOrbitFace RS d)
    rwa [hsimple, orbitFaceDarts_dartOrbitFace_eq_faceOrbit] at hf

end
end Mettapedia.GraphTheory.FourColor.DualTruncateFaceGeometry
