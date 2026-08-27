import Mettapedia.GraphTheory.FourColor.GoertzelV24DigonPatchDarts

/-!
# Exact facial two-cycle at a cubic digon

This file instantiates the generic two-door orbit argument on the canonical
darts of a `DigonPatchData`.  The only residual representation hypothesis is
that the far endpoint of the second attachment is not the other digon
vertex; looplessness already keeps it away from its own endpoint.  The
excluded case is the two-vertex three-edge dipole; it belongs to the finite
floor, not to digon suppression in a larger graph.

Under cubicity, cyclic vertex rotations, and two-sided faces, one of the two
possible local orientations makes one parallel-edge side pair an exact
two-cycle of the face permutation.  Thus the corresponding quotient face is
literally the digon.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace RotationSystem

open GoertzelV24DigonFaceLocal
open GoertzelV24OrbitFaceTwoSided

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

namespace DigonPatchData

variable {RS : RotationSystem V E} (D : @DigonPatchData V E)

/-- One of the two possible digon sides is an exact two-dart face orbit. -/
def HasExactDigonFace (hD : D.WellFormed RS) : Prop :=
  (RS.phi (D.q₁ hD) = D.p₂ hD ∧
      RS.phi (D.p₂ hD) = D.q₁ hD ∧
      ∀ point, RS.phi.SameCycle (D.q₁ hD) point ↔
        point = D.q₁ hD ∨ point = D.p₂ hD) ∨
    (RS.phi (D.q₂ hD) = D.p₁ hD ∧
      RS.phi (D.p₁ hD) = D.q₂ hD ∧
      ∀ point, RS.phi.SameCycle (D.q₂ hD) point ↔
        point = D.q₂ hD ∨ point = D.p₁ hD)

/-- A cubic, two-sided rotation system makes a non-dipole parallel pair bound
an exact digon face.  `houter` says that following the exterior edge at `v`
does not return to `u`; looplessness keeps it away from `v`.  The only cubic
failure is the three-edge dipole on `u,v`. -/
theorem hasExactDigonFace_of_twoSided
    (hD : D.WellFormed RS) (hCubic : RS.IsCubic)
    (hrotation : GoertzelV24FaceDualConnectedness.VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS)
    (houter : RS.vertOf (D.b' hD) ≠ D.u) :
    D.HasExactDigonFace hD := by
  have houterV : RS.vertOf (D.b' hD) ≠ D.v := by
    intro hloop
    apply RS.no_self_loops (D.qᵦ hD)
    rw [D.vertOf_qᵦ hD, D.alpha_qᵦ hD, hloop]
  let side : RS.D → Bool := fun dart =>
    decide (RS.vertOf dart = D.u ∨ RS.vertOf dart = D.v)
  have hside_qᵦ : side (D.qᵦ hD) = true := by
    simp [side, D.vertOf_qᵦ hD]
  have hstep : ∀ x, x ≠ D.a' hD → x ≠ D.b' hD →
      side x ≠ side (D.qᵦ hD) → side (RS.phi x) = side x := by
    intro x hxa hxb hxside
    have hxOutside : RS.vertOf x ≠ D.u ∧ RS.vertOf x ≠ D.v := by
      constructor
      · intro hxu
        apply hxside
        rw [hside_qᵦ]
        simp [side, hxu]
      · intro hxv
        apply hxside
        rw [hside_qᵦ]
        simp [side, hxv]
    have halphaOutside :=
      D.alpha_exterior_of_exterior_of_ne_attachments hD hCubic
        hxa hxb hxOutside
    have hphiOutside :
        RS.vertOf (RS.phi x) ≠ D.u ∧ RS.vertOf (RS.phi x) ≠ D.v := by
      simpa only [RS.vert_phi_eq_vert_alpha] using halphaOutside
    have hxFalse : side x = false := by
      change decide (RS.vertOf x = D.u ∨ RS.vertOf x = D.v) = false
      exact decide_eq_false_iff_not.mpr (not_or_intro hxOutside.1 hxOutside.2)
    have hphiFalse : side (RS.phi x) = false := by
      change decide
        (RS.vertOf (RS.phi x) = D.u ∨ RS.vertOf (RS.phi x) = D.v) = false
      exact decide_eq_false_iff_not.mpr
        (not_or_intro hphiOutside.1 hphiOutside.2)
    rw [hxFalse, hphiFalse]
  have hcross : side (RS.phi (D.qᵦ hD)) ≠ side (D.qᵦ hD) := by
    have hphiOutside :
        RS.vertOf (RS.phi (D.qᵦ hD)) ≠ D.u ∧
          RS.vertOf (RS.phi (D.qᵦ hD)) ≠ D.v := by
      constructor
      · rw [RS.vert_phi_eq_vert_alpha, D.alpha_qᵦ hD]
        exact houter
      · rw [RS.vert_phi_eq_vert_alpha, D.alpha_qᵦ hD]
        exact houterV
    have hphiFalse : side (RS.phi (D.qᵦ hD)) = false := by
      change decide
        (RS.vertOf (RS.phi (D.qᵦ hD)) = D.u ∨
          RS.vertOf (RS.phi (D.qᵦ hD)) = D.v) = false
      exact decide_eq_false_iff_not.mpr
        (not_or_intro hphiOutside.1 hphiOutside.2)
    rw [hside_qᵦ, hphiFalse]
    decide
  have hbTwoSided :
      ¬ RS.phi.SameCycle (D.qᵦ hD) (D.b' hD) := by
    simpa only [D.alpha_qᵦ hD] using
      not_sameCycle_of_dartOrbitFace_ne RS htwoSided (D.qᵦ hD)
  rcases D.rho_orientation_u hD hCubic hrotation with hforward | hreverse
  · left
    have hfirst : RS.phi (D.q₁ hD) = D.p₂ hD := by
      simp only [RotationSystem.phi_apply, D.alpha_q₁ hD]
      exact hforward.1
    have hsecond :
        RS.phi (D.p₂ hD) = D.q₁ hD ∨
          RS.phi (D.p₂ hD) = D.qᵦ hD := by
      simp only [RotationSystem.phi_apply, D.alpha_p₂ hD]
      exact D.rho_q₂_eq_q₁_or_qᵦ hD hCubic hrotation
    have haReturn : RS.phi (D.a' hD) = D.p₁ hD := by
      simp only [RotationSystem.phi_apply, D.alpha_a' hD]
      exact hforward.2.2
    have he₁TwoSided :
        ¬ RS.phi.SameCycle (D.q₁ hD) (D.p₁ hD) := by
      simpa only [D.alpha_q₁ hD] using
        not_sameCycle_of_dartOrbitFace_ne RS htwoSided (D.q₁ hD)
    exact exact_twoCycle_of_twoDoorSide RS.phi side
      (D.p₁ hD) (D.p₂ hD) (D.q₁ hD) (D.qᵦ hD)
      (D.a' hD) (D.b' hD) hfirst hsecond hstep hcross
      hbTwoSided haReturn he₁TwoSided
  · right
    have hfirst : RS.phi (D.q₂ hD) = D.p₁ hD := by
      simp only [RotationSystem.phi_apply, D.alpha_q₂ hD]
      exact hreverse.1
    have hsecond :
        RS.phi (D.p₁ hD) = D.q₂ hD ∨
          RS.phi (D.p₁ hD) = D.qᵦ hD := by
      simp only [RotationSystem.phi_apply, D.alpha_p₁ hD]
      exact D.rho_q₁_eq_q₂_or_qᵦ hD hCubic hrotation
    have haReturn : RS.phi (D.a' hD) = D.p₂ hD := by
      simp only [RotationSystem.phi_apply, D.alpha_a' hD]
      exact hreverse.2.2
    have he₂TwoSided :
        ¬ RS.phi.SameCycle (D.q₂ hD) (D.p₂ hD) := by
      simpa only [D.alpha_q₂ hD] using
        not_sameCycle_of_dartOrbitFace_ne RS htwoSided (D.q₂ hD)
    exact exact_twoCycle_of_twoDoorSide RS.phi side
      (D.p₂ hD) (D.p₁ hD) (D.q₂ hD) (D.qᵦ hD)
      (D.a' hD) (D.b' hD) hfirst hsecond hstep hcross
      hbTwoSided haReturn he₂TwoSided

/-- Boundary-support form of the exact digon theorem: the rotation map has
a quotient face whose edge boundary is precisely the parallel pair. -/
theorem exists_orbitFaceBoundary_eq_parallel_pair_of_twoSided
    (hD : D.WellFormed RS) (hCubic : RS.IsCubic)
    (hrotation : GoertzelV24FaceDualConnectedness.VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS)
    (houter : RS.vertOf (D.b' hD) ≠ D.u) :
    ∃ face : GoertzelV24FaceOrbitIncidence.OrbitFace RS,
      GoertzelV24FaceOrbitIncidence.orbitFaceBoundary RS face =
        {D.e, D.f} := by
  have hexact := D.hasExactDigonFace_of_twoSided
    hD hCubic hrotation htwoSided houter
  rcases hexact with hfirst | hsecond
  · refine ⟨GoertzelV24FaceOrbitIncidence.dartOrbitFace RS (D.q₁ hD), ?_⟩
    have hdarts :
        GoertzelV24FaceOrbitIncidence.orbitFaceDarts RS
          (GoertzelV24FaceOrbitIncidence.dartOrbitFace RS (D.q₁ hD)) =
            {D.q₁ hD, D.p₂ hD} := by
      rw [GoertzelV24FaceOrbitIncidence.orbitFaceDarts_dartOrbitFace_eq_faceOrbit]
      ext point
      rw [RS.mem_faceOrbit]
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hfirst.2.2 point
    unfold GoertzelV24FaceOrbitIncidence.orbitFaceBoundary
    rw [hdarts]
    simp [D.edgeOf_q₁ hD, D.edgeOf_p₂ hD, Finset.pair_comm]
  · refine ⟨GoertzelV24FaceOrbitIncidence.dartOrbitFace RS (D.q₂ hD), ?_⟩
    have hdarts :
        GoertzelV24FaceOrbitIncidence.orbitFaceDarts RS
          (GoertzelV24FaceOrbitIncidence.dartOrbitFace RS (D.q₂ hD)) =
            {D.q₂ hD, D.p₁ hD} := by
      rw [GoertzelV24FaceOrbitIncidence.orbitFaceDarts_dartOrbitFace_eq_faceOrbit]
      ext point
      rw [RS.mem_faceOrbit]
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hsecond.2.2 point
    unfold GoertzelV24FaceOrbitIncidence.orbitFaceBoundary
    rw [hdarts]
    simp [D.edgeOf_q₂ hD, D.edgeOf_p₁ hD, Finset.pair_comm]

/-- Combined form matching the paper: both the exact two-dart orbit and its
two-edge quotient boundary are available from the same hypotheses. -/
theorem exactDigonFace_and_boundary_of_twoSided
    (hD : D.WellFormed RS) (hCubic : RS.IsCubic)
    (hrotation : GoertzelV24FaceDualConnectedness.VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS)
    (houter : RS.vertOf (D.b' hD) ≠ D.u) :
    D.HasExactDigonFace hD ∧
      ∃ face : GoertzelV24FaceOrbitIncidence.OrbitFace RS,
        GoertzelV24FaceOrbitIncidence.orbitFaceBoundary RS face =
          {D.e, D.f} :=
  ⟨D.hasExactDigonFace_of_twoSided hD hCubic hrotation htwoSided houter,
    D.exists_orbitFaceBoundary_eq_parallel_pair_of_twoSided
      hD hCubic hrotation htwoSided houter⟩

end DigonPatchData

end

end RotationSystem

namespace GoertzelV24DigonFaceExact

open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceTwoSided

/-- Module-aligned public name for the combined exact-orbit and boundary
theorem, used by the paper's verification ledger. -/
theorem exactDigonFace_and_boundary_of_twoSided
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {RS : RotationSystem V E} (D : @RotationSystem.DigonPatchData V E)
    (hD : D.WellFormed RS) (hCubic : RS.IsCubic)
    (hrotation : GoertzelV24FaceDualConnectedness.VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS)
    (houter : RS.vertOf (D.b' hD) ≠ D.u) :
    D.HasExactDigonFace hD ∧
      ∃ face : OrbitFace RS,
        orbitFaceBoundary RS face = {D.e, D.f} :=
  D.exactDigonFace_and_boundary_of_twoSided
    hD hCubic hrotation htwoSided houter

end GoertzelV24DigonFaceExact

end Mettapedia.GraphTheory.FourColor
