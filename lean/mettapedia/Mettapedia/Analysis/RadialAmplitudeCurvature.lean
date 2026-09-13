import Mettapedia.Analysis.RadialPancakeCurvature
import Mettapedia.Analysis.SignedCrossKernelFreezing

/-!
# Normal geometry of the amplitude-curvature channel

After separating the isotropic derivative channel, the radial amplitude
channel contains the normal component of the endpoint value itself.
Tangency of that value cancels this channel without requiring tangent
gradients. Each periodic image retains its own normal and signed coefficient.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.RadialPancakeCurvature

open SignedCrossKernel EuclideanCrossProduct
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Op" => R3 →L[ℝ] R3

theorem amplitudeCurvature_radialOperator (n : ℕ) (c k : ℝ) (h a v w : R3) :
    amplitudeCurvature n
      (c • ContinuousLinearMap.id ℝ R3 + k • (innerSL ℝ h).smulRight h) a v w =
      2 * (2 * (n + 2) : ℝ) * k * ‖a‖ ^ (2 * (n + 1)) * ⟪a, v - w⟫ *
        tripleProduct (v - w) a h * ⟪h, a⟫ := by
  have hz : ⟪cross (v - w) a, a⟫ = 0 := by
    rw [real_inner_comm]
    exact inner_cross_self (v - w) a
  simp only [amplitudeCurvature, add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_add_right,
    real_inner_smul_right, hz, mul_zero, zero_add, tripleProduct]
  ring

theorem amplitudeCurvature_radialOperator_eq_zero_of_tangent
    (n : ℕ) (c k : ℝ) (h a v w : R3) (ha : ⟪h, a⟫ = 0) :
    amplitudeCurvature n
      (c • ContinuousLinearMap.id ℝ R3 + k • (innerSL ℝ h).smulRight h) a v w = 0 := by
  rw [amplitudeCurvature_radialOperator, ha, mul_zero]

theorem amplitudeCurvature_tensor (N n : ℕ) (e : R3) (he : ‖e‖ = 1)
    {h : R3} (hh : h ≠ 0) (a v w : R3) :
    amplitudeCurvature n (RadialRieszRegularization.tensor N h) a v w =
      2 * (2 * (n + 2) : ℝ) * RadialRieszRegularization.radialCoefficient N e h *
        ‖a‖ ^ (2 * (n + 1)) * ⟪a, v - w⟫ * tripleProduct (v - w) a h * ⟪h, a⟫ := by
  rw [RadialRieszRegularization.tensor_eq N e he hh, amplitudeCurvature_radialOperator]

theorem amplitudeCurvature_tensor_eq_zero_of_tangent (N n : ℕ) (e : R3) (he : ‖e‖ = 1)
    {h : R3} (hh : h ≠ 0) (a v w : R3) (ha : ⟪h, a⟫ = 0) :
    amplitudeCurvature n (RadialRieszRegularization.tensor N h) a v w = 0 := by
  rw [amplitudeCurvature_tensor N n e he hh, ha, mul_zero]

theorem hasSum_amplitudeCurvature {ι : Type*} (n : ℕ) {H : ι → Op} {K : Op}
    (hH : HasSum H K) (a v w : R3) :
    HasSum (fun i ↦ amplitudeCurvature n (H i) a v w) (amplitudeCurvature n K a v w) := by
  have hs := (innerSL ℝ (cross (v - w) a)).hasSum
    ((ContinuousLinearMap.apply ℝ R3 a).hasSum hH)
  exact hs.mul_left (2 * (2 * (n + 2) : ℝ) * ‖a‖ ^ (2 * (n + 1)) * ⟪a, v - w⟫)

theorem hasSum_amplitudeCurvature_images (N n : ℕ) (e : R3) (he : ‖e‖ = 1)
    {q : UnitAddTorus (Fin 3)} (hq : q ≠ 0) (a v w : R3) :
    HasSum (fun z : UnitTorusLattice.LatticeSubmodule (ι := Fin 3) ↦
      2 * (2 * (n + 2) : ℝ) * RadialRieszRegularization.radialCoefficient N e
        (UnitTorusSchwartzLattice.displacement q z) * ‖a‖ ^ (2 * (n + 1)) * ⟪a, v - w⟫ *
        tripleProduct (v - w) a (UnitTorusSchwartzLattice.displacement q z) *
          ⟪UnitTorusSchwartzLattice.displacement q z, a⟫)
      (amplitudeCurvature n (PeriodicRadialRiesz.tensor N q) a v w) := by
  apply (hasSum_amplitudeCurvature n (PeriodicRadialRiesz.hasSum_tensor_images N hq) a v w).congr_fun
  intro z
  exact (amplitudeCurvature_tensor N n e he (UnitTorusSchwartzLattice.displacement_ne_zero hq z) a v w).symm

end Mettapedia.Analysis.RadialPancakeCurvature
