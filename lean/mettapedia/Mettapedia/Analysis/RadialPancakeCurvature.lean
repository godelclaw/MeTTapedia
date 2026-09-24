import Mettapedia.Analysis.SignedCrossKernelCurvatureIncrement
import Mettapedia.Analysis.PeriodicRadialRiesz

/-!
# Radial paired curvature and pancake-plane derivative defects

The isotropic operator component cancels from the full second variation.
For the radial component, normal pairings of endpoint values and gradients
remain explicit. Tangency of values alone does not imply zero curvature;
tangency of their gradients is a separate condition. Periodization sums the
actual image displacements, not a single normal for the periodic kernel.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.RadialPancakeCurvature

open SignedCrossKernel RadialPower EuclideanCrossProduct
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Op" => R3 →L[ℝ] R3
local notation "T3" => UnitAddTorus (Fin 3)
local notation "Lat" => UnitTorusLattice.LatticeSubmodule (ι := Fin 3)

def radialCurvature (n : ℕ) (a b h v w : R3) : ℝ :=
  2 * tripleProduct v w h * ⟪h, radialPower (2 * (n + 2)) a - radialPower (2 * (n + 2)) b⟫ +
  2 * (tripleProduct v b h + tripleProduct a w h) *
    ⟪h, evenRadialRate (n + 1) a v - evenRadialRate (n + 1) b w⟫ +
  tripleProduct a b h * ⟪h, evenRadialCurvature n a v - evenRadialCurvature n b w⟫

theorem pairedCurvature_radialOperator (n : ℕ) (c k : ℝ) (h a b v w : R3) :
    pairedCurvature n (c • ContinuousLinearMap.id ℝ R3 + k • (innerSL ℝ h).smulRight h) a b v w =
      k * radialCurvature n a b h v w := by
  rw [add_comm, pairedCurvature_add_scalar_identity]
  simp only [pairedCurvature, radialCurvature, tripleProduct, smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, real_inner_smul_right, inner_add_left]
  ring

/-- With tangent endpoint values, only the normal derivatives survive. -/
theorem radialCurvature_of_plane (n : ℕ) (a b h v w : R3)
    (ha : ⟪h, a⟫ = 0) (hb : ⟪h, b⟫ = 0) :
    radialCurvature n a b h v w =
      2 * (tripleProduct v b h + tripleProduct a w h) *
        (‖a‖ ^ (2 * (n + 2)) * ⟪h, v⟫ - ‖b‖ ^ (2 * (n + 2)) * ⟪h, w⟫) +
      (4 * (n + 2) : ℝ) * tripleProduct a b h *
        (‖a‖ ^ (2 * (n + 1)) * ⟪a, v⟫ * ⟪h, v⟫ -
          ‖b‖ ^ (2 * (n + 1)) * ⟪b, w⟫ * ⟪h, w⟫) := by
  simp only [radialCurvature, radialPower, evenRadialRate, evenRadialCurvature,
    inner_sub_right, inner_add_right, real_inner_smul_right, ha, hb,
    show n + 1 + 1 = n + 2 by omega]
  ring

theorem radialCurvature_eq_zero_of_tangent (n : ℕ) (a b h v w : R3)
    (ha : ⟪h, a⟫ = 0) (hb : ⟪h, b⟫ = 0)
    (hv : ⟪h, v⟫ = 0) (hw : ⟪h, w⟫ = 0) : radialCurvature n a b h v w = 0 := by
  rw [radialCurvature_of_plane n a b h v w ha hb]
  simp [hv, hw]

theorem pairedCurvature_tensor (N n : ℕ) (e : R3) (he : ‖e‖ = 1)
    {h : R3} (hh : h ≠ 0) (a b v w : R3) :
    pairedCurvature n (RadialRieszRegularization.tensor N h) a b v w =
      RadialRieszRegularization.radialCoefficient N e h * radialCurvature n a b h v w := by
  rw [RadialRieszRegularization.tensor_eq N e he hh, pairedCurvature_radialOperator]

theorem pairedCurvature_tensor_eq_zero_of_tangent (N n : ℕ) (e : R3) (he : ‖e‖ = 1)
    {h : R3} (hh : h ≠ 0) (a b v w : R3)
    (ha : ⟪h, a⟫ = 0) (hb : ⟪h, b⟫ = 0)
    (hv : ⟪h, v⟫ = 0) (hw : ⟪h, w⟫ = 0) :
    pairedCurvature n (RadialRieszRegularization.tensor N h) a b v w = 0 := by
  rw [pairedCurvature_tensor N n e he hh, radialCurvature_eq_zero_of_tangent n a b h v w ha hb hv hw,
    mul_zero]

/-- Equal tangent values retain a quadratic gradient-increment channel. -/
theorem pairedCurvature_radial_same_value (n : ℕ) (c k : ℝ) (h a v w : R3)
    (ha : ⟪h, a⟫ = 0) :
    pairedCurvature n (c • ContinuousLinearMap.id ℝ R3 + k • (innerSL ℝ h).smulRight h) a a v w =
      2 * k * ‖a‖ ^ (2 * (n + 2)) * tripleProduct (v - w) a h * ⟪h, v - w⟫ := by
  rw [add_comm, pairedCurvature_add_scalar_identity, pairedCurvature_same_value]
  simp only [evenRadialRate, smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, inner_add_right, real_inner_smul_right, ha,
    show n + 1 + 1 = n + 2 by omega, tripleProduct]
  ring

theorem abs_pairedCurvature_radial_same_value_le (n : ℕ) (c k : ℝ) (h a v w : R3)
    (ha : ⟪h, a⟫ = 0) :
    |pairedCurvature n (c • ContinuousLinearMap.id ℝ R3 + k • (innerSL ℝ h).smulRight h) a a v w| ≤
      2 * |k| * ‖a‖ ^ (2 * (n + 2)) * ‖cross (v - w) a‖ * ‖h‖ * |⟪h, v - w⟫| := by
  rw [pairedCurvature_radial_same_value n c k h a v w ha]
  simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_nonneg (pow_nonneg (norm_nonneg a) _)]
  have hb := abs_real_inner_le_norm (cross (v - w) a) h
  have ht := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * |k| * ‖a‖ ^ (2 * (n + 2))))
    (abs_nonneg ⟪h, v - w⟫)
  exact ht.trans_eq (by ring)

theorem pairedCurvature_tensor_same_value (N n : ℕ) (e : R3) (he : ‖e‖ = 1)
    {h : R3} (hh : h ≠ 0) (a v w : R3) (ha : ⟪h, a⟫ = 0) :
    pairedCurvature n (RadialRieszRegularization.tensor N h) a a v w =
      2 * RadialRieszRegularization.radialCoefficient N e h * ‖a‖ ^ (2 * (n + 2)) *
        tripleProduct (v - w) a h * ⟪h, v - w⟫ := by
  rw [RadialRieszRegularization.tensor_eq N e he hh, pairedCurvature_radial_same_value n _ _ h a v w ha]

theorem hasSum_pairedCurvature {ι : Type*} (n : ℕ) {H : ι → Op} {K : Op}
    (hH : HasSum H K) (a b v w : R3) :
    HasSum (fun i ↦ pairedCurvature n (H i) a b v w) (pairedCurvature n K a b v w) := by
  have h₁ := (innerSL ℝ (cross v w)).hasSum
    ((ContinuousLinearMap.apply ℝ R3 (radialPower (2 * (n + 2)) a -
      radialPower (2 * (n + 2)) b)).hasSum hH)
  have h₂ := (innerSL ℝ (cross v b + cross a w)).hasSum
    ((ContinuousLinearMap.apply ℝ R3 (evenRadialRate (n + 1) a v -
      evenRadialRate (n + 1) b w)).hasSum hH)
  have h₃ := (innerSL ℝ (cross a b)).hasSum
    ((ContinuousLinearMap.apply ℝ R3 (evenRadialCurvature n a v - evenRadialCurvature n b w)).hasSum hH)
  exact ((h₁.mul_left 2).add (h₂.mul_left 2)).add h₃

/-- Each image keeps its own normal. This is a fixed-cutoff series, not a uniform budget. -/
theorem hasSum_radialCurvature_images (N n : ℕ) (e : R3) (he : ‖e‖ = 1)
    {q : T3} (hq : q ≠ 0) (a b v w : R3) :
    HasSum (fun z : Lat ↦
      RadialRieszRegularization.radialCoefficient N e (UnitTorusSchwartzLattice.displacement q z) *
        radialCurvature n a b (UnitTorusSchwartzLattice.displacement q z) v w)
      (pairedCurvature n (PeriodicRadialRiesz.tensor N q) a b v w) := by
  apply (hasSum_pairedCurvature n (PeriodicRadialRiesz.hasSum_tensor_images N hq) a b v w).congr_fun
  intro z
  exact (pairedCurvature_tensor N n e he (UnitTorusSchwartzLattice.displacement_ne_zero hq z) a b v w).symm

end Mettapedia.Analysis.RadialPancakeCurvature
