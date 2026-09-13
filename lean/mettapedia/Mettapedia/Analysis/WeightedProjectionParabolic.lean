import Mettapedia.Analysis.RegularizedProjectionParabolic

/-!
# Diffusion curvature of the sixth-power-weighted projection

The changing weight contributes both radial curvature and a mixed term.
Completing that mixed term as a square keeps the moving-center gradient
explicit. None of these identities asserts that the curvature is nonnegative.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.WeightedProjectionParabolic

open scoped RealInnerProductSpace
open RegularizedProjection RegularizedProjectionParabolic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def weightedEnergy (δ : ℝ) (a b : E) : ℝ := ‖a‖ ^ 6 * energy δ a b

def weightedRate (δ : ℝ) (a b v z : E) : ℝ :=
  6 * ‖a‖ ^ 4 * ⟪a, v⟫ * energy δ a b + ‖a‖ ^ 6 * energyRate δ a b v z

def weightedCurvature (δ : ℝ) (a b v z : E) : ℝ :=
  (24 * ‖a‖ ^ 2 * ⟪a, v⟫ ^ 2 + 6 * ‖a‖ ^ 4 * ‖v‖ ^ 2) * energy δ a b +
    12 * ‖a‖ ^ 4 * ⟪a, v⟫ * energyRate δ a b v z +
    ‖a‖ ^ 6 * energyCurvature δ a b v z

theorem hasDerivAt_weightedEnergy (δ : ℝ) (hδ : 0 < δ)
    {a b : ℝ → E} {v z : E} {t : ℝ} (ha : HasDerivAt a v t) (hb : HasDerivAt b z t) :
    HasDerivAt (fun τ ↦ weightedEnergy δ (a τ) (b τ)) (weightedRate δ (a t) (b t) v z) t := by
  have h := (ha.norm_sq.fun_pow 3).mul (RegularizedProjection.hasDerivAt_energy δ hδ ha hb)
  simp only [← pow_mul, Nat.reduceMul, Nat.reduceSub, Nat.cast_ofNat] at h
  apply h.congr_deriv
  unfold weightedRate energyRate
  ring

theorem hasDerivAt_weightedRate (δ : ℝ) (hδ : 0 < δ)
    {a b v z : ℝ → E} {aa bb : E} {t : ℝ}
    (ha : HasDerivAt a (v t) t) (hb : HasDerivAt b (z t) t)
    (hv : HasDerivAt v aa t) (hz : HasDerivAt z bb t) :
    HasDerivAt (fun τ ↦ weightedRate δ (a τ) (b τ) (v τ) (z τ))
      (weightedRate δ (a t) (b t) aa bb + weightedCurvature δ (a t) (b t) (v t) (z t)) t := by
  have hJ := RegularizedProjection.hasDerivAt_energy δ hδ ha hb
  have hR := hasDerivAt_energyRate δ hδ ha hb hv hz
  have h := ((((ha.norm_sq.fun_pow 2).const_mul 6).mul (ha.inner ℝ hv)).mul hJ).add
    ((ha.norm_sq.fun_pow 3).mul hR)
  simp only [← pow_mul, Nat.reduceMul, Nat.reduceSub, Nat.cast_ofNat, pow_one,
    real_inner_self_eq_norm_sq] at h
  apply h.congr_deriv
  simp only [weightedRate, weightedCurvature, energyRate, Pi.mul_apply]
  ring

/-- A division-free completion of the mixed radial/projection square,
valid also at a zero of the first field. -/
theorem weightedCurvature_eq_square (δ : ℝ) (a b v z : E) :
    weightedCurvature δ a b v z =
      2 * ‖‖a‖ ^ 3 • (z - coefficient δ a b • v) +
        (6 * ‖a‖ * ⟪a, v⟫) • residual δ a b‖ ^ 2 +
      6 * ‖a‖ ^ 4 * ‖v‖ ^ 2 * energy δ a b -
      48 * ‖a‖ ^ 2 * ⟪a, v⟫ ^ 2 * energy δ a b +
      72 * δ * ‖a‖ ^ 2 * ⟪a, v⟫ ^ 2 * coefficient δ a b ^ 2 -
      2 * ‖a‖ ^ 6 * (δ + ‖a‖ ^ 2) * coefficientRate δ a b v z ^ 2 := by
  simp only [weightedCurvature, energyRate, energyCurvature, norm_add_sq_real, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm (z - coefficient δ a b • v) (residual δ a b), energy]
  ring

/-- The remaining upper bound on viscous production has only first jets
of the two fields, but still contains the moving-center gradient. -/
theorem weightedCurvature_ge (δ : ℝ) (hδ : 0 < δ) (a b v z : E) :
    -(42 * ‖a‖ ^ 4 * ‖v‖ ^ 2 * energy δ a b) -
      2 * ‖a‖ ^ 6 * (δ + ‖a‖ ^ 2) * coefficientRate δ a b v z ^ 2 ≤
        weightedCurvature δ a b v z := by
  have hJ := energy_nonneg δ hδ.le a b
  have hcs : ⟪a, v⟫ ^ 2 ≤ ‖a‖ ^ 2 * ‖v‖ ^ 2 := by
    simpa only [sq, real_inner_self_eq_norm_sq] using real_inner_mul_inner_self_le a v
  have h := mul_le_mul_of_nonneg_left hcs
    (show 0 ≤ 48 * ‖a‖ ^ 2 * energy δ a b by positivity)
  rw [weightedCurvature_eq_square]
  have hs : 0 ≤ 2 * ‖‖a‖ ^ 3 • (z - coefficient δ a b • v) +
      (6 * ‖a‖ * ⟪a, v⟫) • residual δ a b‖ ^ 2 := by positivity
  have hr : 0 ≤ 72 * δ * ‖a‖ ^ 2 * ⟪a, v⟫ ^ 2 * coefficient δ a b ^ 2 := by positivity
  nlinarith only [h, hs, hr]

variable {X : Type*} [TopologicalSpace X]

def diffusionCost (δ : ℝ) (a b v z : E) : ℝ :=
  42 * ‖a‖ ^ 4 * ‖v‖ ^ 2 * energy δ a b +
    2 * ‖a‖ ^ 6 * (δ + ‖a‖ ^ 2) * coefficientRate δ a b v z ^ 2

theorem neg_weightedCurvature_le (δ : ℝ) (hδ : 0 < δ) (a b v z : E) :
    -weightedCurvature δ a b v z ≤ diffusionCost δ a b v z := by
  have h := weightedCurvature_ge δ hδ a b v z
  unfold diffusionCost
  linarith only [h]

theorem diffusionCost_nonneg (δ : ℝ) (hδ : 0 ≤ δ) (a b v z : E) :
    0 ≤ diffusionCost δ a b v z := by
  have hJ := energy_nonneg δ hδ a b
  unfold diffusionCost
  positivity

theorem continuous_diffusionCost (δ : ℝ) (hδ : 0 < δ) {a b v z : X → E}
    (ha : Continuous a) (hb : Continuous b) (hv : Continuous v) (hz : Continuous z) :
    Continuous (fun x ↦ diffusionCost δ (a x) (b x) (v x) (z x)) := by
  unfold diffusionCost coefficientRate energy RegularizedProjection.residual coefficient
  fun_prop (disch := intro x; positivity)

theorem continuous_weightedRate (δ : ℝ) (hδ : 0 < δ) {a b v z : X → E}
    (ha : Continuous a) (hb : Continuous b) (hv : Continuous v) (hz : Continuous z) :
    Continuous (fun x ↦ weightedRate δ (a x) (b x) (v x) (z x)) := by
  unfold weightedRate energyRate energy RegularizedProjection.residual coefficient
  fun_prop (disch := intro x; positivity)

theorem continuous_weightedCurvature (δ : ℝ) (hδ : 0 < δ) {a b v z : X → E}
    (ha : Continuous a) (hb : Continuous b) (hv : Continuous v) (hz : Continuous z) :
    Continuous (fun x ↦ weightedCurvature δ (a x) (b x) (v x) (z x)) := by
  unfold weightedCurvature energyCurvature energyRate coefficientRate energy
    RegularizedProjection.residual coefficient
  fun_prop (disch := intro x; positivity)

end Mettapedia.Analysis.WeightedProjectionParabolic
