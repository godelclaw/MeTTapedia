import MettapediaNS.WholeSpacePressureAugmentation
import MettapediaNS.PressureDiffusionCompletion
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Euler.LpBochnerRealization

/-!
# Spatial diffusion payment for the actual canonical pressure receiver

The pressure receiver `2aP` uses the Hessian of the constructed whole-fluid
pressure and the continuous soft-excess weight. Both terms in its spatial
derivative are retained. Rademacher's theorem and the minimum at zero
identify that derivative almost everywhere, including the cutoff level.

The canonical pressure-square diffusion and the perspective diffusion pay
the derivative. No division by the selector is used. The ratio's Lipschitz
constant establishes differentiability; it does not enter the payment.
This is a spatial estimate, not an arbitrary-history production bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpacePressureReceiver

open MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanClassical WholeSpaceBetchov
  MiddleEigenvalueAlgebra WholeSpacePressureAugmentation WholeSpaceViscousEnergy
  EulerMeanSolenoidal

open scoped Topology NNReal

/-- Globally Lipschitz extension of the physical selector for `b>0`.
Clamping the argument avoids a spurious singularity outside `z>0`. -/
def extendedWeight (b z : ℝ) : ℝ := 1 - b ^ 2 / (max z b) ^ 2

theorem extendedWeight_nonneg (b z : ℝ) (hb : 0 < b) :
    0 ≤ extendedWeight b z := by
  have hm : 0 < max z b := hb.trans_le (le_max_right _ _)
  have hs : b ^ 2 ≤ (max z b) ^ 2 := by gcongr; exact le_max_right _ _
  have hd := (div_le_one (sq_pos_of_pos hm)).2 hs
  unfold extendedWeight
  linarith

theorem extendedWeight_le_one (b z : ℝ) : extendedWeight b z ≤ 1 := by
  have hd : 0 ≤ b ^ 2 / (max z b) ^ 2 := by positivity
  unfold extendedWeight
  linarith

theorem extendedWeight_eq_zero (b z : ℝ) (hb : 0 < b) (hz : z ≤ b) :
    extendedWeight b z = 0 := by
  rw [extendedWeight, max_eq_right hz, div_self (pow_ne_zero 2 hb.ne')]
  ring

theorem extendedWeight_eq_active (b z : ℝ) (hb : 0 < b) :
    extendedWeight b z = if b < z then 1 - b ^ 2 / z ^ 2 else 0 := by
  split_ifs with ha
  · rw [extendedWeight, max_eq_left ha.le]
  · exact extendedWeight_eq_zero b z hb (le_of_not_gt ha)

theorem extendedWeight_eq_receiverWeight (b z : ℝ) (hb : 0 < b) (hz : 0 < z) :
    extendedWeight b z = receiverWeight b z := by
  rw [extendedWeight_eq_active b z hb, receiverWeight_eq_active b z hb.le hz]

/-- A datum-fixed Lipschitz modulus; it is not used in the diffusion cost. -/
theorem extendedWeight_lipschitz (b : ℝ) (hb : 0 < b) :
    LipschitzWith (Real.toNNReal (2 / b)) (extendedWeight b) := by
  have hr : LipschitzOnWith (Real.toNNReal (2 / b))
      (fun y : ℝ ↦ 1 - b ^ 2 / y ^ 2) (Set.Ici b) := by
    apply (convex_Ici b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun y hy ↦ (ViscousMemorySoftExcess.weight_hasDerivAt b y
        (hb.trans_le hy).ne').hasDerivWithinAt)
    intro y hy
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs,
      abs_of_nonneg (ViscousMemorySoftExcess.curvature_nonneg b y (hb.trans_le hy)),
      Real.coe_toNNReal _ (by positivity)]
    exact ViscousMemorySoftExcess.curvature_le b y hb hy
  have hm : LipschitzWith 1 (fun y : ℝ ↦ max y b) := LipschitzWith.id.max_const b
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist (extendedWeight b x) (extendedWeight b y) ≤
        (Real.toNNReal (2 / b) : ℝ) * dist (max x b) (max y b) :=
      hr.dist_le_mul (max x b) (show max x b ∈ Set.Ici b from le_max_right x b)
        (max y b) (show max y b ∈ Set.Ici b from le_max_right y b)
    _ ≤ (Real.toNNReal (2 / b) : ℝ) * dist x y := by
      gcongr
      simpa using hm.dist_le_mul x y

/-- The derivative on the active branch and zero on its complement. -/
def weightSlope (b z : ℝ) : ℝ :=
  if b < z then ViscousMemorySoftExcess.curvature b z else 0

theorem weightSlope_nonneg (b z : ℝ) (hb : 0 < b) : 0 ≤ weightSlope b z := by
  unfold weightSlope
  split_ifs with ha
  · exact ViscousMemorySoftExcess.curvature_nonneg b z (hb.trans ha)
  · rfl

/-- Where the selector is zero, it is at a minimum. The Fréchet derivative
is therefore zero whenever it exists (and is zero by definition otherwise). -/
theorem extendedWeight_fderiv (b : ℝ) (hb : 0 < b) (z : Space → ℝ)
    (x : Space) (hz : DifferentiableAt ℝ z x) :
    fderiv ℝ (fun y ↦ extendedWeight b (z y)) x =
      weightSlope b (z x) • fderiv ℝ z x := by
  by_cases ha : b < z x
  · have he : (fun y ↦ extendedWeight b (z y)) =ᶠ[𝓝 x]
        (fun y ↦ 1 - b ^ 2 / (z y) ^ 2) := by
      filter_upwards [hz.continuousAt.eventually (eventually_gt_nhds ha)] with y hy
      rw [extendedWeight, max_eq_left hy.le]
    have hd := (ViscousMemorySoftExcess.weight_hasDerivAt b (z x)
      (hb.trans ha).ne').comp_hasFDerivAt x hz.hasFDerivAt
    rw [(hd.congr_of_eventuallyEq he).fderiv, weightSlope, ite_eq_left ha]
  · have hzero := extendedWeight_eq_zero b (z x) hb (le_of_not_gt ha)
    have hmin : IsLocalMin (fun y ↦ extendedWeight b (z y)) x := by
      exact Filter.Eventually.of_forall fun y ↦ by
        change extendedWeight b (z x) ≤ extendedWeight b (z y)
        rw [hzero]
        exact extendedWeight_nonneg b (z y) hb
    rw [hmin.fderiv_eq_zero, weightSlope, ite_eq_right ha, zero_smul]

/-- The literal canonical pressure Hessian entry. -/
def pressureEntry (u : SmoothL2Field Space) (i j : Fin 3) (x : Space) : ℝ :=
  gradMatrix (pressureField u) x i j

private theorem pressureEntry_hasFDerivAt (u : SmoothL2Field Space)
    (i j : Fin 3) (x : Space) :
    HasFDerivAt (pressureEntry u i j) (fderiv ℝ (pressureEntry u i j) x) x := by
  exact ((coord ((pressureField u).directionalField (axis j)) i).smooth.differentiable
    (by simp)).differentiableAt.hasFDerivAt

theorem pressureEntry_directional (u : SmoothL2Field Space)
    (i j k : Fin 3) (x : Space) :
    fderiv ℝ (pressureEntry u i j) x (axis k) =
      gradMatrix ((pressureField u).directionalField (axis k)) x i j := by
  change fderiv ℝ (coord ((pressureField u).directionalField (axis j)) i).field x
    (axis k) = _
  rw [← directionalField_field, coord_directional_field, directionalField_comm]
  rfl

/-- Actual pressure receiver; it is continuous across the excess boundary. -/
def receiverEntry (u : SmoothL2Field Space) (b : ℝ) (z : Space → ℝ)
    (i j : Fin 3) (x : Space) : ℝ :=
  2 * extendedWeight b (z x) * pressureEntry u i j x

/-- Local Lipschitz regularity prevents the surface-measure derivative of
a discontinuous active-set selector. A weak integration-by-parts theorem
can therefore consume the almost-everywhere derivative below. -/
theorem receiverEntry_locallyLipschitz (u : SmoothL2Field Space) (b : ℝ) (hb : 0 < b)
    (z : Space → ℝ) {Kz : ℝ≥0} (hz : LipschitzWith Kz z) (i j : Fin 3) :
    LocallyLipschitz (receiverEntry u b z i j) := by
  have hw := ((extendedWeight_lipschitz b hb).comp hz).locallyLipschitz
  have hp : ContDiff ℝ 1 (pressureEntry u i j) :=
    (coord ((pressureField u).directionalField (axis j)) i).smooth.of_le (by simp)
  have hm : ContDiff ℝ 1 (fun v : ℝ × ℝ ↦ 2 * v.1 * v.2) := by fun_prop
  exact hm.locallyLipschitz.comp (hw.prodMk hp.locallyLipschitz)

/-- The receiver itself belongs to `L²` by bounded selection of the actual
pressure. Together with the derivative payment this supports its Sobolev
interpretation; the weak derivative identification remains separate. -/
theorem receiverEntry_memLp (u : SmoothL2Field Space) (b : ℝ) (hb : 0 < b)
    (z : Space → ℝ) {Kz : ℝ≥0} (hz : LipschitzWith Kz z) (i j : Fin 3) :
    MemLp (receiverEntry u b z i j) 2 volume := by
  have hp : MemLp (pressureEntry u i j) 2 volume :=
    (coord ((pressureField u).directionalField (axis j)) i).memLp
  have hc : Continuous (receiverEntry u b z i j) := by
    exact ((continuous_const.mul ((extendedWeight_lipschitz b hb).continuous.comp
      hz.continuous)).mul
      (coord ((pressureField u).directionalField (axis j)) i).smooth.continuous)
  apply hp.of_le_mul hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x ↦ by
    change ‖2 * extendedWeight b (z x) * pressureEntry u i j x‖ ≤
      2 * ‖pressureEntry u i j x‖
    rw [norm_mul, norm_mul, Real.norm_eq_abs (extendedWeight b (z x)),
      abs_of_nonneg (extendedWeight_nonneg b (z x) hb)]
    norm_num
    have hm := mul_le_mul_of_nonneg_right (extendedWeight_le_one b (z x))
      (abs_nonneg (pressureEntry u i j x))
    nlinarith only [hm]

/-- Fréchet spatial derivative of the constructed receiver, not a free jet. -/
def receiverDirectional (u : SmoothL2Field Space) (b : ℝ) (z : Space → ℝ)
    (k : Fin 3) (x : Space) : GradMatrix :=
  fun i j ↦ fderiv ℝ (receiverEntry u b z i j) x (axis k)

/-- The product rule holds almost everywhere, including points on `z=b`.
Neither a zero-measure level-set hypothesis nor a smooth selector is used. -/
theorem receiverDirectional_eq_ae (u : SmoothL2Field Space) (b : ℝ) (hb : 0 < b)
    (z : Space → ℝ) {Kz : ℝ≥0} (hz : LipschitzWith Kz z) (k : Fin 3) :
    ∀ᵐ x, receiverDirectional u b z k x = fun i j ↦
      2 * extendedWeight b (z x) *
        gradMatrix ((pressureField u).directionalField (axis k)) x i j +
      2 * pressureEntry u i j x * weightSlope b (z x) * fderiv ℝ z x (axis k) := by
  have hw := (extendedWeight_lipschitz b hb).comp hz
  filter_upwards [hz.ae_differentiableAt, hw.ae_differentiableAt] with x hzx hwx
  funext i j
  have hd := (hwx.hasFDerivAt.const_mul 2).mul (pressureEntry_hasFDerivAt u i j x)
  have he := congrArg (fun L : Space →L[ℝ] ℝ ↦ L (axis k)) hd.fderiv
  change fderiv ℝ (receiverEntry u b z i j) x (axis k) =
    ((2 * extendedWeight b (z x)) • fderiv ℝ (pressureEntry u i j) x +
      pressureEntry u i j x • 2 • fderiv ℝ (fun y ↦ extendedWeight b (z y)) x)
        (axis k) at he
  simp only [add_apply, smul_apply, smul_eq_mul, extendedWeight_fderiv b hb z x hzx,
    pressureEntry_directional u i j k x] at he
  change fderiv ℝ (receiverEntry u b z i j) x (axis k) = _
  rw [he]
  ring

private theorem receiver_normSq_le (P PP : GradMatrix) (a c g : ℝ) :
    normSq (fun i j ↦ 2 * a * PP i j + 2 * P i j * c * g) ≤
      8 * a ^ 2 * normSq PP + 8 * c ^ 2 * g ^ 2 * normSq P := by
  calc
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
        (8 * a ^ 2 * (PP i j) ^ 2 + 8 * c ^ 2 * g ^ 2 * (P i j) ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      nlinarith [sq_nonneg (a * PP i j - P i j * c * g)]
    _ = _ := by simp only [normSq, Fin.sum_univ_three]; ring

/-- Diffusion payment for both literal derivative terms. `|P|²≤hz` comes
from retaining the canonical pressure square in the augmented observable. -/
theorem receiver_jet_paid (P PP : GradMatrix) (ν h b z g : ℝ)
    (hν : 0 ≤ ν) (hh : 0 ≤ h) (hb : 0 < b) (hP : normSq P ≤ h * z) :
    ν * normSq (fun i j ↦ 2 * extendedWeight b z * PP i j +
      2 * P i j * weightSlope b z * g) ≤
      8 * ν * extendedWeight b z * normSq PP +
        16 * ν * h * weightSlope b z * g ^ 2 := by
  by_cases ha : b < z
  · have h0 := extendedWeight_nonneg b z hb
    have h1 := extendedWeight_le_one b z
    have ha₂ : (extendedWeight b z) ^ 2 ≤ extendedWeight b z := by nlinarith
    have hc := ViscousMemorySoftExcess.curvature_nonneg b z (hb.trans ha)
    have hscale := PressureDiffusionCompletion.receiver_weight_scale b z hb ha.le
    have hm := mul_le_mul_of_nonneg_left
      (receiver_normSq_le P PP (extendedWeight b z)
        (ViscousMemorySoftExcess.curvature b z) g) hν
    rw [weightSlope, ite_eq_left ha]
    have hp := mul_le_mul_of_nonneg_left hP
      (show 0 ≤ 8 * ν * (ViscousMemorySoftExcess.curvature b z) ^ 2 * g ^ 2 by positivity)
    have hs := mul_le_mul_of_nonneg_right hscale
      (show 0 ≤ 8 * ν * h * ViscousMemorySoftExcess.curvature b z * g ^ 2 by positivity)
    have hn : 0 ≤ normSq PP := by simp only [normSq]; positivity
    have hw := mul_le_mul_of_nonneg_right ha₂ (show 0 ≤ 8 * ν * normSq PP by positivity)
    nlinarith only [hm, hp, hs, hw]
  · rw [extendedWeight_eq_zero b z hb (le_of_not_gt ha), weightSlope, ite_eq_right ha]
    simp [normSq]

/-- Native perspective diffusion in a coordinate direction. -/
def selectionDiffusion (ν : ℝ) (h z : Space → ℝ) (b : ℝ)
    (k : Fin 3) (x : Space) : ℝ :=
  ν * h x * weightSlope b (z x) * (fderiv ℝ z x (axis k)) ^ 2

/-- Actual almost-everywhere derivative estimate on a smooth fluid slice.
The ratio regularity is explicit; no unknown future bound enters the cost. -/
theorem receiverDirectional_paid_ae (u : SmoothL2Field Space) (ν b : ℝ)
    (hν : 0 ≤ ν) (hb : 0 < b) (h z : Space → ℝ) (hh : ∀ x, 0 ≤ h x)
    {Kz : ℝ≥0} (hz : LipschitzWith Kz z)
    (hP : ∀ x, pressureSquare u x ≤ h x * z x) (k : Fin 3) :
    ∀ᵐ x, ν * normSq (receiverDirectional u b z k x) ≤
      8 * ν * extendedWeight b (z x) *
        normSq (gradMatrix ((pressureField u).directionalField (axis k)) x) +
      16 * selectionDiffusion ν h z b k x := by
  filter_upwards [receiverDirectional_eq_ae u b hb z hz k] with x hx
  rw [hx]
  simpa only [pressureEntry, selectionDiffusion, mul_assoc] using
    receiver_jet_paid (gradMatrix (pressureField u) x)
      (gradMatrix ((pressureField u).directionalField (axis k)) x)
      ν (h x) b (z x) (fderiv ℝ z x (axis k)) hν (hh x) hb (hP x)

theorem receiverDirectional_normSq_measurable (u : SmoothL2Field Space)
    (b : ℝ) (z : Space → ℝ) (k : Fin 3) :
    Measurable (fun x ↦ normSq (receiverDirectional u b z k x)) := by
  unfold normSq receiverDirectional
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  exact (measurable_fderiv_apply_const ℝ (receiverEntry u b z i j) (axis k)).pow_const 2

private theorem selected_pressure_gradient_integrable (u : SmoothL2Field Space)
    (b : ℝ) (hb : 0 < b) (z : Space → ℝ) {Kz : ℝ≥0}
    (hz : LipschitzWith Kz z) (k : Fin 3) :
    Integrable (fun x ↦ extendedWeight b (z x) *
      normSq (gradMatrix ((pressureField u).directionalField (axis k)) x)) := by
  apply (WholeSpaceBetchov.normSq_integrable
    ((pressureField u).directionalField (axis k))).bdd_mul
      ((extendedWeight_lipschitz b hb).continuous.comp hz.continuous).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x ↦ by
    simpa only [Function.comp_apply, Real.norm_eq_abs,
      abs_of_nonneg (extendedWeight_nonneg b (z x) hb)]
      using extendedWeight_le_one b (z x)

/-- The literal receiver derivative is integrable when the native
perspective diffusion is integrable. Receiver integrability is concluded,
not smuggled into the hypotheses of the integral comparison. -/
theorem receiverDirectional_cost_integrable (u : SmoothL2Field Space) (ν b : ℝ)
    (hν : 0 ≤ ν) (hb : 0 < b) (h z : Space → ℝ) (hh : ∀ x, 0 ≤ h x)
    {Kz : ℝ≥0} (hz : LipschitzWith Kz z)
    (hP : ∀ x, pressureSquare u x ≤ h x * z x) (k : Fin 3)
    (hJ : Integrable (selectionDiffusion ν h z b k)) :
    Integrable (fun x ↦ ν * normSq (receiverDirectional u b z k x)) := by
  have hmajor := ((selected_pressure_gradient_integrable u b hb z hz k).const_mul
    (8 * ν)).add (hJ.const_mul 16)
  apply hmajor.mono_nonneg
    ((measurable_const.mul (receiverDirectional_normSq_measurable u b z k)).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall fun x ↦ by
      apply mul_nonneg hν
      simp only [normSq]
      positivity
  · simpa only [Pi.mul_apply, Pi.add_apply, mul_assoc] using
      receiverDirectional_paid_ae u ν b hν hb h z hh hz hP k

/-- Integrated spatial payment by the actual canonical pressure-square
diffusion and the native perspective diffusion. -/
theorem integral_receiverDirectional_paid (u : SmoothL2Field Space) (ν b : ℝ)
    (hν : 0 ≤ ν) (hb : 0 < b) (h z : Space → ℝ) (hh : ∀ x, 0 ≤ h x)
    {Kz : ℝ≥0} (hz : LipschitzWith Kz z)
    (hP : ∀ x, pressureSquare u x ≤ h x * z x) (k : Fin 3)
    (hJ : Integrable (selectionDiffusion ν h z b k)) :
    (∫ x, ν * normSq (receiverDirectional u b z k x)) ≤
      8 * ν * (∫ x, extendedWeight b (z x) *
        normSq (gradMatrix ((pressureField u).directionalField (axis k)) x)) +
      16 * ∫ x, selectionDiffusion ν h z b k x := by
  have hp := (selected_pressure_gradient_integrable u b hb z hz k).const_mul (8 * ν)
  have hi := integral_mono_ae
    (receiverDirectional_cost_integrable u ν b hν hb h z hh hz hP k hJ)
    (hp.add (hJ.const_mul 16))
    (show ∀ᵐ x, ν * normSq (receiverDirectional u b z k x) ≤
        (8 * ν) * (extendedWeight b (z x) *
          normSq (gradMatrix ((pressureField u).directionalField (axis k)) x)) +
        16 * selectionDiffusion ν h z b k x from by
      simpa only [mul_assoc] using receiverDirectional_paid_ae u ν b hν hb h z hh hz hP k)
  simpa only [Pi.add_apply, integral_add hp (hJ.const_mul 16), integral_const_mul] using hi

/-- Retaining the actual pressure square supplies the required bound for
the physical augmented ratio. Positivity of the older observable is explicit. -/
theorem pressureSquare_le_augmented_ratio (u : SmoothL2Field Space)
    (X h : Space → ℝ) (hX : ∀ x, 0 ≤ X x) (hh : ∀ x, 0 < h x) (x : Space) :
    pressureSquare u x ≤ h x * (augmented u X x / h x) := by
  rw [mul_div_cancel₀ _ (hh x).ne']
  unfold augmented
  linarith [hX x]

/-- The actual divergence of the receiver's almost-everywhere spatial jet. -/
def receiverDivergence (u : SmoothL2Field Space) (b : ℝ) (z : Space → ℝ)
    (x : Space) : Space :=
  ∑ i : Fin 3, (∑ j : Fin 3, receiverDirectional u b z j x i j) • axis i

theorem receiverDivergence_measurable (u : SmoothL2Field Space) (b : ℝ)
    (z : Space → ℝ) : Measurable (receiverDivergence u b z) := by
  unfold receiverDivergence
  apply Finset.measurable_sum
  intro i _
  have hs : Measurable (fun x ↦ ∑ j : Fin 3, receiverDirectional u b z j x i j) := by
    apply Finset.measurable_sum
    intro j _
    exact measurable_fderiv_apply_const ℝ (receiverEntry u b z i j) (axis j)
  exact (ContinuousLinearMap.toSpanSingleton ℝ (axis i)).continuous.measurable.comp hs

private theorem three_sum_sq_le (v : Fin 3 → ℝ) :
    (∑ i, v i) ^ 2 ≤ 3 * ∑ i, (v i) ^ 2 := by
  simp only [Fin.sum_univ_three]
  nlinarith [sq_nonneg (v 0 - v 1), sq_nonneg (v 0 - v 2), sq_nonneg (v 1 - v 2)]

theorem receiverDivergence_norm_sq_le (u : SmoothL2Field Space) (b : ℝ)
    (z : Space → ℝ) (x : Space) :
    ‖receiverDivergence u b z x‖ ^ 2 ≤
      3 * ∑ k : Fin 3, normSq (receiverDirectional u b z k x) := by
  have hcoord (i : Fin 3) : receiverDivergence u b z x i =
      ∑ j : Fin 3, receiverDirectional u b z j x i j := by
    simp [receiverDivergence, axis, Fin.sum_univ_three]
    fin_cases i <;> simp
  rw [EuclideanSpace.real_norm_sq_eq]
  simp_rw [hcoord]
  calc
    _ ≤ ∑ i : Fin 3, 3 * ∑ k : Fin 3, (receiverDirectional u b z k x i k) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact three_sum_sq_le _
    _ = 3 * ∑ k : Fin 3, ∑ i : Fin 3, (receiverDirectional u b z k x i k) ^ 2 := by
      simp only [Fin.sum_univ_three]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro i _
      exact Finset.single_le_sum (fun j _ ↦ sq_nonneg _) (Finset.mem_univ k)

/-- With positive viscosity, the diffusion payment constructs the actual
receiver divergence in `L²`; its membership is not a free assumption. -/
theorem receiverDivergence_memLp (u : SmoothL2Field Space) (ν b : ℝ)
    (hν : 0 < ν) (hb : 0 < b) (h z : Space → ℝ) (hh : ∀ x, 0 ≤ h x)
    {Kz : ℝ≥0} (hz : LipschitzWith Kz z)
    (hP : ∀ x, pressureSquare u x ≤ h x * z x)
    (hJ : ∀ k : Fin 3, Integrable (selectionDiffusion ν h z b k)) :
    MemLp (receiverDivergence u b z) 2 volume := by
  have hi (k : Fin 3) : Integrable (fun x ↦ normSq (receiverDirectional u b z k x)) := by
    have hp := (receiverDirectional_cost_integrable u ν b hν.le hb h z hh hz hP k
      (hJ k)).const_mul (1 / ν)
    convert! hp using 1
    funext x
    field_simp
  apply (memLp_two_iff_integrable_sq_norm
    (receiverDivergence_measurable u b z).aestronglyMeasurable).2
  apply ((integrable_finsetSum Finset.univ (fun k _ ↦ hi k)).const_mul 3).mono_nonneg
    ((receiverDivergence_measurable u b z).norm.pow_const 2).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x ↦ sq_nonneg _
  · exact Filter.Eventually.of_forall fun x ↦ receiverDivergence_norm_sq_le u b z x

/-- Canonical pressure component of the actual `L²` receiver divergence.
The minus sign matches `-Δq = div div N` and the fluid pressure operator.
Identifying this with a weak Poisson potential additionally uses the weak
integration-by-parts interpretation of the Lipschitz receiver. -/
def receiverPressureGradient (u : SmoothL2Field Space) (b : ℝ) (z : Space → ℝ)
    (hd : MemLp (receiverDivergence u b z) 2 volume) : L2 :=
  -gradientSpace.starProjection (hd.toLp (receiverDivergence u b z))

theorem receiverPressureGradient_mem_gradient (u : SmoothL2Field Space)
    (b : ℝ) (z : Space → ℝ) (hd : MemLp (receiverDivergence u b z) 2 volume) :
    receiverPressureGradient u b z hd ∈ gradientSpace :=
  gradientSpace.neg_mem (gradientSpace.starProjection_apply_mem _)

/-- This is the same ordinary Helmholtz pressure component as in the
fluid operator, applied to the receiver divergence. -/
theorem receiverPressureGradient_helmholtz (u : SmoothL2Field Space)
    (b : ℝ) (z : Space → ℝ) (hd : MemLp (receiverDivergence u b z) 2 volume) :
    receiverPressureGradient u b z hd =
      solenoidalProjection (hd.toLp (receiverDivergence u b z)) -
        hd.toLp (receiverDivergence u b z) := by
  unfold receiverPressureGradient solenoidalProjection
  have hp := Submodule.starProjection_orthogonal gradientSpace
  have he := congrArg (fun L : L2 →L[ℝ] L2 ↦ L (hd.toLp (receiverDivergence u b z))) hp
  change solenoidalSpace.starProjection (hd.toLp (receiverDivergence u b z)) =
    hd.toLp (receiverDivergence u b z) -
      gradientSpace.starProjection (hd.toLp (receiverDivergence u b z)) at he
  rw [he]
  abel

/-- The nonlocal projection preserves the unweighted diffusion payment.
The anisotropic memory-weighted pressure norm is a separate obligation. -/
theorem receiverPressureGradient_paid (u : SmoothL2Field Space) (ν b : ℝ)
    (hν : 0 < ν) (hb : 0 < b) (h z : Space → ℝ) (hh : ∀ x, 0 ≤ h x)
    {Kz : ℝ≥0} (hz : LipschitzWith Kz z)
    (hP : ∀ x, pressureSquare u x ≤ h x * z x)
    (hJ : ∀ k : Fin 3, Integrable (selectionDiffusion ν h z b k)) :
    ν * ‖receiverPressureGradient u b z
      (receiverDivergence_memLp u ν b hν hb h z hh hz hP hJ)‖ ^ 2 ≤
      3 * ∑ k : Fin 3,
        (8 * ν * (∫ x, extendedWeight b (z x) *
          normSq (gradMatrix ((pressureField u).directionalField (axis k)) x)) +
        16 * ∫ x, selectionDiffusion ν h z b k x) := by
  let hd := receiverDivergence_memLp u ν b hν hb h z hh hz hP hJ
  have he : ‖hd.toLp (receiverDivergence u b z)‖ ^ 2 =
      ∫ x, ‖receiverDivergence u b z x‖ ^ 2 := by
    rw [EulerLpBochnerRealization.norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [hd.coeFn_toLp] with x hx
    rw [hx]
  have hi (k : Fin 3) := receiverDirectional_cost_integrable
    u ν b hν.le hb h z hh hz hP k (hJ k)
  have hid := (memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).1 hd
  have hdiv : ν * (∫ x, ‖receiverDivergence u b z x‖ ^ 2) ≤
      3 * ∑ k : Fin 3, ∫ x, ν * normSq (receiverDirectional u b z k x) := by
    rw [← integral_const_mul, ← integral_finsetSum _ (fun k _ ↦ hi k),
      ← integral_const_mul]
    apply integral_mono (hid.const_mul ν)
      ((integrable_finsetSum _ (fun k _ ↦ hi k)).const_mul 3)
    intro x
    have hp := mul_le_mul_of_nonneg_left (receiverDivergence_norm_sq_le u b z x) hν.le
    simpa only [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using hp
  calc
    _ ≤ ν * ‖hd.toLp (receiverDivergence u b z)‖ ^ 2 := by
      simp only [receiverPressureGradient, norm_neg]
      apply mul_le_mul_of_nonneg_left _ hν.le
      exact pow_le_pow_left₀ (norm_nonneg _) (gradientSpace.norm_starProjection_apply_le _) 2
    _ = ν * (∫ x, ‖receiverDivergence u b z x‖ ^ 2) := by rw [he]
    _ ≤ 3 * ∑ k : Fin 3, ∫ x, ν * normSq (receiverDirectional u b z k x) := hdiv
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun k _ ↦
        integral_receiverDirectional_paid u ν b hν.le hb h z hh hz hP k (hJ k)

end Mettapedia.FluidDynamics.NavierStokes.WholeSpacePressureReceiver
