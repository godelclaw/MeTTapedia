import Mettapedia.Analysis.PeriodicRadialRieszSolenoidal
import Mettapedia.Analysis.UnitTorusConvolutionEnergy
import Mettapedia.Analysis.UnitTorusKernelCorrelation
import Mettapedia.Analysis.OcticKernelCorrelation

/-!
# An eighth-order endpoint correlation for the radial Riesz operator

The quartic tensor at the source is paired with the regularized Riesz transform
of the fourth power of the receiving vorticity. The correlation is bounded by
the eighth moment, uniformly in the cutoff. This is a size bound, not a sign
or monotonicity assertion about its evolution.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.PeriodicRadialRiesz

open MeasureTheory UnitTorusConvolutionEnergy
open scoped RealInnerProductSpace
variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)
local notation "Td" => UnitAddTorus (Fin d)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem abs_rieszEntry_le_one (i j : Fin d) (x : Rd) :
    |AnnularRieszKernel.rieszEntry i j x| ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx, AnnularRieszKernel.rieszEntry]
  have hi : |x i| ≤ ‖x‖ := PiLp.norm_apply_le x i
  have hj : |x j| ≤ ‖x‖ := PiLp.norm_apply_le x j
  rw [AnnularRieszKernel.rieszEntry, abs_div, abs_mul, abs_pow, abs_norm,
    div_le_one (sq_pos_of_pos (norm_pos_iff.mpr hx))]
  simpa only [pow_two] using mul_le_mul hi hj (abs_nonneg _) (norm_nonneg _)

theorem continuous_entry (N : ℕ) (i j : Fin d) : Continuous (entry N i j) :=
  UnitTorusSchwartzLattice.continuous_periodize _

theorem norm_mFourierCoeff_re_entry_le_one (N : ℕ) (i j : Fin d) (k : Fin d → ℤ) :
    ‖UnitAddTorus.mFourierCoeff (fun x ↦ ((entry N i j x).re : ℂ)) k‖ ≤ 1 := by
  rw [mFourierCoeff_re_entry, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (RadialRieszRegularization.weight_nonneg _ _)]
  exact (mul_le_mul_of_nonneg_left (abs_rieszEntry_le_one i j _)
    (RadialRieszRegularization.weight_nonneg _ _)).trans
      (by simpa only [mul_one] using RadialRieszRegularization.weight_le_one N _)

theorem integral_re_entry_convolution_sq_le (N : ℕ) (i j : Fin d)
    (f : Td → ℝ) (hf : Continuous f) :
    (∫ x : Td, realConvolution (fun h ↦ (entry N i j h).re) f x ^ 2) ≤
      ∫ x : Td, f x ^ 2 :=
  integral_realConvolution_sq_le _ f (Complex.continuous_re.comp (continuous_entry N i j)) hf
    (norm_mFourierCoeff_re_entry_le_one N i j)

def quarticTensorEntry (a : Rd) (i j : Fin d) : ℝ := ‖a‖ ^ 2 * a i * a j

theorem abs_quarticTensorEntry_le (a : Rd) (i j : Fin d) :
    |quarticTensorEntry a i j| ≤ ‖a‖ ^ 4 := by
  have hi : |a i| ≤ ‖a‖ := PiLp.norm_apply_le a i
  have hj : |a j| ≤ ‖a‖ := PiLp.norm_apply_le a j
  rw [quarticTensorEntry, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ (‖a‖ ^ 2 * ‖a‖) * ‖a‖ :=
      mul_le_mul (mul_le_mul_of_nonneg_left hi (sq_nonneg _)) hj (abs_nonneg _)
        (by positivity)
    _ = _ := by ring

theorem continuous_quarticTensorEntry (w : Td → Rd) (hw : Continuous w) (i j : Fin d) :
    Continuous (fun x ↦ quarticTensorEntry (w x) i j) :=
  ((hw.norm.pow 2).mul ((PiLp.continuous_apply 2 (fun _ : Fin d ↦ ℝ) i).comp hw)).mul
    ((PiLp.continuous_apply 2 (fun _ : Fin d ↦ ℝ) j).comp hw)

def eighthMoment (w : Td → Rd) : ℝ := ∫ x : Td, ‖w x‖ ^ 8

def correlationEntry (N : ℕ) (w : Td → Rd) (i j : Fin d) : ℝ :=
  ∫ x : Td, quarticTensorEntry (w x) i j *
    realConvolution (fun h ↦ (entry N i j h).re) (fun y ↦ ‖w y‖ ^ 4) x

def octicCorrelation (N : ℕ) (w : Td → Rd) : ℝ := ∑ i, ∑ j, correlationEntry N w i j

theorem abs_correlationEntry_le (N : ℕ) (w : Td → Rd) (hw : Continuous w) (i j : Fin d) :
    |correlationEntry N w i j| ≤ eighthMoment w := by
  have hq := continuous_quarticTensorEntry w hw i j
  have hi (v : Td → ℝ) (hv : Continuous v) : Integrable v :=
    hv.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsq : (∫ x : Td, quarticTensorEntry (w x) i j ^ 2) ≤ eighthMoment w := by
    apply integral_mono (hi _ (hq.pow 2)) (hi _ (hw.norm.pow 8))
    intro x
    change quarticTensorEntry (w x) i j ^ 2 ≤ ‖w x‖ ^ 8
    have h := pow_le_pow_left₀ (abs_nonneg _) (abs_quarticTensorEntry_le (w x) i j) 2
    simpa only [sq_abs, ← pow_mul] using h
  have h := abs_integral_mul_realConvolution_le _ _ _ (Complex.continuous_re.comp (continuous_entry N i j))
    (hw.norm.pow 4) hq (norm_mFourierCoeff_re_entry_le_one N i j)
  change |correlationEntry N w i j| ≤ _ at h
  simp only [Pi.pow_apply, ← pow_mul] at h
  change |correlationEntry N w i j| ≤ ((∫ x : Td, quarticTensorEntry (w x) i j ^ 2) +
    eighthMoment w) / 2 at h
  linarith

theorem abs_octicCorrelation_le (N : ℕ) (w : Td → Rd) (hw : Continuous w) :
    |octicCorrelation N w| ≤ (d : ℝ) ^ 2 * eighthMoment w := by
  calc
    _ ≤ ∑ i : Fin d, ∑ j : Fin d, |correlationEntry N w i j| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun i _ ↦ Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i : Fin d, ∑ j : Fin d, eighthMoment w :=
      Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum (fun j _ ↦ abs_correlationEntry_le N w hw i j))
    _ = _ := by simp [pow_two, mul_assoc]

theorem octic_correction_bounds (N : ℕ) (w : Td → Rd) (hw : Continuous w) (ε : ℝ) :
    (1 - |ε| * (d : ℝ) ^ 2) * eighthMoment w ≤ eighthMoment w + ε * octicCorrelation N w ∧
      eighthMoment w + ε * octicCorrelation N w ≤ (1 + |ε| * (d : ℝ) ^ 2) * eighthMoment w := by
  have h := mul_le_mul_of_nonneg_left (abs_octicCorrelation_le N w hw) (abs_nonneg ε)
  rw [← abs_mul, abs_le] at h
  constructor <;> nlinarith [h.1, h.2]

theorem integral_quadratic_tensor_eq_zero (N : ℕ) (x : Td) (a : Rd) :
    (∫ y : Td, ⟪a, tensor N (x - y) a⟫) = 0 := by
  rw [UnitTorusKernelCorrelation.integral_quadratic_eq_mean _ (continuous_tensor N),
    integral_tensor_eq_zero]
  simp

theorem integral_weighted_quadratic_tensor_eq_increment (N : ℕ) (w : Td → ℝ)
    (hw : Continuous w) (x : Td) (a : Rd) :
    (∫ y : Td, w y * ⟪a, tensor N (x - y) a⟫) =
      ∫ y : Td, (w y - w x) * ⟪a, tensor N (x - y) a⟫ :=
  UnitTorusKernelCorrelation.integral_weighted_quadratic_eq_increment _
    (continuous_tensor N) (integral_tensor_eq_zero N) w hw x a

theorem bilinear_tensor_eq_sum (N : ℕ) (q : Td) (a b : Rd) :
    ⟪a, tensor N q b⟫ = ∑ i : Fin d, ∑ j : Fin d, (entry N i j q).re * a i * b j := by
  simp only [PiLp.inner_apply, tensor_apply_component, Real.inner_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quadratic_tensor_eq_sum (N : ℕ) (q : Td) (a : Rd) :
    ⟪a, tensor N q a⟫ = ∑ i : Fin d, ∑ j : Fin d, (entry N i j q).re * a i * a j :=
  bilinear_tensor_eq_sum N q a a

theorem octicCorrelation_eq_pairIntegral (N : ℕ) (w : Td → Rd) (hw : Continuous w) :
    octicCorrelation N w =
      ∫ x : Td, ∫ y : Td, OcticKernelCorrelation.density (tensor N (x - y)) (w x) (w y) := by
  have hi (v : Td → ℝ) (hv : Continuous v) : Integrable v :=
    hv.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hentry (i j : Fin d) : Continuous (fun x : Td ↦ quarticTensorEntry (w x) i j *
      realConvolution (fun h ↦ (entry N i j h).re) (fun y ↦ ‖w y‖ ^ 4) x) :=
    (continuous_quarticTensorEntry w hw i j).mul (continuous_realConvolution _ _
      (Complex.continuous_re.comp (continuous_entry N i j)) (hw.norm.pow 4))
  unfold octicCorrelation correlationEntry
  simp_rw [← integral_finsetSum _ (fun j _ ↦ hi _ (hentry _ j))]
  rw [← integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hi _ (hentry i j)))]
  apply integral_congr_ae
  filter_upwards [] with x
  have hre (i j : Fin d) :
      realConvolution (fun h ↦ (entry N i j h).re) (fun y ↦ ‖w y‖ ^ 4) x =
        ∫ y : Td, (entry N i j (x - y)).re * ‖w y‖ ^ 4 := by
    unfold realConvolution
    rw [← integral_sub_left_eq_self (fun h : Td ↦ (entry N i j h).re * ‖w (x - h)‖ ^ 4) volume x]
    simp only [sub_sub_cancel]
  simp_rw [hre, ← integral_const_mul]
  have hterm (i j : Fin d) : Integrable (fun y : Td ↦ quarticTensorEntry (w x) i j *
      ((entry N i j (x - y)).re * ‖w y‖ ^ 4)) :=
    hi _ (continuous_const.mul (((Complex.continuous_re.comp (continuous_entry N i j)).comp
      (continuous_const.sub continuous_id)).mul (hw.norm.pow 4)))
  simp_rw [← integral_finsetSum _ (fun j _ ↦ hterm _ j)]
  rw [← integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hterm i j))]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [OcticKernelCorrelation.density, quadratic_tensor_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold quarticTensorEntry
  ring

end Mettapedia.Analysis.PeriodicRadialRiesz
