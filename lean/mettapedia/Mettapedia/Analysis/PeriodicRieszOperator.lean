import Mettapedia.Analysis.PeriodicRieszKernel
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Real even operator kernels with resolution-independent second moments

The scalar Riesz entries assemble into actual operators on Euclidean space.
Taking real parts and averaging opposite displacements preserves the second
moment bound and gives exact evenness. The bound depends on the dimension
and fixed annular kernels, not on the cutoff or on a velocity field.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.PeriodicRieszOperator

open MeasureTheory
variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)
local notation "Td" => UnitAddTorus (Fin d)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : Measure.IsNegInvariant (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsNegInvariant AddCircle.haarAddCircle)

def basisOperator (i j : Fin d) : Rd →L[ℝ] Rd :=
  InnerProductSpace.rankOne ℝ (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

@[simp] theorem norm_basisOperator (i j : Fin d) : ‖basisOperator i j‖ = 1 := by
  simp [basisOperator]

def rawKernel (N : ℕ) (x : Td) : Rd →L[ℝ] Rd :=
  ∑ i, ∑ j, (PeriodicRieszKernel.kernel i j N x).re • basisOperator i j

def kernel (N : ℕ) (x : Td) : Rd →L[ℝ] Rd :=
  (1 / 2 : ℝ) • (rawKernel N x + rawKernel N (-x))

@[simp] theorem kernel_neg (N : ℕ) (x : Td) : kernel N (-x) = kernel N x := by
  simp only [kernel, neg_neg, add_comm]

theorem kernel_sub_swap (N : ℕ) (x y : Td) : kernel N (y - x) = kernel N (x - y) := by
  rw [← neg_sub x y, kernel_neg]

theorem measurable_rawKernel (N : ℕ) : Measurable (rawKernel (d := d) N) := by
  unfold rawKernel
  exact Finset.measurable_sum _ (fun i _ ↦ Finset.measurable_sum _ (fun j _ ↦
    (Complex.continuous_re.measurable.comp (PeriodicRieszKernel.measurable_kernel i j N)).smul_const
      (basisOperator i j)))

theorem norm_rawKernel_le (N : ℕ) (x : Td) :
    ‖rawKernel N x‖ ≤ ∑ i : Fin d, ∑ j : Fin d, ‖PeriodicRieszKernel.kernel i j N x‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ ↦ ?_))
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ ↦ ?_))
  simp only [norm_smul, norm_basisOperator, mul_one, Real.norm_eq_abs]
  exact Complex.abs_re_le_norm _

theorem integrable_rawKernel (N : ℕ) : Integrable (rawKernel (d := d) N) := by
  have hi := integrable_finsetSum Finset.univ (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) ↦
    integrable_finsetSum Finset.univ (fun j _ ↦ (PeriodicRieszKernel.integrable_kernel i j N).norm))
  exact hi.mono' (measurable_rawKernel N).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_rawKernel_le N))

theorem integrable_rawSecondMoment (N : ℕ) :
    Integrable (fun x : Td ↦ ‖x‖ ^ 2 * ‖rawKernel N x‖) := by
  have hi := integrable_finsetSum Finset.univ (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) ↦
    integrable_finsetSum Finset.univ (fun j _ ↦ PeriodicRieszKernel.integrable_secondMoment i j N))
  apply hi.mono' (((continuous_norm.pow 2).measurable.mul (measurable_rawKernel N).norm).aestronglyMeasurable)
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (by positivity)]
  simpa only [Finset.mul_sum] using mul_le_mul_of_nonneg_left (norm_rawKernel_le N x) (sq_nonneg ‖x‖)

def secondMomentBound (d : ℕ) : ℝ :=
  (16 / 3 : ℝ) * ∑ i : Fin d, ∑ j : Fin d, AnnularRieszKernel.secondMoment i j

theorem secondMomentBound_nonneg (d : ℕ) : 0 ≤ secondMomentBound d := by
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦
    AnnularRieszKernel.secondMoment_nonneg i j))

theorem rawSecondMoment_le (N : ℕ) :
    (∫ x : Td, ‖x‖ ^ 2 * ‖rawKernel N x‖) ≤ secondMomentBound d := by
  have hi := integrable_finsetSum Finset.univ (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) ↦
    integrable_finsetSum Finset.univ (fun j _ ↦ PeriodicRieszKernel.integrable_secondMoment i j N))
  calc
    _ ≤ ∫ x : Td, ∑ i : Fin d, ∑ j : Fin d, ‖x‖ ^ 2 * ‖PeriodicRieszKernel.kernel i j N x‖ :=
      integral_mono (integrable_rawSecondMoment N) hi (fun x ↦ by
        simpa only [Finset.mul_sum] using mul_le_mul_of_nonneg_left (norm_rawKernel_le N x) (sq_nonneg ‖x‖))
    _ = ∑ i : Fin d, ∑ j : Fin d, ∫ x : Td, ‖x‖ ^ 2 * ‖PeriodicRieszKernel.kernel i j N x‖ := by
      rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦
        PeriodicRieszKernel.integrable_secondMoment i j N))]
      congr 1
      funext i
      exact integral_finsetSum _ (fun j _ ↦ PeriodicRieszKernel.integrable_secondMoment i j N)
    _ ≤ ∑ i : Fin d, ∑ j : Fin d, (16 / 3 : ℝ) * AnnularRieszKernel.secondMoment i j :=
      Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum (fun j _ ↦ PeriodicRieszKernel.secondMoment_le i j N))
    _ = _ := by simp only [secondMomentBound, Finset.mul_sum]

theorem measurable_kernel (N : ℕ) : Measurable (kernel (d := d) N) := by
  unfold kernel
  exact ((measurable_rawKernel N).add ((measurable_rawKernel N).comp measurable_neg)).const_smul (1 / 2 : ℝ)

theorem integrable_kernel (N : ℕ) : Integrable (kernel (d := d) N) := by
  unfold kernel
  exact ((integrable_rawKernel N).add (integrable_rawKernel N).comp_neg).smul (1 / 2 : ℝ)

theorem norm_kernel_le (N : ℕ) (x : Td) :
    ‖kernel N x‖ ≤ (1 / 2 : ℝ) * (‖rawKernel N x‖ + ‖rawKernel N (-x)‖) := by
  rw [kernel, norm_smul]
  norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)

theorem integrable_secondMoment (N : ℕ) :
    Integrable (fun x : Td ↦ ‖x‖ ^ 2 * ‖kernel N x‖) := by
  have hn : Integrable (fun x : Td ↦ ‖x‖ ^ 2 * ‖rawKernel N (-x)‖) := by
    simpa only [norm_neg] using (integrable_rawSecondMoment (d := d) N).comp_neg
  have hi := ((integrable_rawSecondMoment N).add hn).const_mul (1 / 2 : ℝ)
  apply hi.mono' (((continuous_norm.pow 2).measurable.mul (measurable_kernel N).norm).aestronglyMeasurable)
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (by positivity)]
  have hb := mul_le_mul_of_nonneg_left (norm_kernel_le N x) (sq_nonneg ‖x‖)
  simpa only [Pi.add_apply, mul_add, mul_left_comm] using hb

theorem secondMoment_le (N : ℕ) :
    (∫ x : Td, ‖x‖ ^ 2 * ‖kernel N x‖) ≤ secondMomentBound d := by
  have hn : Integrable (fun x : Td ↦ ‖x‖ ^ 2 * ‖rawKernel N (-x)‖) := by
    simpa only [norm_neg] using (integrable_rawSecondMoment (d := d) N).comp_neg
  have he : (∫ x : Td, ‖x‖ ^ 2 * ‖rawKernel N (-x)‖) = ∫ x : Td, ‖x‖ ^ 2 * ‖rawKernel N x‖ := by
    simpa only [norm_neg] using integral_neg_eq_self (fun x : Td ↦ ‖x‖ ^ 2 * ‖rawKernel N x‖) volume
  have hb := integral_mono (integrable_secondMoment N)
    (((integrable_rawSecondMoment N).add hn).const_mul (1 / 2 : ℝ)) (fun x ↦ by
      have h := mul_le_mul_of_nonneg_left (norm_kernel_le N x) (sq_nonneg ‖x‖)
      simpa only [Pi.add_apply, mul_add, mul_left_comm] using h)
  simp only [Pi.add_apply] at hb
  rw [integral_const_mul, integral_add (integrable_rawSecondMoment N) hn, he] at hb
  linarith only [hb, rawSecondMoment_le (d := d) N]

end Mettapedia.Analysis.PeriodicRieszOperator
