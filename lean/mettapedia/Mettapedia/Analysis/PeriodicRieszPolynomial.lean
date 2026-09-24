import Mettapedia.Analysis.AnnularRieszFourierSupport
import Mettapedia.Analysis.PeriodicRieszOperatorFourier
import Mettapedia.Analysis.UnitTorusFourierL1Uniqueness
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Finite Fourier representatives of the periodic annular Riesz kernels

The representative is identified almost everywhere with the constructed
periodization. Hence its spatial second moment has the same bound, independent
of the frequency cutoff. No bound for derivatives uniform in that cutoff is
asserted here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.PeriodicRieszPolynomial

open MeasureTheory UnitAddTorus UnitTorusLattice
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

def entry (i j : Fin d) (N : ℕ) (x : Td) : ℝ :=
  ∑ k ∈ AnnularRieszKernel.frequencySupport N,
    (mFourier k x).re * (AnnularRieszKernel.weight N (frequency k) *
      AnnularRieszKernel.rieszEntry i j (frequency k))

@[fun_prop] theorem continuous_entry (i j : Fin d) (N : ℕ) : Continuous (entry i j N) := by
  unfold entry
  fun_prop

@[simp] theorem entry_zero (i j : Fin d) (x : Td) : entry i j 0 x = 0 := by
  simp [entry, AnnularRieszKernel.weight]

theorem entry_ae_eq (i j : Fin d) (N : ℕ) :
    entry i j N =ᵐ[volume] PeriodicRieszOperator.entryKernel i j N := by
  have h := UnitTorusFourierL1Uniqueness.ae_eq_polynomial
    (PeriodicRieszOperator.integrable_entryKernel i j N).ofReal
    (AnnularRieszKernel.frequencySupport N) (fun k hk ↦ by
      have hc := PeriodicRieszOperator.mFourierCoeff_entryKernel i j N k
      rw [AnnularRieszKernel.weight_frequency_eq_zero_of_not_mem N k hk, zero_mul,
        Complex.ofReal_zero] at hc
      exact hc)
  filter_upwards [h] with x hx
  have hr := congrArg Complex.re hx
  simpa [UnitTorusFourierUniqueness.polynomial_apply,
    PeriodicRieszOperator.mFourierCoeff_entryKernel, entry, smul_eq_mul,
    Complex.mul_re] using hr.symm

def kernel (N : ℕ) (x : Td) : Rd →L[ℝ] Rd :=
  ∑ i : Fin d, ∑ j : Fin d, entry i j N x • PeriodicRieszOperator.basisOperator i j

@[fun_prop] theorem continuous_kernel (N : ℕ) : Continuous (kernel (d := d) N) := by
  unfold kernel
  fun_prop

@[simp] theorem kernel_zero (x : Td) : kernel 0 x = 0 := by
  unfold kernel
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  rw [entry_zero]
  exact zero_smul ℝ (PeriodicRieszOperator.basisOperator i j)

theorem kernel_ae_eq (N : ℕ) :
    kernel (d := d) N =ᵐ[volume] PeriodicRieszOperator.kernel N := by
  have h : ∀ᵐ x : Td, ∀ i j : Fin d,
      entry i j N x = PeriodicRieszOperator.entryKernel i j N x := by
    simp only [ae_all_iff]
    exact fun i j ↦ entry_ae_eq i j N
  filter_upwards [h] with x hx
  simp only [kernel, PeriodicRieszOperator.kernel_eq_sum_entryKernel, hx]

theorem kernel_sub_ae_eq (N : ℕ) (x : Td) :
    (fun y ↦ kernel N (x - y)) =ᵐ[volume]
      fun y ↦ PeriodicRieszOperator.kernel N (x - y) :=
  ((volume : Measure Td).measurePreserving_sub_left x).quasiMeasurePreserving.ae_eq_comp
    (kernel_ae_eq N)

@[simp] theorem kernel_neg (N : ℕ) (x : Td) : kernel N (-x) = kernel N x := by
  have hn := (Measure.measurePreserving_neg (volume : Measure Td)).quasiMeasurePreserving.ae_eq_comp
    (kernel_ae_eq N)
  have he : (fun x : Td ↦ kernel N (-x)) =ᵐ[volume] kernel N := by
    filter_upwards [hn, kernel_ae_eq (d := d) N] with y hy hz
    change kernel N (-y) = PeriodicRieszOperator.kernel N (-y) at hy
    rw [hy, PeriodicRieszOperator.kernel_neg, hz]
  exact congrArg (fun f : Td → Rd →L[ℝ] Rd ↦ f x)
    (Measure.eq_of_ae_eq he ((continuous_kernel N).comp continuous_neg) (continuous_kernel N))

/-- Integral replacement is valid even for nonlinear tests of the kernel.
This is not a claim that arbitrary paths preserve almost-everywhere equality. -/
theorem integral_pair_eq (N : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Td → Td → (Rd →L[ℝ] Rd) → E) :
    (∫ x : Td, ∫ y : Td, F x y (kernel N (x - y))) =
      ∫ x : Td, ∫ y : Td, F x y (PeriodicRieszOperator.kernel N (x - y)) := by
  apply integral_congr_ae
  filter_upwards with x
  apply integral_congr_ae
  filter_upwards [kernel_sub_ae_eq N x] with y hy
  rw [hy]

theorem integrable_kernel (N : ℕ) : Integrable (kernel (d := d) N) :=
  (PeriodicRieszOperator.integrable_kernel N).congr (kernel_ae_eq N).symm

theorem integrable_secondMoment (N : ℕ) :
    Integrable (fun x : Td ↦ ‖x‖ ^ 2 * ‖kernel N x‖) := by
  apply (PeriodicRieszOperator.integrable_secondMoment N).congr
  filter_upwards [kernel_ae_eq (d := d) N] with x hx
  rw [hx]

theorem secondMoment_le (N : ℕ) :
    (∫ x : Td, ‖x‖ ^ 2 * ‖kernel N x‖) ≤ PeriodicRieszOperator.secondMomentBound d := by
  have he : (∫ x : Td, ‖x‖ ^ 2 * ‖kernel N x‖) =
      ∫ x : Td, ‖x‖ ^ 2 * ‖PeriodicRieszOperator.kernel N x‖ := by
    apply integral_congr_ae
    filter_upwards [kernel_ae_eq (d := d) N] with x hx
    rw [hx]
  rw [he]
  exact PeriodicRieszOperator.secondMoment_le N

end Mettapedia.Analysis.PeriodicRieszPolynomial
