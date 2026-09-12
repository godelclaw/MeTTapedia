import Mettapedia.Analysis.AnnularRieszKernel
import Mettapedia.Analysis.UnitTorusPeriodization

/-!
# Periodic second-order Riesz kernels with uniform second moments

Periodizing the actual annular inverse Fourier kernels gives a regularized
periodic multiplier. The second moment stays bounded independently of the
number of annuli; its Fourier coefficients tend to the second-order Riesz
symbol on every lattice mode. No unweighted uniform kernel mass is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.PeriodicRieszKernel

open MeasureTheory UnitTorusLattice UnitTorusPeriodization
open scoped SchwartzMap FourierTransform Topology

variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)
local notation "Td" => UnitAddTorus (Fin d)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def kernel (i j : Fin d) (N : ℕ) (x : Td) : ℂ :=
  periodize (AnnularRieszKernel.partialKernel i j N) x

theorem measurable_kernel (i j : Fin d) (N : ℕ) : Measurable (kernel i j N) :=
  measurable_periodize _ (AnnularRieszKernel.partialKernel i j N).continuous.measurable

theorem integrable_kernel (i j : Fin d) (N : ℕ) : Integrable (kernel i j N) :=
  integrable_periodize _

theorem integrable_secondMoment (i j : Fin d) (N : ℕ) :
    Integrable (fun x : Td ↦ ‖x‖ ^ 2 * ‖kernel i j N x‖) :=
  integrable_moment_periodize _ 2

theorem secondMoment_le (i j : Fin d) (N : ℕ) :
    (∫ x : Td, ‖x‖ ^ 2 * ‖kernel i j N x‖) ≤
      (16 / 3) * AnnularRieszKernel.secondMoment i j :=
  (integral_moment_periodize_le _ 2).trans
    (AnnularRieszKernel.secondMoment_partialKernel_le i j N)

theorem mFourierCoeff_kernel (i j : Fin d) (N : ℕ) (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (kernel i j N) k =
      ∑ n ∈ Finset.range N, (𝓕 (AnnularRieszKernel.dyadicKernel i j n)) (frequency k) := by
  change UnitAddTorus.mFourierCoeff (periodize (AnnularRieszKernel.partialKernel i j N)) k = _
  rw [mFourierCoeff_periodize _ (AnnularRieszKernel.partialKernel i j N).continuous.measurable
    (AnnularRieszKernel.partialKernel i j N).integrable, ← SchwartzMap.fourier_coe]
  simp only [AnnularRieszKernel.partialKernel, FourierTransform.fourier_sum, sum_apply]

theorem one_le_norm_frequency (k : Fin d → ℤ) (hk : k ≠ 0) : 1 ≤ ‖frequency k‖ := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h
    push Not at h
    exact hk (funext h)
  have ha : (1 : ℝ) ≤ |(k i : ℝ)| := by
    have hp : (0 : ℤ) < |k i| := abs_pos.mpr hi
    have h : (1 : ℤ) ≤ |k i| := by omega
    exact_mod_cast h
  exact ha.trans (by simpa [frequency, Real.norm_eq_abs] using PiLp.norm_apply_le (frequency k) i)

theorem mFourierCoeff_kernel_eq_weight (i j : Fin d) (N : ℕ) (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (kernel i j N) k =
      ((AnnularRieszKernel.weight N (frequency k) * AnnularRieszKernel.rieszEntry i j (frequency k) : ℝ) : ℂ) := by
  change UnitAddTorus.mFourierCoeff (periodize (AnnularRieszKernel.partialKernel i j N)) k = _
  rw [mFourierCoeff_periodize _ (AnnularRieszKernel.partialKernel i j N).continuous.measurable
    (AnnularRieszKernel.partialKernel i j N).integrable, ← SchwartzMap.fourier_coe,
    AnnularRieszKernel.fourier_partialKernel]

theorem mFourierCoeff_kernel_neg (i j : Fin d) (N : ℕ) (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (kernel i j N) (-k) = UnitAddTorus.mFourierCoeff (kernel i j N) k := by
  have hf : frequency (-k) = -frequency k := by ext i; simp [frequency]
  simp only [mFourierCoeff_kernel_eq_weight, hf, AnnularRieszKernel.weight_neg, AnnularRieszKernel.rieszEntry_neg]

theorem tendsto_mFourierCoeff_kernel (i j : Fin d) (k : Fin d → ℤ) :
    Filter.Tendsto (fun N : ℕ ↦ UnitAddTorus.mFourierCoeff (kernel i j N) k)
      Filter.atTop (𝓝 (AnnularRieszKernel.rieszEntry i j (frequency k) : ℂ)) := by
  by_cases hk : k = 0
  · subst k
    have hz (n : ℕ) : (𝓕 (AnnularRieszKernel.dyadicKernel i j n)) (frequency 0) = 0 := by
      simp [AnnularRieszKernel.fourier_dyadicKernel, frequency, AnnularRieszKernel.rieszEntry]
    simp only [mFourierCoeff_kernel, hz, Finset.sum_const_zero]
    simpa only [AnnularRieszKernel.rieszEntry, frequency, Pi.zero_apply, Int.cast_zero,
      mul_zero, zero_div, Complex.ofReal_zero] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (0 : ℂ)) Filter.atTop (𝓝 0))
  · simpa only [mFourierCoeff_kernel] using
      (AnnularRieszKernel.hasSum_fourier_dyadicKernel i j (frequency k)
        (one_le_norm_frequency k hk)).tendsto_sum_nat

@[simp] theorem kernel_zero (i j : Fin d) (x : Td) : kernel i j 0 x = 0 := by
  simp [kernel, AnnularRieszKernel.partialKernel, periodize,
    FundamentalDomainPeriodization.addPeriodization]

end Mettapedia.Analysis.PeriodicRieszKernel
