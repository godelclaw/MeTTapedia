import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPlanarPressureBox

/-!
# Unbounded initial axial production at unit kinetic energy

Normalize the explicit planar box family to kinetic energy one. The axial
component of the actual infinite unforced right-hand side at the datum,
measured in the inverse-frequency weighted square sum over the output box,
is unbounded as the frequency increases.
This rules out a scale-independent instantaneous bound by kinetic energy
alone. It makes no assertion about the production integrated in time.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierPlanarPressureGrowth

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad PancakeViscousMisalignmentAbsorption FourierPlanarPressureSign
  FourierPlanarPressureBox FourierAxialLeraySource FourierSingleConeStretch
  PancakeCoefficientLimitEquation PancakeFrequencyProjectorCommutator

theorem fullEnergy_mul_denominator (P : Finset Wavevector) (L R : ℝ) :
    fullEnergy P (velocity P (L * R)) = fullEnergy P (velocity P L) / R ^ 2 := by
  rw [fullEnergy_eq, fullEnergy_eq, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  simp only [mul_pow, div_div]

theorem areaSum_mul_denominator (P : Finset Wavevector) (L R : ℝ) (q : Wavevector) :
    areaSum P (L * R) q = areaSum P L q / R ^ 2 := by
  simp only [areaSum, Finset.sum_div, mul_pow, div_div]

theorem axialPressureSource_mul_denominator (P : Finset Wavevector) (L R : ℝ)
    (q : Wavevector) :
    axialPressureSource axis P (velocity P (L * R)) q =
      axialPressureSource axis P (velocity P L) q / (R : ℂ) ^ 2 := by
  rw [axialPressureSource_eq, axialPressureSource_eq, areaSum_mul_denominator]
  push_cast
  ring

theorem norm_axialPressureSource_mul_denominator (P : Finset Wavevector) (L R : ℝ)
    (q : Wavevector) :
    ‖axialPressureSource axis P (velocity P (L * R)) q‖ =
      ‖axialPressureSource axis P (velocity P L) q‖ / R ^ 2 := by
  rw [axialPressureSource_mul_denominator]
  simp only [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem axialDerivativeEnergy_mul_denominator (m : ℕ) (hm : 0 < m) (ν L R : ℝ) :
    axialDerivativeEnergy m ν (L * R) = axialDerivativeEnergy m ν L / R ^ 4 := by
  rw [axialDerivativeEnergy_eq m hm, axialDerivativeEnergy_eq m hm, Finset.sum_div]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [norm_axialPressureSource_mul_denominator]
  simp only [div_pow, div_div]
  congr 1
  ring

def normalizedDenominator (m : ℕ) : ℝ :=
  (scale m : ℝ) * Real.sqrt (fullEnergy (support m) (velocity (support m) (scale m)))

def normalizedVelocity (m : ℕ) : FourierVelocity :=
  velocity (support m) (normalizedDenominator m)

theorem normalized_energy (m : ℕ) (hm : 0 < m) :
    fullEnergy (support m) (normalizedVelocity m) = 1 := by
  have hE : 0 < fullEnergy (support m) (velocity (support m) (scale m)) :=
    lt_of_lt_of_le zero_lt_one (fullEnergy_ge_one m hm)
  rw [normalizedVelocity, normalizedDenominator, fullEnergy_mul_denominator,
    Real.sq_sqrt hE.le, div_self hE.ne']

theorem normalized_supported (m : ℕ) (k : Wavevector) (hk : k ∉ support m) :
    normalizedVelocity m k = 0 := velocity_supported _ _ k hk

/-- The same unit normalization holds for the full infinite kinetic-energy sum. -/
theorem normalized_kineticEnergy (m : ℕ) (hm : 0 < m) :
    InfiniteConvectionEnergy.kineticEnergy (normalizedVelocity m) = 1 := by
  unfold InfiniteConvectionEnergy.kineticEnergy
  calc
    _ = ∑ k ∈ support m, ‖coefficientVec (normalizedVelocity m k)‖ ^ 2 :=
      tsum_eq_sum fun k hk ↦ by rw [normalized_supported m k hk]; simp [coefficientVec]
    _ = fullEnergy (support m) (normalizedVelocity m) :=
      Finset.sum_congr rfl fun k _ ↦ norm_coefficientVec_sq _
    _ = 1 := normalized_energy m hm

theorem normalized_transverse (m : ℕ) (k : Wavevector) :
    modeDot k (normalizedVelocity m k) = 0 := velocity_transverse _ _ k

theorem normalized_planar (m : ℕ) (k : Wavevector) :
    coefficientDot (normalizedVelocity m k) (axisCoefficient axis) = 0 :=
  velocity_planar _ _ k

theorem normalized_reality (m : ℕ) (k : Wavevector) :
    normalizedVelocity m (-k) = fun i ↦ conj (normalizedVelocity m k i) :=
  velocity_reality _ _ (support_neg m) k

/-- The squared axial source is at least `m^3 / 160000000000`, at unit kinetic energy. -/
theorem normalized_source_growth (m : ℕ) (hm : 0 < m) (ν : ℝ) :
    (m : ℝ) ^ 3 ≤ 160000000000 * axialDerivativeEnergy m ν (normalizedDenominator m) := by
  have hE : 0 < fullEnergy (support m) (velocity (support m) (scale m)) :=
    lt_of_lt_of_le zero_lt_one (fullEnergy_ge_one m hm)
  have hs : (Real.sqrt (fullEnergy (support m) (velocity (support m) (scale m)))) ^ 4 =
      (fullEnergy (support m) (velocity (support m) (scale m))) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hE.le]
  rw [normalizedDenominator, axialDerivativeEnergy_mul_denominator m hm, hs,
    ← mul_div_assoc]
  exact (le_div_iff₀ (sq_pos_of_pos hE)).mpr (energy_relative_source_growth m hm ν)

/-- No finite constant bounds the initial weighted axial production of this unit-energy family. -/
theorem normalized_source_unbounded (ν C : ℝ) :
    ∃ m : ℕ, 0 < m ∧ C < axialDerivativeEnergy m ν (normalizedDenominator m) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max (1 : ℝ) (160000000000 * C))
  have hm1 : (1 : ℝ) < m := (le_max_left _ _).trans_lt hm
  have hm0 : 0 < m := by exact_mod_cast (zero_lt_one.trans hm1)
  have hm3 : (m : ℝ) ≤ (m : ℝ) ^ 3 := le_self_pow₀ hm1.le (by decide)
  have hC : 160000000000 * C < (m : ℝ) := (le_max_right _ _).trans_lt hm
  refine ⟨m, hm0, ?_⟩
  have hg := normalized_source_growth m hm0 ν
  linarith

/-- All data in the unbounded family are real, transverse, planar, and have kinetic energy one.
The support lies in the critical belt by `FourierPlanarPressureBox.support_inBelt`. -/
theorem unit_energy_unbounded (ν C : ℝ) :
    ∃ m : ℕ, 0 < m ∧ InfiniteConvectionEnergy.kineticEnergy (normalizedVelocity m) = 1 ∧
      (∀ k, modeDot k (normalizedVelocity m k) = 0) ∧
      (∀ k, normalizedVelocity m (-k) = fun i ↦ conj (normalizedVelocity m k i)) ∧
      (∀ k, coefficientDot (normalizedVelocity m k) (axisCoefficient axis) = 0) ∧
      C < ∑ q ∈ outputBox m,
        (‖coefficientDot (infiniteVelocityRHS ν (normalizedVelocity m) q)
          (axisCoefficient axis)‖ / ‖frequencyVec q‖) ^ 2 := by
  obtain ⟨m, hm, hC⟩ := normalized_source_unbounded ν C
  exact ⟨m, hm, normalized_kineticEnergy m hm, normalized_transverse m, normalized_reality m,
    normalized_planar m, hC⟩

end Mettapedia.FluidDynamics.NavierStokes.FourierPlanarPressureGrowth
