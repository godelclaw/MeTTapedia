import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicGradientFluxPair

/-!
# Angular depletion with its necessary output-frequency weight

For transverse input coefficients the projected rank-one pair factors
through their cross product. Its squared norm is bounded after multiplying
by the squared output frequency. An explicit nearly cancelling pair
refutes the corresponding bound with that frequency ratio removed.
The counterexample is to a coefficient estimate, not to NS regularity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PeriodicGradientFluxAngle

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeFrequencyProjectorCommutator PancakeFourierPressureStrain PancakeSameSectorDissipation
open PeriodicGradientFluxSymbol PeriodicGradientFluxPair
open PancakePeriodicVorticityEquation

theorem transverse_pair_eq_cross (l : Wavevector) (a b : VelocityCoefficient)
    (hb : modeDot l b = 0) :
    modeDot l a • b = -coefficientCross (wavevectorCoefficient l) (coefficientCross a b) := by
  have h := cross_cross_eq_smul_sub_smul' (wavevectorCoefficient l) a b
  rw [dotProduct_comm a (wavevectorCoefficient l)] at h
  change coefficientCross (wavevectorCoefficient l) (coefficientCross a b) =
    modeDot l b • a - modeDot l a • b at h
  rw [hb, zero_smul, zero_sub] at h
  rw [h, neg_neg]

theorem projected_rankOne_eq_cross (k l : Wavevector) (a b : VelocityCoefficient)
    (ha : modeDot k a = 0) (hb : modeDot l b = 0) (j : Fin 3) :
    projectedCoeff (k + l) (fun i ↦ a i • b) j =
      -(((k + l) j : ℂ) / modeSquare (k + l)) •
        coefficientCross (wavevectorCoefficient l) (coefficientCross a b) := by
  rw [projectedCoeff, contraction_rankOne, modeDot_add_wavevector, ha, zero_add,
    transverse_pair_eq_cross l a b hb, smul_neg, neg_smul]

/-- The ratio of input to output frequency is retained explicitly. -/
theorem output_weighted_pair_energy_le (k l : Wavevector) (a b : VelocityCoefficient)
    (ha : modeDot k a = 0) (hb : modeDot l b = 0) :
    ‖frequencyVec (k + l)‖ ^ 2 *
      (∑ j, ‖coefficientVec (projectedCoeff (k + l) (fun i ↦ a i • b) j)‖ ^ 2) ≤
      ‖frequencyVec l‖ ^ 2 * ‖coefficientVec (coefficientCross a b)‖ ^ 2 := by
  rw [sum_norm_projectedCoeff_sq, contraction_rankOne, modeDot_add_wavevector, ha, zero_add,
    transverse_pair_eq_cross l a b hb]
  have hn : ‖coefficientVec (-coefficientCross (wavevectorCoefficient l) (coefficientCross a b))‖ =
      ‖coefficientVec (coefficientCross (wavevectorCoefficient l) (coefficientCross a b))‖ := by
    change ‖-coefficientVec (coefficientCross (wavevectorCoefficient l) (coefficientCross a b))‖ = _
    exact norm_neg _
  rw [hn]
  have hc := pow_le_pow_left₀ (norm_nonneg _) (norm_cross_le l (coefficientCross a b)) 2
  rw [mul_pow] at hc
  by_cases hz : ‖frequencyVec (k + l)‖ = 0
  · simp only [hz, zero_pow (by omega : 2 ≠ 0), zero_mul]
    positivity
  · rw [mul_div_cancel₀ _ (pow_ne_zero 2 hz)]
    exact hc

theorem output_weighted_viscous_pair_energy_le (k l : Wavevector) (a b : VelocityCoefficient)
    (ha : modeDot k a = 0) (hb : modeDot l b = 0) :
    ‖frequencyVec (k + l)‖ ^ 2 *
      (∑ j, ‖coefficientVec (projectedCoeff (k + l) (viscousPairCoeff k l a b) j)‖ ^ 2) ≤
      ‖unitTorusDerivativePhase ^ 2 * frequencyPairing k l‖ ^ 2 *
        ‖frequencyVec l‖ ^ 2 * ‖coefficientVec (coefficientCross a b)‖ ^ 2 := by
  let c := unitTorusDerivativePhase ^ 2 * frequencyPairing k l
  have he : viscousPairCoeff k l a b = fun i ↦ c • (a i • b) :=
    funext (viscousPairCoeff_eq k l a b)
  have hn (j : Fin 3) :
      ‖coefficientVec (projectedCoeff (k + l) (viscousPairCoeff k l a b) j)‖ ^ 2 =
        ‖c‖ ^ 2 * ‖coefficientVec (projectedCoeff (k + l) (fun i ↦ a i • b) j)‖ ^ 2 := by
    rw [he, projectedCoeff_smul]
    change ‖c • coefficientVec (projectedCoeff (k + l) (fun i ↦ a i • b) j)‖ ^ 2 = _
    rw [norm_smul, mul_pow]
  simp_rw [hn]
  rw [← Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left (output_weighted_pair_energy_le k l a b ha hb) (sq_nonneg ‖c‖)
  change _ ≤ ‖c‖ ^ 2 * _ * _
  nlinarith

def firstFrequency (N : ℕ) : Wavevector := ![N, 0, 0]
def secondFrequency (N : ℕ) : Wavevector := ![-(N : ℤ), 1, 0]
def firstCoefficient (N : ℕ) : VelocityCoefficient := ![0, N, 0]
def secondCoefficient (N : ℕ) : VelocityCoefficient := ![1, N, 0]

theorem family_transverse (N : ℕ) :
    modeDot (firstFrequency N) (firstCoefficient N) = 0 ∧
      modeDot (secondFrequency N) (secondCoefficient N) = 0 := by
  simp [firstFrequency, secondFrequency, firstCoefficient, secondCoefficient, modeDot, Fin.sum_univ_three]

theorem family_output (N : ℕ) : firstFrequency N + secondFrequency N = ![0, 1, 0] := by
  ext j
  fin_cases j <;> simp [firstFrequency, secondFrequency]

theorem family_cross_energy (N : ℕ) :
    ‖coefficientVec (coefficientCross (firstCoefficient N) (secondCoefficient N))‖ ^ 2 = (N : ℝ) ^ 2 := by
  simp [coefficientVec, coefficientCross, firstCoefficient, secondCoefficient,
    PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]

theorem family_projected_energy (N : ℕ) :
    (∑ j, ‖coefficientVec (projectedCoeff (firstFrequency N + secondFrequency N)
      (fun i ↦ firstCoefficient N i • secondCoefficient N) j)‖ ^ 2) = (N : ℝ) ^ 2 + (N : ℝ) ^ 4 := by
  rw [family_output, sum_norm_projectedCoeff_sq, contraction_rankOne]
  simp [modeDot, frequencyVec, wavevectorCoefficient, coefficientVec, firstCoefficient, secondCoefficient,
    PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  ring

theorem family_saturates_weighted_bound (N : ℕ) :
    ‖frequencyVec (firstFrequency N + secondFrequency N)‖ ^ 2 *
      (∑ j, ‖coefficientVec (projectedCoeff (firstFrequency N + secondFrequency N)
        (fun i ↦ firstCoefficient N i • secondCoefficient N) j)‖ ^ 2) =
      ‖frequencyVec (secondFrequency N)‖ ^ 2 *
        ‖coefficientVec (coefficientCross (firstCoefficient N) (secondCoefficient N))‖ ^ 2 := by
  rw [family_projected_energy, family_cross_energy, family_output]
  simp [frequencyVec, wavevectorCoefficient, coefficientVec, secondFrequency,
    PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  ring

theorem not_exists_uniform_cross_energy_bound :
    ¬ ∃ C : ℝ, ∀ (k l : Wavevector) (a b : VelocityCoefficient),
      modeDot k a = 0 → modeDot l b = 0 →
      (∑ j, ‖coefficientVec (projectedCoeff (k + l) (fun i ↦ a i • b) j)‖ ^ 2) ≤
        C * ‖coefficientVec (coefficientCross a b)‖ ^ 2 := by
  rintro ⟨C, hC⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (max C 1)
  have hNC : C < (N : ℝ) := (le_max_left _ _).trans_lt hN
  have hN1 : (1 : ℝ) < N := (le_max_right _ _).trans_lt hN
  have h := hC (firstFrequency N) (secondFrequency N) (firstCoefficient N) (secondCoefficient N)
    (family_transverse N).1 (family_transverse N).2
  rw [family_projected_energy, family_cross_energy] at h
  have hp : 0 < (N : ℝ) ^ 2 := sq_pos_of_pos (by linarith)
  have hlarge : C < (N : ℝ) ^ 2 + 1 := by nlinarith
  nlinarith [mul_pos hp (sub_pos.mpr hlarge)]

end Mettapedia.FluidDynamics.NavierStokes.PeriodicGradientFluxAngle
