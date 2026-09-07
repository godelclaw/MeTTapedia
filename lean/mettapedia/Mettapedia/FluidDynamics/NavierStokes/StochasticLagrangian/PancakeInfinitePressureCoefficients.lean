import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalProjectedEquation

/-!
# Scalar pressure of the infinite velocity

The zero-mean pressure is constructed from the same infinite convection.
Its first derivatives have a summable all-output envelope. No pressure
field or pressure estimate is supplied as an independent assumption.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeInfinitePressureCoefficients

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCoefficientLimitEquation PancakeInfiniteVelocityEnvelope PancakeLowPressureBudget
open PancakeIndexedFourierMoments PancakeCurlOutputTail PancakeIncomingLowSourceEnergy
open PancakePeriodicVorticityEquation PancakeGalerkinKineticEnergy PancakeBlockReality
open PancakeSobolevFiberEnvelope PancakeInfiniteFourierDerivative

def infinitePressureCoeff (u : FourierVelocity) (q : Wavevector) : ℂ :=
  -modeDot q (infiniteConvection u q) / modeSquare q

def infinitePressureGradientCoeff (u : FourierVelocity) (q : Wavevector) : VelocityCoefficient :=
  fun j ↦ unitTorusDerivativePhase * (q j : ℂ) * infinitePressureCoeff u q

theorem infinitePressureCoeff_zero (u : FourierVelocity) : infinitePressureCoeff u 0 = 0 := by
  simp [infinitePressureCoeff, modeDot]

theorem infinitePressureCoeff_poisson (u : FourierVelocity) (q : Wavevector) :
    modeSquare q * infinitePressureCoeff u q = -modeDot q (infiniteConvection u q) := by
  by_cases hq : q = 0
  · subst q
    simp [modeDot, modeSquare]
  · have hs := modeSquare_ne_zero_of_frequencyVec_ne_zero (frequencyVec_ne_zero hq)
    unfold infinitePressureCoeff
    field_simp

theorem one_le_norm_frequencyVec {q : Wavevector} (hq : q ≠ 0) :
    1 ≤ ‖frequencyVec q‖ := by
  have hj : ∃ j, q j ≠ 0 := by
    by_contra! h
    exact hq (funext h)
  obtain ⟨j, hj⟩ := hj
  have hi : (1 : ℤ) ≤ |q j| := by
    have := abs_pos.mpr hj
    omega
  apply le_trans (b := ‖(q j : ℂ)‖) _ (norm_frequency_coordinate_le q j)
  rw [Complex.norm_intCast]
  exact_mod_cast hi

theorem norm_frequency_mul_pressure_le (u : FourierVelocity) (q : Wavevector) :
    ‖frequencyVec q‖ * ‖infinitePressureCoeff u q‖ ≤
      ‖coefficientVec (infiniteConvection u q)‖ := by
  by_cases hq : q = 0
  · subst q
    simp [infinitePressureCoeff_zero]
  · have hp := congrArg norm (infinitePressureCoeff_poisson u q)
    rw [norm_mul, norm_neg, norm_modeSquare] at hp
    have h := norm_modeDot_le q (infiniteConvection u q)
    have hr := norm_pos_iff.mpr (frequencyVec_ne_zero hq)
    nlinarith

theorem norm_infinitePressureCoeff_le (u : FourierVelocity) (q : Wavevector) :
    ‖infinitePressureCoeff u q‖ ≤ ‖coefficientVec (infiniteConvection u q)‖ := by
  by_cases hq : q = 0
  · subst q
    simp [infinitePressureCoeff_zero]
  · exact (le_mul_of_one_le_left (norm_nonneg _) (one_le_norm_frequencyVec hq)).trans
      (norm_frequency_mul_pressure_le u q)

theorem norm_infinitePressureDerivative_le (u : FourierVelocity) (j : Fin 3) (q : Wavevector) :
    ‖indexedDerivativeCoeff id j (infinitePressureCoeff u) q‖ ≤
      (2 * Real.pi) * ‖coefficientVec (infiniteConvection u q)‖ := by
  simp only [indexedDerivativeCoeff, norm_smul, norm_mul, id_eq, norm_derivativePhase]
  calc
    _ ≤ (2 * Real.pi) * ‖frequencyVec q‖ * ‖infinitePressureCoeff u q‖ := by
      gcongr
      exact norm_frequency_coordinate_le q j
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (norm_frequency_mul_pressure_le u q) (by positivity)

theorem summable_norm_infiniteConvection (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) :
    Summable (fun q ↦ ‖coefficientVec (infiniteConvection u q)‖) :=
  ((summable_convolutionEnvelope (fourierMoment 2 u) (fourierMoment_nonneg _ _) hu).mul_left 3).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (norm_infiniteConvection_le u _ (fourierMoment_nonneg _ _) hu (fun _ ↦ le_rfl))

theorem summable_norm_infinitePressure (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) : Summable (fun q ↦ ‖infinitePressureCoeff u q‖) :=
  (summable_norm_infiniteConvection u hu).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (norm_infinitePressureCoeff_le u)

theorem summable_norm_infinitePressureDerivative (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (j : Fin 3) :
    Summable (fun q ↦ ‖indexedDerivativeCoeff id j (infinitePressureCoeff u) q‖) :=
  ((summable_norm_infiniteConvection u hu).mul_left (2 * Real.pi)).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) (norm_infinitePressureDerivative_le u j)

theorem summable_norm_infinitePressureGradient (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) :
    Summable (fun q ↦ ‖infinitePressureGradientCoeff u q‖) := by
  apply ((summable_norm_infiniteConvection u hu).mul_left (2 * Real.pi)).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _)
  intro q
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  exact norm_infinitePressureDerivative_le u j q

theorem infiniteVelocityRHS_pressure_decomposition (nu : ℝ) (u : FourierVelocity)
    (q : Wavevector) :
    infiniteVelocityRHS nu u q =
      (-unitTorusDerivativePhase) • infiniteConvection u q -
        infinitePressureGradientCoeff u q + unitTorusViscousVorticityCoeff nu u q := by
  rw [infiniteVelocityRHS, lerayMode_smul]
  by_cases hq : modeSquare q = 0
  · ext i
    simp [lerayMode, hq, infinitePressureGradientCoeff, infinitePressureCoeff]
  · ext i
    simp [lerayMode, hq, infinitePressureGradientCoeff, infinitePressureCoeff]
    ring

theorem infiniteConvection_neg_conjugate (u : FourierVelocity)
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (q : Wavevector) :
    infiniteConvection u (-q) = -coefficientConjugate (infiniteConvection u q) := by
  ext i
  simp only [infiniteConvection, Pi.neg_apply, coefficientConjugate_apply,
    Complex.conj_tsum, ← tsum_neg]
  rw [← (Equiv.neg Wavevector).tsum_eq (fun k ↦ outputFiber (-q) u k i)]
  apply tsum_congr
  intro k
  change outputFiber (-q) u (-k) i = -conj (outputFiber q u k i)
  have he : -q - -k = -(q-k) := by abel
  simp only [outputFiber, he, hr, modeDot_neg_conjugate, coefficientConjugate_apply,
    neg_mul, map_mul]

theorem infinitePressureCoeff_conjugate (u : FourierVelocity)
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (q : Wavevector) :
    infinitePressureCoeff u (-q) = conj (infinitePressureCoeff u q) := by
  have hm (v : VelocityCoefficient) :
      modeDot (-q) (-coefficientConjugate v) = conj (modeDot q v) := by
    simp [modeDot, coefficientConjugate, map_sum, map_mul]
  have hs : conj (modeSquare q) = modeSquare q := by simp [modeSquare]
  simp only [infinitePressureCoeff, infiniteConvection_neg_conjugate u hr,
    modeSquare_neg, hm, map_div₀, map_neg, hs]

end Mettapedia.FluidDynamics.NavierStokes.PancakeInfinitePressureCoefficients
